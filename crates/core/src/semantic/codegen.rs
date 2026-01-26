use crate::semantic::check::{FunItem, Items};
use crate::syntax::parse::{Builtin, Expr, Ident, Idents, Stmt};
use crate::{BuiltinType, Span, Type};
use chumsky::prelude::SimpleSpan;
use std::collections::HashMap;
use std::fmt::{Result as FmtResult, Write};
use std::mem::{replace, take};

pub fn generate(items: Items) -> String {
    Codegen::default().generate(items)
}

const INCLUDES: &[&str] = &["stddef.h", "stdint.h", "assert.h"];

#[derive(Default)]
struct Codegen {
    idents: Idents,
    main: Option<Ident>,
    buf: String,
    level: usize,
    mono: HashMap<Ident, Type>,
}

impl Codegen {
    fn generate(mut self, items: Items) -> String {
        self.idents = items.idents;
        self.main = items.main;
        self.items(items).unwrap();
        self.buf
    }

    fn items(&mut self, items: Items) -> FmtResult {
        INCLUDES
            .iter()
            .try_for_each(|p| writeln!(self.buf, "#include <{p}>"))?;

        writeln!(self.buf)?;

        for fun in items.fns.iter() {
            if fun.item.constrs.is_empty() {
                self.fun_sig(&fun.item, None, true)?;
            } else {
                for (types, name) in &fun.item.mono {
                    let env = fun.item.mono_env(types);
                    self.with_mono(env, |s| s.fun_sig(&fun.item, Some(name), true))?;
                }
            }
            writeln!(self.buf)?;
        }

        let mut it = items.fns.into_iter().peekable();
        while let Some(mut fun) = it.next() {
            let stmts = Lower::new(&mut self.idents).lower(take(&mut fun.item.body));
            if fun.item.constrs.is_empty() {
                self.fun_def(&fun.item, None, &stmts)?;
            } else {
                for (types, name) in &fun.item.mono {
                    let env = fun.item.mono_env(types);
                    self.with_mono(env, |s| s.fun_def(&fun.item, Some(*name), &stmts))?;
                }
            }
            if it.peek().is_some() {
                writeln!(self.buf)?;
            }
        }

        Ok(())
    }

    fn fun_sig(&mut self, fun: &FunItem, name: Option<&Ident>, trailing_semi: bool) -> FmtResult {
        if Some(fun.name) != self.main {
            write!(self.buf, "static ")?;
        }
        self.typ(&fun.ret)?;
        writeln!(self.buf)?;
        self.ident(name.unwrap_or(&fun.name))?;
        self.params(&fun.params)?;
        if trailing_semi {
            writeln!(self.buf, ";")?;
        }
        Ok(())
    }

    fn fun_def(&mut self, fun: &FunItem, name: Option<Ident>, body: &[Span<Stmt>]) -> FmtResult {
        self.fun_sig(fun, name.as_ref(), false)?;
        writeln!(self.buf)?;
        writeln!(self.buf, "{{")?;
        self.with_block(|s| body.iter().try_for_each(|stmt| s.stmt(stmt)))?;
        writeln!(self.buf, "}}")
    }

    fn params(&mut self, params: &[(Ident, Type)]) -> FmtResult {
        write!(self.buf, "(")?;
        if params.is_empty() {
            write!(self.buf, "void")?;
        } else {
            let mut it = params.iter();
            if let Some(param) = it.next() {
                self.param(param)?
            }
            for param in it {
                write!(self.buf, ", ")?;
                self.param(param)?
            }
        }
        write!(self.buf, ")")
    }

    fn param(&mut self, (ident, typ): &(Ident, Type)) -> FmtResult {
        self.typ(typ)?;
        write!(self.buf, " ")?;
        self.ident(ident)
    }

    fn typ(&mut self, typ: &Type) -> FmtResult {
        match typ {
            Type::Unknown => unreachable!(),
            Type::Builtin(b) => self.builtin_type(b),
            Type::Fun(..) => todo!(),
            Type::Ref(t) => {
                write!(self.buf, "*")?;
                self.typ(t)
            }
            Type::Array { .. } => todo!(),
            Type::Generic { .. } => unreachable!(),
            Type::Ident(t) => self.typ(&self.mono.get(t).unwrap().clone()),
            Type::CType { to, .. } => write!(self.buf, "{to}"),
            Type::Struct(i) => {
                write!(self.buf, "struct ")?;
                self.ident(i)
            }
        }
    }

    fn builtin_type(&mut self, t: &BuiltinType) -> FmtResult {
        self.buf.write_str(match t {
            BuiltinType::Void => "void",
            BuiltinType::Bool => "uint8_t",
            BuiltinType::I8 => "int8_t",
            BuiltinType::I16 => "int16_t",
            BuiltinType::I32 => "int32_t",
            BuiltinType::I64 => "int64_t",
            BuiltinType::U8 => "uint8_t",
            BuiltinType::U16 => "uint16_t",
            BuiltinType::U32 => "uint32_t",
            BuiltinType::U64 => "uint64_t",
            BuiltinType::USize => "size_t",
            BuiltinType::F32 => "float",
            BuiltinType::F64 => "double",
            BuiltinType::Str => todo!(),
            BuiltinType::Number | BuiltinType::Type => unreachable!(),
        })
    }

    fn stmt(&mut self, stmt: &Span<Stmt>) -> FmtResult {
        self.with_indent(|s| match &stmt.item {
            Stmt::Expr(e) => {
                s.expr(e)?;
                writeln!(s.buf, ";")
            }
            Stmt::Assign { name, typ, rhs } => {
                s.expr(&typ.as_ref().unwrap().item)?;
                write!(s.buf, " ")?;
                s.ident(&name.item)?;
                write!(s.buf, " = ")?;
                s.expr(&rhs.item)?;
                writeln!(s.buf, ";")
            }
            Stmt::Update { name, rhs } => {
                s.ident(&name.item)?;
                write!(s.buf, " = ")?;
                s.expr(&rhs.item)?;
                writeln!(s.buf, ";")
            }
            Stmt::Return(e) => {
                write!(s.buf, "return")?;
                if let Some(e) = e {
                    write!(s.buf, " ")?;
                    s.expr(&e.item)?;
                }
                writeln!(s.buf, ";")
            }
            Stmt::If { .. } => todo!(),
            Stmt::While { branch, exit } => {
                let exit = exit.as_ref().unwrap();

                writeln!(s.buf, "do {{")?;
                s.with_block(|s| {
                    s.with_indent(|s| {
                        write!(s.buf, "if (")?;
                        s.expr(&branch.cond.item)?;
                        writeln!(s.buf, ") {{")
                    })?;

                    s.with_block(|s| branch.body.iter().try_for_each(|stmt| s.stmt(stmt)))?;

                    s.with_indent(|s| writeln!(s.buf, "}} else {{"))?;

                    s.with_block(|s| {
                        s.with_indent(|s| {
                            s.ident(&exit.item)?;
                            writeln!(s.buf, " = 1;")
                        })
                    })?;

                    s.with_indent(|s| writeln!(s.buf, "}}"))
                })?;

                s.with_indent(|s| {
                    write!(s.buf, "}} while (!")?;
                    s.ident(&exit.item)?;
                    writeln!(s.buf, ");")
                })
            }
            Stmt::Break => writeln!(s.buf, "break;"),
            Stmt::Continue => writeln!(s.buf, "continue;"),
            Stmt::Decl { name, typ } => {
                s.expr(&typ.item)?;
                write!(s.buf, " ")?;
                s.ident(&name.item)?;
                writeln!(s.buf, ";")
            }
        })
    }

    fn expr(&mut self, expr: &Expr) -> FmtResult {
        match expr {
            Expr::Ident(i) => self.ident(i),
            Expr::BuiltinType(b) => self.builtin_type(b),
            Expr::Apply(f, ..) => self.expr(&f.item),
            Expr::RefType(..) => unreachable!(),
            Expr::ArrayType { .. } => unreachable!(),
            Expr::Integer(i) => write!(self.buf, "{i}"),
            Expr::Float(f) => write!(self.buf, "{f}"),
            Expr::String(s) => write!(self.buf, "{s}"),
            Expr::Boolean(b) => write!(self.buf, "{}", if *b { "1" } else { "0" }),
            Expr::Call { callee, args, .. } => {
                self.expr(&callee.item)?;
                write!(self.buf, "(")?;
                let mut it = args.iter();
                if let Some(x) = it.next() {
                    self.expr(&x.item)?;
                }
                for x in it {
                    write!(self.buf, ", ")?;
                    self.expr(&x.item)?;
                }
                write!(self.buf, ")")
            }
            Expr::BinaryOp { lhs, op, rhs, .. } => {
                self.expr(&lhs.item)?;
                write!(self.buf, " {op} ")?;
                self.expr(&rhs.item)
            }
            Expr::Object(..) => todo!(),
            Expr::Access(..) => todo!(),
            Expr::Method { .. } => todo!(),
        }
    }

    fn ident(&mut self, i: &Ident) -> FmtResult {
        if let Some(b) = Builtin::from_id(i.id) {
            return write!(self.buf, "{b}");
        }
        if Some(i) == self.main.as_ref() {
            return write!(self.buf, "main");
        }
        write!(self.buf, "{}_{}", i.text, i.id)
    }

    fn with_block<F>(&mut self, f: F) -> FmtResult
    where
        F: FnOnce(&mut Self) -> FmtResult,
    {
        self.level += 1;
        f(self)?;
        self.level -= 1;
        Ok(())
    }

    fn with_indent<F>(&mut self, f: F) -> FmtResult
    where
        F: FnOnce(&mut Self) -> FmtResult,
    {
        for _ in 0..self.level * 4 {
            self.buf.write_char(' ')?;
        }
        f(self)
    }

    fn with_mono<I, F>(&mut self, env: I, f: F) -> FmtResult
    where
        I: Iterator<Item = (Ident, Type)>,
        F: FnOnce(&mut Self) -> FmtResult,
    {
        self.mono.extend(env);
        f(self)?;
        self.mono.clear();
        Ok(())
    }
}

struct Lower<'a> {
    idents: &'a mut Idents,
    decls: Vec<Span<Stmt>>,
}

impl<'a> Lower<'a> {
    fn new(idents: &'a mut Idents) -> Self {
        Self {
            idents,
            decls: Default::default(),
        }
    }

    fn lower(mut self, stmts: Vec<Span<Stmt>>) -> Vec<Span<Stmt>> {
        let stmts = self.stmts(stmts);
        self.decls.extend(stmts);
        self.decls
    }

    fn stmts(&mut self, stmts: Vec<Span<Stmt>>) -> Vec<Span<Stmt>> {
        let mut ret = Vec::with_capacity(stmts.len());
        for stmt in stmts {
            let s = self.stmt(stmt, &mut ret);
            ret.push(s);
        }
        ret
    }

    fn stmt(&mut self, mut stmt: Span<Stmt>, lifted: &mut Vec<Span<Stmt>>) -> Span<Stmt> {
        let span = stmt.span;
        match stmt.item {
            Stmt::Expr(ref mut e) => {
                self.expr(0, span, e, lifted);
                stmt
            }
            Stmt::Decl { .. } => unreachable!(),
            Stmt::Assign { name, typ, rhs } => {
                self.decls.push(Span::new(
                    span,
                    Stmt::Decl {
                        name: name.clone(),
                        typ: typ.unwrap(),
                    },
                ));
                Span::new(span, Stmt::Update { name, rhs })
            }
            Stmt::Update { ref mut rhs, .. } => {
                self.expr(0, span, &mut rhs.item, lifted);
                stmt
            }
            Stmt::Return(ref mut e) => {
                if let Some(e) = e {
                    self.expr(0, span, &mut e.item, lifted);
                }
                stmt
            }
            Stmt::If { .. } => todo!(),
            Stmt::While { mut branch, .. } => {
                let exit = Span::new(span, self.idents.intermediate("exit"));
                self.decls.push(Span::new(
                    span,
                    Stmt::Decl {
                        name: exit.clone(),
                        typ: Span::new(span, Expr::BuiltinType(BuiltinType::Bool)),
                    },
                ));
                lifted.push(Span::new(
                    span,
                    Stmt::Update {
                        name: exit.clone(),
                        rhs: Span::new(span, Expr::Boolean(false)),
                    },
                ));
                self.expr(0, span, &mut branch.cond.item, lifted);
                branch.body = self.stmts(branch.body);
                let exit = Some(exit);
                Span::new(span, Stmt::While { branch, exit })
            }
            Stmt::Break | Stmt::Continue => stmt,
        }
    }

    fn expr(
        &mut self,
        depth: usize,
        span: SimpleSpan,
        expr: &mut Expr,
        lifted: &mut Vec<Span<Stmt>>,
    ) {
        match expr {
            Expr::BinaryOp { lhs, rhs, .. } => {
                self.expr(depth + 1, span, &mut lhs.item, lifted);
                self.expr(depth + 1, span, &mut rhs.item, lifted);
            }
            Expr::Call { callee, args, .. } => {
                self.expr(depth + 1, callee.span, &mut callee.item, lifted);
                args.iter_mut()
                    .for_each(|x| self.expr(depth + 1, span, &mut x.item, lifted));
            }

            Expr::Object(..) => todo!(),
            Expr::Access(..) => todo!(),
            Expr::Method { .. } => todo!(),

            Expr::Ident(..)
            | Expr::BuiltinType(..)
            | Expr::Apply(..)
            | Expr::RefType(..)
            | Expr::ArrayType { .. }
            | Expr::Integer(..)
            | Expr::Float(..)
            | Expr::String(..)
            | Expr::Boolean(..) => (),
        }

        if depth > 0
            && let Expr::BinaryOp { typ, .. } | Expr::Call { typ, .. } = expr
            && let Some(typ) = typ.as_deref()
            && !matches!(&typ.item, Expr::BuiltinType(BuiltinType::Void))
        {
            // Only lift non-void expressions.
            self.replace_expr(span, Some(typ.clone()), expr, lifted);
        }
    }

    fn replace_expr(
        &mut self,
        span: SimpleSpan,
        typ: Option<Span<Expr>>,
        expr: &mut Expr,
        lifted: &mut Vec<Span<Stmt>>,
    ) {
        let name = Span::new(span, self.idents.intermediate("expr"));
        self.decls.push(Span::new(
            span,
            Stmt::Decl {
                name: name.clone(),
                typ: typ.unwrap(),
            },
        ));
        lifted.push(Span::new(
            span,
            Stmt::Update {
                rhs: Span::new(span, replace(expr, Expr::Ident(name.item))),
                name,
            },
        ))
    }
}
