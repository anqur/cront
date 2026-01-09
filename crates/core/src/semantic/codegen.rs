use crate::semantic::check::{FunItem, Items};
use crate::syntax::parse::{Branch, Expr, Ident, Stmt};
use crate::{BuiltinType, Span, Type};
use chumsky::prelude::SimpleSpan;
use std::fmt::{Result as FmtResult, Write};
use std::mem::replace;

pub fn generate(items: Items) -> String {
    Codegen::default().generate(items)
}

const INCLUDES: &[&str] = &["stdbool.h", "stddef.h", "stdint.h"];

#[derive(Default)]
struct Codegen {
    buf: String,
    next_id: u64,
    level: usize,
}

impl Codegen {
    fn generate(mut self, items: Items) -> String {
        self.items(items).unwrap();
        self.buf
    }

    fn items(&mut self, items: Items) -> FmtResult {
        INCLUDES
            .iter()
            .try_for_each(|p| writeln!(self.buf, "#include <{p}>"))?;

        writeln!(self.buf)?;

        for fun in items.fns.iter().filter(|f| f.is_concrete()) {
            self.fun_sig(&fun.item)?;
            writeln!(self.buf, ";")?;
        }

        writeln!(self.buf)?;

        for fun in items.fns.into_iter().filter(|f| f.is_concrete()) {
            self.fun_def(fun.item)?;
        }

        Ok(())
    }

    fn fun_sig(&mut self, fun: &FunItem) -> FmtResult {
        write!(self.buf, "static ")?;
        self.typ(&fun.ret)?;
        writeln!(self.buf)?;
        write!(self.buf, "{}(", fun.name)?;
        self.params(&fun.params)?;
        write!(self.buf, ")")
    }

    fn fun_def(&mut self, fun: FunItem) -> FmtResult {
        self.fun_sig(&fun)?;
        writeln!(self.buf)?;
        writeln!(self.buf, "{{")?;
        self.with_block(|s| fun.body.into_iter().try_for_each(|stmt| s.stmt(stmt)))?;
        writeln!(self.buf, "}}")
    }

    fn params(&mut self, params: &[(Ident, Type)]) -> FmtResult {
        let mut it = params.iter();
        if let Some(param) = it.next() {
            self.param(param)?
        }
        for param in it {
            write!(self.buf, ", ")?;
            self.param(param)?
        }
        Ok(())
    }

    fn param(&mut self, (ident, typ): &(Ident, Type)) -> FmtResult {
        self.typ(typ)?;
        write!(self.buf, " ")?;
        self.ident(ident)
    }

    fn typ(&mut self, typ: &Type) -> FmtResult {
        match typ {
            Type::Builtin(b) => self.builtin_type(b),
            Type::Fun(..) => todo!(),
            Type::Ref(t) => {
                write!(self.buf, "*")?;
                self.typ(t)
            }
            Type::Array { .. } => todo!(),
            Type::Generic { .. } => unreachable!(),
            Type::Ident(..) => unreachable!(),
        }
    }

    fn builtin_type(&mut self, t: &BuiltinType) -> FmtResult {
        self.buf.write_str(match t {
            BuiltinType::Void => "void",
            BuiltinType::Bool => "bool",
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
            BuiltinType::Type => unreachable!(),
        })
    }

    fn stmt(&mut self, mut stmt: Span<Stmt>) -> FmtResult {
        let span = stmt.span;
        let mut lifted = Vec::default();

        match &mut stmt.item {
            Stmt::Expr(e) => self.lift_expr(span, e, &mut lifted),
            Stmt::Assign { rhs, .. } | Stmt::Update { rhs, .. } => {
                self.lift_expr(rhs.span, &mut rhs.item, &mut lifted)
            }
            Stmt::Return(e) => {
                if let Some(e) = e {
                    self.lift_expr(e.span, &mut e.item, &mut lifted);
                }
            }
            Stmt::If { .. } | Stmt::While(Branch { .. }) | Stmt::Break | Stmt::Continue => (),
        };

        lifted.push(stmt);

        lifted.into_iter().try_for_each(|stmt| {
            self.with_indent(|s| {
                match stmt.item {
                    Stmt::Expr(e) => {
                        s.expr(&e)?;
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
                    Stmt::While(Branch { mut cond, body }) => {
                        // bool exit_1 = false;
                        // do {
                        //      lifted_cond;
                        //      if (cond) {
                        //          body
                        //      } else {
                        //          exit_1 = true;
                        //      }
                        // } while (!exit_1);

                        let mut lifted = Vec::default();
                        s.lift_expr(cond.span, &mut cond.item, &mut lifted);

                        let exit = s.fresh(span, "exit");
                        write!(s.buf, "bool ")?;
                        s.ident(&exit.item)?;
                        writeln!(s.buf, " = false;")?;

                        s.with_indent(|s|writeln!(s.buf, "do {{"))?;
                        s.with_block(|s| {
                            lifted.into_iter().try_for_each(|stmt| s.stmt(stmt))?;

                            s.with_indent(|s| {
                                write!(s.buf, "if (")?;
                                s.expr(&cond.item)?;
                                writeln!(s.buf, ") {{")
                            })?;

                            s.with_block(|s| body.into_iter().try_for_each(|stmt| s.stmt(stmt)))?;

                            s.with_indent(|s| writeln!(s.buf, "}} else {{"))?;

                            s.with_block(|s| {
                                s.with_indent(|s| {
                                    s.ident(&exit.item)?;
                                    writeln!(s.buf, " = true;")
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
                }
            })
        })
    }

    fn lift_expr(&mut self, span: SimpleSpan, expr: &mut Expr, lifted: &mut Vec<Span<Stmt>>) {
        match expr {
            Expr::BinaryOp(lhs, .., typ, rhs) => {
                let typ = typ.as_deref().cloned();
                self.lift_expr(span, &mut lhs.item, lifted);
                self.lift_expr(span, &mut rhs.item, lifted);
                let name = self.fresh(span, "lifted");
                let rhs = replace(expr, Expr::Ident(name.item));
                lifted.push(Span::new(
                    span,
                    Stmt::Assign {
                        name,
                        typ,
                        rhs: Span::new(span, rhs),
                    },
                ));
            }

            Expr::Call(f, xs) => {
                self.lift_expr(span, &mut f.item, lifted);
                xs.iter_mut()
                    .for_each(|x| self.lift_expr(span, &mut x.item, lifted));
            }
            Expr::Object(..) => todo!(),
            Expr::Access(..) => todo!(),
            Expr::Method { .. } => todo!(),

            Expr::Ident(..) => (),
            Expr::BuiltinType(..) => (),
            Expr::Apply(..) => (),
            Expr::RefType(..) => (),
            Expr::ArrayType { .. } => (),
            Expr::Integer(..) => (),
            Expr::Float(..) => {}
            Expr::String(..) => {}
            Expr::Boolean(..) => {}
        }
    }

    fn fresh(&mut self, span: SimpleSpan, name: &str) -> Span<Ident> {
        self.next_id += 1;
        let mut i = Ident::unbound(name.into());
        i.fresh(self.next_id);
        Span::new(span, i)
    }

    #[allow(dead_code)]
    fn expr(&mut self, expr: &Expr) -> FmtResult {
        match expr {
            Expr::Ident(i) => self.ident(i),
            Expr::BuiltinType(b) => self.builtin_type(b),
            Expr::Apply(..) => unreachable!(),
            Expr::RefType(..) => unreachable!(),
            Expr::ArrayType { .. } => unreachable!(),
            Expr::Integer(i) => write!(self.buf, "{i}"),
            Expr::Float(f) => write!(self.buf, "{f}"),
            Expr::String(s) => write!(self.buf, "{s}"),
            Expr::Boolean(b) => write!(self.buf, "{b}"),
            Expr::Call(..) => todo!(),
            Expr::BinaryOp(lhs, op, .., rhs) => {
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
}
