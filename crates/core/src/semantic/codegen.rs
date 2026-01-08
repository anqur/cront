use crate::semantic::check::{FunItem, Items};
use crate::syntax::parse::{Expr, Ident, Stmt};
use crate::{BuiltinType, Type};
use std::fmt::{Result as FmtResult, Write};

pub fn generate(items: &Items) -> String {
    Codegen::default().generate(items)
}

const INCLUDES: &[&str] = &["stdbool.h", "stddef.h", "stdint.h"];

#[derive(Default)]
struct Codegen {
    buf: String,
    #[allow(dead_code)]
    next_id: usize,
    level: usize,
}

impl Codegen {
    fn generate(mut self, items: &Items) -> String {
        self.items(items).unwrap();
        self.buf
    }

    fn items(&mut self, items: &Items) -> FmtResult {
        INCLUDES
            .iter()
            .try_for_each(|p| writeln!(self.buf, "#include <{p}>"))?;

        writeln!(self.buf)?;

        let fns = items.fns.iter().filter(|f| f.item.constrs.is_empty());

        for fun in fns.clone() {
            self.fun_sig(&fun.item)?;
            writeln!(self.buf, ";")?;
        }

        writeln!(self.buf)?;

        for fun in fns {
            self.fun_def(&fun.item)?;
        }

        Ok(())
    }

    fn fun_sig(&mut self, fun: &FunItem) -> FmtResult {
        self.typ(&fun.ret)?;
        writeln!(self.buf)?;
        write!(self.buf, "{}(", fun.name)?;
        self.params(&fun.params)?;
        writeln!(self.buf, ")")
    }

    fn fun_def(&mut self, fun: &FunItem) -> FmtResult {
        self.fun_sig(fun)?;
        writeln!(self.buf, "{{")?;
        self.block(|s| fun.body.iter().try_for_each(|stmt| s.stmt(&stmt.item)))?;
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
        write!(self.buf, " {ident}")
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

    fn stmt(&mut self, stmt: &Stmt) -> FmtResult {
        self.indented_line(|_| match stmt {
            Stmt::Expr(_) => todo!(),
            Stmt::Assign { .. } => todo!(),
            Stmt::Update { .. } => todo!(),
            Stmt::Return(_) => todo!(),
            Stmt::If { .. } => todo!(),
            Stmt::While(_) => todo!(),
            Stmt::Break => todo!(),
            Stmt::Continue => todo!(),
        })
    }

    #[allow(dead_code)]
    fn expr(&mut self, expr: &Expr) -> FmtResult {
        match expr {
            Expr::Ident(ident) => write!(self.buf, "{ident}"),
            Expr::BuiltinType(b) => self.builtin_type(b),
            Expr::Apply(..) => unreachable!(),
            Expr::RefType(..) => unreachable!(),
            Expr::ArrayType { .. } => unreachable!(),
            Expr::Integer(i) => write!(self.buf, "{i}"),
            Expr::Float(f) => write!(self.buf, "{f}"),
            Expr::String(s) => write!(self.buf, "{s}"),
            Expr::Boolean(b) => write!(self.buf, "{b}"),
            Expr::Call(..) => todo!(),
            Expr::BinaryOp(..) => {
                // TODO: Constant lifting.
                todo!()
            }
            Expr::Object(..) => todo!(),
            Expr::Access(..) => todo!(),
            Expr::Method { .. } => todo!(),
        }
    }

    fn block<F>(&mut self, f: F) -> FmtResult
    where
        F: FnOnce(&mut Self) -> FmtResult,
    {
        self.level += 1;
        f(self)?;
        self.level -= 1;
        Ok(())
    }

    fn indented_line<F>(&mut self, f: F) -> FmtResult
    where
        F: FnOnce(&mut Self) -> FmtResult,
    {
        for _ in 0..self.level * 4 {
            self.buf.write_char(' ')?;
        }
        f(self)
    }
}
