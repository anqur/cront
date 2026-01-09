mod build;
mod semantic;
mod syntax;
#[cfg(test)]
mod tests;

pub use crate::semantic::check::check;
pub use crate::semantic::codegen::generate;
pub use crate::semantic::resolve::resolve;
pub use crate::syntax::parse::parse;
use crate::syntax::parse::{Expr, Ident};
pub use build::build;
use chumsky::prelude::SimpleSpan;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::result::Result as StdResult;
use strum::{Display, EnumString};
use ustr::Ustr;

macro_rules! write_separated {
    ($f:ident, $items:expr, $sep:literal) => {
        let mut it = $items.iter();
        if let Some(first) = it.next() {
            write!($f, "{first}")?;
        }
        for item in it {
            write!($f, $sep)?;
            write!($f, "{item}")?;
        }
    };
}

macro_rules! write_delimited {
    ($f:ident, $lhs:literal, $items:expr, $sep:literal, $rhs:literal) => {
        write!($f, $lhs)?;
        write_separated!($f, $items, $sep);
        write!($f, $rhs)?;
    };
}

#[derive(Debug, Clone)]
pub struct Span<T> {
    span: SimpleSpan,
    item: T,
}

impl<T> Span<T> {
    pub fn new(span: SimpleSpan, item: T) -> Self {
        Span { span, item }
    }

    fn with<U>(&self, u: U) -> Span<U> {
        Span::new(self.span, u)
    }

    fn map<F, U>(self, f: F) -> Span<U>
    where
        F: FnOnce(T) -> U,
    {
        Span::new(self.span, f(self.item))
    }
}

#[derive(Default, Debug, Copy, Clone, Eq, PartialEq, EnumString, Display)]
pub enum BuiltinType {
    #[default]
    Void,
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    USize,
    F32,
    F64,
    Str,
    Type,
}

impl BuiltinType {
    fn narrow_integer(&self, n: i64) -> Option<Integer> {
        match self {
            Self::I8 => i8::try_from(n).ok().map(Integer::I8),
            Self::I16 => i16::try_from(n).ok().map(Integer::I16),
            Self::I32 => i32::try_from(n).ok().map(Integer::I32),
            Self::I64 => Some(Integer::I64(n)),
            Self::U8 => u8::try_from(n).ok().map(Integer::U8),
            Self::U16 => u16::try_from(n).ok().map(Integer::U16),
            Self::U32 => u32::try_from(n).ok().map(Integer::U32),
            Self::USize => usize::try_from(n).ok().map(Integer::USize),
            Self::U64 => u64::try_from(n).ok().map(Integer::U64),
            _ => unreachable!(),
        }
    }

    fn is_integer(&self) -> bool {
        self.is_signed_integer() || self.is_unsigned_integer()
    }

    fn is_signed_integer(&self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }

    fn is_unsigned_integer(&self) -> bool {
        matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::U64)
    }

    fn narrow_float(&self, n: f64) -> Float {
        match self {
            Self::F32 => Float::F32(n as _),
            Self::F64 => Float::F64(n),
            _ => unreachable!(),
        }
    }

    fn is_float(&self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Display)]
pub enum Integer {
    #[strum(transparent)]
    I8(i8),
    #[strum(transparent)]
    I16(i16),
    #[strum(transparent)]
    I32(i32),
    #[strum(transparent)]
    I64(i64),
    #[strum(transparent)]
    U8(u8),
    #[strum(transparent)]
    U16(u16),
    #[strum(transparent)]
    U32(u32),
    #[strum(transparent)]
    USize(usize),
    #[strum(transparent)]
    U64(u64),
}

#[derive(Debug, Clone, Display)]
pub enum Float {
    #[strum(transparent)]
    F32(f32),
    #[strum(transparent)]
    F64(f64),
}

#[derive(Debug, Clone)]
pub enum Type {
    Builtin(BuiltinType),
    Fun(Box<FunType>),
    Ref(Box<Self>),
    Array {
        elem: Box<Self>,
        len: Option<Box<Self>>,
    },
    Generic {
        typ: Ident,
        constr: Box<Self>,
        ret: Box<Self>,
    },
    Ident(Ident),
}

impl Type {
    fn main() -> Self {
        Self::Fun(Box::new(FunType {
            params: Default::default(),
            ret: Self::Builtin(BuiltinType::Void),
        }))
    }

    fn to_expr(&self, span: SimpleSpan) -> Span<Expr> {
        Span::new(
            span,
            match self {
                Self::Builtin(t) => Expr::BuiltinType(*t),
                Self::Ref(t) => Expr::RefType(Box::new(t.to_expr(span))),
                Self::Ident(id) => Expr::Ident(*id),
                _ => unreachable!(),
            },
        )
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Builtin(t) => write!(f, "{t}"),
            Self::Fun(t) => write!(f, "{t}"),
            Self::Ref(t) => write!(f, "&{t}"),
            Self::Array { elem, len } => match len {
                None => write!(f, "[]{elem}"),
                Some(len) => write!(f, "[{len}]{elem}"),
            },
            Self::Generic { typ, constr, ret } => write!(f, "({typ}: {constr}) => {ret}"),
            Self::Ident(i) => write!(f, "{i}"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunType {
    params: Vec<Type>,
    ret: Type,
}

impl Display for FunType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write_delimited!(f, "(", self.params, ", ", ")");
        write!(f, " => {}", self.ret)
    }
}

type Result<T> = StdResult<T, Error>;

#[derive(Debug)]
pub enum Error {
    Resolve(Vec<Span<ResolveErr>>),
    Check(Vec<Span<CheckErr>>),
}

#[derive(Debug)]
pub enum ResolveErr {
    UndefName(Ustr),
    DuplicateName(Ustr),
}

#[derive(Debug)]
pub enum CheckErr {
    TypeMismatch { got: String, want: String },
    ArityMismatch { got: usize, want: usize },
}
