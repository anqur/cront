mod build;
mod semantic;
mod syntax;
#[cfg(test)]
mod tests;

pub use crate::semantic::resolve::resolve;
pub use crate::syntax::lex::lex;
pub use crate::syntax::parse::expr;
pub use crate::syntax::parse::file;
pub use crate::syntax::parse::stmt;
pub use build::build;
use chumsky::prelude::SimpleSpan;
use std::result::Result as StdResult;
use strum::{Display, EnumString};
use ustr::Ustr;

#[derive(Debug, Clone)]
pub struct Span<T> {
    span: SimpleSpan,
    item: T,
}

impl<T> Span<T> {
    pub fn new(span: SimpleSpan, item: T) -> Self {
        Span { span, item }
    }

    pub(crate) fn map<F, U>(self, f: F) -> Span<U>
    where
        F: FnOnce(T) -> U,
    {
        Span {
            span: self.span,
            item: f(self.item),
        }
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
    Type,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Integer {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    U8(u8),
    U16(u16),
    U32(u32),
    USize(usize),
    U64(u64),
}

#[derive(Debug, Clone)]
pub enum Float {
    F32(f32),
    F64(f64),
}

#[derive(Debug, Clone, Display)]
pub enum Type {
    #[strum(transparent)]
    Builtin(BuiltinType),
}

type Result<T> = StdResult<T, Error>;

#[derive(Debug)]
pub enum Error {
    Resolve(Vec<Span<ResolveErr>>),
}

#[derive(Debug)]
pub enum ResolveErr {
    UndefName(Ustr),
    DuplicateName(Ustr),
}
