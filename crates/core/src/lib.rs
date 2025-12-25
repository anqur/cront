mod syntax;
#[cfg(test)]
mod tests;

pub use crate::syntax::lex::lex;
pub use crate::syntax::parse::expr;
pub use crate::syntax::parse::stmt;
use strum::{Display, EnumString};

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
