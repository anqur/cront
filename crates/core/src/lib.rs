mod parse;
#[cfg(test)]
mod tests;

pub use crate::parse::lex::lex;
use chumsky::extra::ParserExtra;
use chumsky::input::MapExtra;
use chumsky::prelude::{Input, SimpleSpan};
use strum::{Display, EnumString};
use ustr::Ustr;

type Span = SimpleSpan;

#[derive(Debug, Clone)]
struct Spanned<T> {
    span: Span,
    item: T,
}

impl<T> Spanned<T> {
    fn from_map_extra<'src, 'b, I, E>(item: T, e: &mut MapExtra<'src, 'b, I, E>) -> Self
    where
        I: Input<'src, Span = Span>,
        E: ParserExtra<'src, I>,
    {
        Self {
            span: e.span(),
            item,
        }
    }
}

#[derive(Debug, Clone, EnumString, Display)]
#[strum(serialize_all = "lowercase")]
enum Keyword {
    Fun,
    If,
    Return,
}

#[derive(Debug, Eq, PartialEq, Clone, Display)]
enum Symbol {
    LParen,
    RParen,
    LBrace,
    RBrace,
    Semi,
    At,
}

#[derive(Debug, Clone, Display)]
enum Token {
    #[strum(transparent)]
    Number(Ustr),
    #[strum(transparent)]
    String(String),
    #[strum(transparent)]
    Boolean(bool),
    #[strum(transparent)]
    Ident(Ustr),
    #[strum(transparent)]
    Doc(String),
    #[strum(transparent)]
    Symbol(Symbol),
    #[strum(transparent)]
    BuiltinType(BuiltinType),
    #[strum(transparent)]
    Keyword(Keyword),
}

#[derive(Default, Debug, Copy, Clone, EnumString, Display)]
enum BuiltinType {
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
