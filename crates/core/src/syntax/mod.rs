pub(crate) mod lex;
pub(crate) mod parse;

use crate::Span;
use chumsky::error::Rich;
use chumsky::extra::{Err, ParserExtra};
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;

impl<T> Span<T> {
    fn from_map_extra<'src, 'b, I, E>(item: T, e: &mut MapExtra<'src, 'b, I, E>) -> Self
    where
        I: Input<'src, Span = SimpleSpan>,
        E: ParserExtra<'src, I>,
    {
        Self {
            span: e.span(),
            item,
        }
    }
}

type SyntaxError<'a, T> = Err<Rich<'a, T, SimpleSpan>>;
