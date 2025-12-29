pub(crate) mod lex;
#[allow(dead_code)]
pub(crate) mod parse;

use chumsky::error::Rich;
use chumsky::extra::{Err, ParserExtra};
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;

#[derive(Debug, Clone)]
pub struct Span<T> {
    span: SimpleSpan,
    item: T,
}

impl<T> Span<T> {
    fn map<F, U>(self, f: F) -> Span<U>
    where
        F: FnOnce(T) -> U,
    {
        Span {
            span: self.span,
            item: f(self.item),
        }
    }

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
