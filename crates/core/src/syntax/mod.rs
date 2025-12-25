pub(crate) mod lex;
pub(crate) mod parse;

use chumsky::error::Rich;
use chumsky::extra::{Err, ParserExtra};
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;

type Span = SimpleSpan;

#[derive(Debug, Clone)]
pub struct Spanned<T> {
    span: Span,
    item: T,
}

impl<T> Spanned<T> {
    fn map<F, U>(self, f: F) -> Spanned<U>
    where
        F: FnOnce(T) -> U,
    {
        Spanned {
            span: self.span,
            item: f(self.item),
        }
    }

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

type SyntaxError<'a, T> = Err<Rich<'a, T, Span>>;
