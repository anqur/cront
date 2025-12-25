pub(crate) mod lex;

use crate::Span;
use chumsky::error::Rich;
use chumsky::extra::Err;

type SyntaxError<'a, T> = Err<Rich<'a, T, Span>>;
type LexError<'a> = SyntaxError<'a, char>;
