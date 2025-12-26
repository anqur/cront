use crate::BuiltinType;
use crate::syntax::{Spanned, SyntaxError};
use chumsky::Parser;
use chumsky::container::Container;
use chumsky::error::Rich;
use chumsky::prelude::{
    IterParser, SimpleSpan, any, choice, end, just, none_of, one_of, skip_then_retry_until,
};
use chumsky::text::{digits, ident, int};
use std::str::FromStr;
use strum::{Display, EnumString};
use ustr::Ustr;

#[derive(Default)]
pub struct Tokens {
    pub spans: Vec<SimpleSpan>,
    pub tokens: Vec<Token>,
}

impl Container<Spanned<Token>> for Tokens {
    fn with_capacity(n: usize) -> Self {
        Self {
            spans: Vec::with_capacity(n),
            tokens: Vec::with_capacity(n),
        }
    }

    fn push(&mut self, Spanned { span, item }: Spanned<Token>) {
        self.spans.push(span);
        self.tokens.push(item);
    }
}

#[derive(Debug, Clone, Eq, PartialEq, EnumString, Display)]
#[strum(serialize_all = "lowercase")]
pub enum Keyword {
    Fun,
    Let,
    If,
    Else,
    For,
    While,
    Break,
    Continue,
    Return,
    Struct,
    Typ,
}

#[derive(Debug, Eq, PartialEq, Clone, Display)]
pub enum Symbol {
    EqEq,
    Le,
    Ge,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Lt,
    Gt,
    Semi,
    Colon,
    Comma,
    Dot,
    Eq,
    Plus,
    Minus,
    Mul,
    Question,
}

#[derive(Debug, Clone, Eq, PartialEq, Display)]
pub enum Token {
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

type LexError<'a> = SyntaxError<'a, char>;

pub fn lex<'s>() -> impl Parser<'s, &'s str, Tokens, LexError<'s>> {
    let dec = digits(10).to_slice();
    let frac = just('.').then(dec);
    let exp = choice((just('e'), just('E')))
        .then(one_of("+-").or_not())
        .then(dec);
    let number = just('-')
        .or_not()
        .then(int(10))
        .then(frac.or_not())
        .then(exp.or_not())
        .to_slice()
        .map(|s: &str| Token::Number(s.into()));

    let escape = just('\\')
        .then(choice((
            just('\\'),
            just('/'),
            just('"'),
            just('b').to('\x08'),
            just('f').to('\x0C'),
            just('n').to('\n'),
            just('r').to('\r'),
            just('t').to('\t'),
            just('u').ignore_then(digits(16).exactly(4).to_slice().validate(
                |digits, m, emitter| {
                    char::from_u32(u32::from_str_radix(digits, 16).unwrap()).unwrap_or_else(|| {
                        emitter.emit(Rich::custom(m.span(), digits));
                        '\u{FFFD}' // unicode replacement character
                    })
                },
            )),
        )))
        .ignored();
    let string = choice((none_of("\\\"").ignored(), escape))
        .repeated()
        .to_slice()
        .map(|s: &str| Token::String(s.into()))
        .delimited_by(just('"'), just('"'));

    let ident = ident().map(|text| {
        if let Ok(b) = bool::from_str(text) {
            Token::Boolean(b)
        } else if let Ok(t) = BuiltinType::from_str(text) {
            Token::BuiltinType(t)
        } else if let Ok(w) = Keyword::from_str(text) {
            Token::Keyword(w)
        } else {
            Token::Ident(text.into())
        }
    });

    let symbol = choice((
        just("==").to(Symbol::EqEq),
        just("<=").to(Symbol::Le),
        just(">=").to(Symbol::Ge),
        just('(').to(Symbol::LParen),
        just(')').to(Symbol::RParen),
        just('{').to(Symbol::LBrace),
        just('}').to(Symbol::RBrace),
        just('[').to(Symbol::LBracket),
        just(']').to(Symbol::RBracket),
        just('<').to(Symbol::Lt),
        just('>').to(Symbol::Gt),
        just(';').to(Symbol::Semi),
        just(':').to(Symbol::Colon),
        just(',').to(Symbol::Comma),
        just('.').to(Symbol::Dot),
        just('=').to(Symbol::Eq),
        just('+').to(Symbol::Plus),
        just('-').to(Symbol::Minus),
        just('*').to(Symbol::Mul),
        just('?').to(Symbol::Question),
    ))
    .map(Token::Symbol);

    let doc = just("///")
        .ignore_then(any().and_is(just('\n').not()).repeated().to_slice())
        .map(|s: &str| Token::Doc(s.into()));

    let token = choice((number, string, ident, symbol, doc));

    let line_comment = just("//")
        .then_ignore(any().and_is(just('/')).not())
        .then_ignore(any().and_is(just('\n').not()).repeated())
        .padded();
    let block_comment = just("/*")
        .then_ignore(any().and_is(just("*/").not()).repeated())
        .then_ignore(just("*/"))
        .padded();
    let comment = choice((line_comment, block_comment));

    token
        .map_with(Spanned::from_map_extra)
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}
