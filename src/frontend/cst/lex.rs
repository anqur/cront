use crate::Span;
use crate::frontend::cst::Kind;
use chumsky::IterParser;
use chumsky::error::Rich;
use chumsky::prelude::{any, choice, just, none_of, one_of, via_parser};
use chumsky::text::{digits, ident, int, newline, whitespace};
use chumsky::{Parser, extra};

type LexError<'src> = extra::Err<Rich<'src, char>>;

fn token<'src>() -> impl Parser<'src, &'src str, Kind, LexError<'src>> {
    let dec = digits(10);
    let frac = just('.').then(dec);
    let exp = choice((just('e'), just('E')))
        .then(one_of("+-").or_not())
        .then(dec);
    let number = just('-')
        .or_not()
        .then(int(10))
        .then(frac.or_not())
        .then(exp.or_not())
        .to(Kind::Number);

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
        .to(Kind::String)
        .delimited_by(just('"'), just('"'));

    let word = ident().map(|text| match text {
        "true" => Kind::KwTrue,
        "false" => Kind::KwFalse,
        "fun" => Kind::KwFun,
        "let" => Kind::KwLet,
        "if" => Kind::KwIf,
        "else" => Kind::KwElse,
        "for" => Kind::KwFor,
        "while" => Kind::KwWhile,
        "break" => Kind::KwBreak,
        "continue" => Kind::KwContinue,
        "return" => Kind::KwReturn,
        "struct" => Kind::KwStruct,
        "typ" => Kind::KwTyp,
        "Void" => Kind::KwVoid,
        "Bool" => Kind::KwBool,
        "I8" => Kind::KwI8,
        "I16" => Kind::KwI16,
        "I32" => Kind::KwI32,
        "I64" => Kind::KwI64,
        "U8" => Kind::KwU8,
        "U16" => Kind::KwU16,
        "U32" => Kind::KwU32,
        "U64" => Kind::KwU64,
        "USize" => Kind::KwUSize,
        "F32" => Kind::KwF32,
        "F64" => Kind::KwF64,
        "Str" => Kind::KwStr,
        "Number" => Kind::KwNumber,
        "Type" => Kind::KwType,
        _ => Kind::Ident,
    });

    let symbol = choice((
        just("==").to(Kind::SymEqEq),
        just("<=").to(Kind::SymLe),
        just(">=").to(Kind::SymGe),
        just("::").to(Kind::SymColonColon),
        just('(').to(Kind::SymLParen),
        just(')').to(Kind::SymRParen),
        just('{').to(Kind::SymLBrace),
        just('}').to(Kind::SymRBrace),
        just('[').to(Kind::SymLBracket),
        just(']').to(Kind::SymRBracket),
        just('<').to(Kind::SymLt),
        just('>').to(Kind::SymGt),
        just(';').to(Kind::SymSemi),
        just(':').to(Kind::SymColon),
        just(',').to(Kind::SymComma),
        just('.').to(Kind::SymDot),
        just('=').to(Kind::SymEq),
        just('+').to(Kind::SymPlus),
        just('-').to(Kind::SymMinus),
        just('*').to(Kind::SymMul),
        just('&').to(Kind::SymAnd),
        just('?').to(Kind::SymQuestion),
    ));

    let doc = just("///")
        .ignore_then(any().and_is(just('\n').not()).repeated())
        .to(Kind::Doc);
    let line_comment = just("//")
        .then_ignore(any().and_is(just('/')).not())
        .then_ignore(any().and_is(just('\n').not()).repeated())
        .to(Kind::LineComment);
    let block_comment = just("/*")
        .then_ignore(any().and_is(just("*/").not()).repeated())
        .then_ignore(just("*/"))
        .to(Kind::BlockComment);

    choice((
        doc,
        line_comment,
        block_comment,
        newline().to(Kind::Newline),
        whitespace().at_least(1).to(Kind::Whitespace),
        number,
        string,
        word,
        symbol,
    ))
}

fn lex<'src>() -> impl Parser<'src, &'src str, Vec<Span<Kind>>, LexError<'src>> {
    token()
        .recover_with(via_parser(
            any()
                .and_is(token().not())
                .repeated()
                .at_least(1)
                .to(Kind::Error),
        ))
        .map_with(Span::from_map_extra)
        .repeated()
        .collect()
}

pub(super) struct State<'s> {
    pub(super) src: &'s str,
    pub(super) tokens: Vec<Span<Kind>>,
    pub(super) errs: Vec<Rich<'s, char>>,
}

impl<'s> State<'s> {
    pub(super) fn lex(src: &'s str) -> Self {
        let (tokens, errs) = lex().parse(src).into_output_errors();
        let tokens = tokens.unwrap_or_default();
        State { src, tokens, errs }
    }
}
