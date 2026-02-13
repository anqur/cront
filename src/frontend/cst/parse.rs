use crate::Span;
use crate::frontend::cst::{Builder, Kind, Tokens};
use chumsky::error::Rich;
use chumsky::input::MapExtra;
use chumsky::pratt::{infix, left, prefix};
use chumsky::prelude::{Recursive, choice, custom, just};
use chumsky::{Parser, extra};
use cstree::build::Checkpoint;

type ParseError<'t> = extra::Full<Rich<'t, Span<Kind>>, Builder<'t>, ()>;

fn as_node<'t, O>(
    kind: Kind,
    parser: impl Parser<'t, Tokens<'t>, O, ParseError<'t>>,
) -> impl Parser<'t, Tokens<'t>, (), ParseError<'t>> {
    custom(move |r| {
        let builder: &mut Builder = r.state();
        let c = builder.builder.checkpoint();
        let ret = r.parse(&parser)?;
        let builder = &mut r.state().builder;
        builder.start_node_at(c, kind);
        builder.finish_node();
        Ok(ret)
    })
    .try_map(with_effect)
}

fn checkpoint<'t>() -> impl Parser<'t, Tokens<'t>, Checkpoint, ParseError<'t>> {
    custom(|r| {
        let builder: &mut Builder = r.state();
        Ok(builder.builder.checkpoint())
    })
}

fn with_effect<V, Span, E>(_: V, _: Span) -> Result<(), E> {
    Ok(())
}

pub fn ws<'t>() -> impl Parser<'t, Tokens<'t>, (), ParseError<'t>> {
    choice((
        just(Kind::LineComment),
        just(Kind::BlockComment),
        just(Kind::Whitespace),
        just(Kind::Newline),
    ))
    .repeated()
}

fn grouped_by<'t>(
    lhs: Kind,
    parser: impl Parser<'t, Tokens<'t>, (), ParseError<'t>>,
    sep: Kind,
    rhs: Kind,
) -> impl Parser<'t, Tokens<'t>, (), ParseError<'t>> {
    parser
        .padded_by(ws())
        .separated_by(just(sep))
        .allow_trailing()
        .try_map(with_effect)
        .delimited_by(just(lhs), just(rhs))
}

fn binary<'t, Op, R>()
-> impl Fn(Checkpoint, Op, R, &mut MapExtra<'t, '_, Tokens<'t>, ParseError<'t>>) -> Checkpoint {
    move |l, _, _, x| {
        let st: &mut Builder = x.state();
        st.insert(l, Kind::ExprBinaryOp);
        l
    }
}

fn unary<'t, Op>(
    k: Kind,
) -> impl Fn(Checkpoint, Op, &mut MapExtra<'t, '_, Tokens<'t>, ParseError<'t>>) -> Checkpoint {
    move |l, _, x| {
        let st: &mut Builder = x.state();
        st.insert(l, k);
        l
    }
}

fn expr<'t>() -> impl Parser<'t, Tokens<'t>, (), ParseError<'t>> {
    let primary = choice((
        just(Kind::Number),
        just(Kind::String),
        just(Kind::KwTrue),
        just(Kind::KwFalse),
        just(Kind::KwVoid),
        just(Kind::KwBool),
        just(Kind::KwI8),
        just(Kind::KwI16),
        just(Kind::KwI32),
        just(Kind::KwI64),
        just(Kind::KwU8),
        just(Kind::KwU16),
        just(Kind::KwU32),
        just(Kind::KwU64),
        just(Kind::KwUSize),
        just(Kind::KwF32),
        just(Kind::KwF64),
        just(Kind::KwStr),
        just(Kind::KwNumber),
        just(Kind::KwType),
        just(Kind::Ident),
    ));

    let mut expr = Recursive::declare();

    let args = grouped_by(
        Kind::SymLParen,
        expr.clone(),
        Kind::SymComma,
        Kind::SymRParen,
    )
    .labelled("arguments")
    .boxed();
    let obj = as_node(
        Kind::CallObject,
        grouped_by(
            Kind::SymLBrace,
            just(Kind::Ident)
                .then_ignore(just(Kind::SymEq))
                .then(expr.clone())
                .try_map(with_effect),
            Kind::SymComma,
            Kind::SymRBrace,
        )
        .labelled("object expression"),
    );
    let method = as_node(
        Kind::CallMethod,
        just(Kind::SymDot)
            .ignore_then(just(Kind::Ident))
            .then(args.clone())
            .labelled("method expression"),
    );
    let access = as_node(
        Kind::CallAccess,
        just(Kind::SymDot)
            .ignore_then(just(Kind::Ident))
            .labelled("access expression"),
    );
    let type_args = as_node(
        Kind::CallTypeArgs,
        grouped_by(Kind::SymLt, expr.clone(), Kind::SymComma, Kind::SymGt)
            .labelled("type arguments"),
    );
    let chainer = choice((args, obj, method, access, type_args));

    let call = as_node(
        Kind::ExprCall,
        primary.then(chainer.repeated()).labelled("call expression"),
    );

    let op = |op: Kind| checkpoint().then_ignore(just(op)).padded_by(ws());

    let expr_ = checkpoint()
        .then_ignore(call)
        .pratt((
            prefix(
                4,
                checkpoint().then_ignore(
                    expr.clone()
                        .padded_by(ws())
                        .or_not()
                        .delimited_by(just(Kind::SymLBracket), just(Kind::SymRBracket)),
                ),
                unary(Kind::ExprArrayType),
            ),
            prefix(4, op(Kind::SymAnd), unary(Kind::ExprRefType)),
            infix(left(3), op(Kind::SymMul), binary()),
            infix(left(2), op(Kind::SymPlus), binary()),
            infix(left(2), op(Kind::SymMinus), binary()),
            infix(left(1), op(Kind::SymLt), binary()),
            infix(left(1), op(Kind::SymLe), binary()),
            infix(left(1), op(Kind::SymGt), binary()),
            infix(left(1), op(Kind::SymGe), binary()),
            infix(left(1), op(Kind::SymEqEq), binary()),
        ))
        .try_map(with_effect)
        .boxed();

    expr.define(expr_);
    expr
}
