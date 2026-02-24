use crate::Span;
use crate::frontend::cst::{Builder, Kind, Tokens};
use chumsky::error::Rich;
use chumsky::input::MapExtra;
use chumsky::pratt::{infix, left, prefix};
use chumsky::prelude::{Recursive, choice, custom, just};
use chumsky::{Parser, extra};
use cstree::build::{Checkpoint, NodeCache};
use cstree::prelude::SyntaxNode;

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

    let def = checkpoint()
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

    expr.define(def);
    expr
}
fn stmt<'t>() -> impl Parser<'t, Tokens<'t>, (), ParseError<'t>> {
    let assign = as_node(
        Kind::StmtAssign,
        just(Kind::KwLet)
            .then_ignore(ws())
            .ignore_then(just(Kind::Ident))
            .then_ignore(ws())
            .then(
                just(Kind::SymColon)
                    .ignore_then(expr().padded_by(ws()))
                    .or_not(),
            )
            .then_ignore(just(Kind::SymEq))
            .then_ignore(ws())
            .then(expr())
            .then_ignore(ws())
            .then_ignore(just(Kind::SymSemi))
            .labelled("assignment statement"),
    );

    let update = as_node(
        Kind::StmtUpdate,
        just(Kind::Ident)
            .then_ignore(ws())
            .then_ignore(just(Kind::SymEq))
            .then_ignore(ws())
            .then(expr())
            .then_ignore(ws())
            .then_ignore(just(Kind::SymSemi))
            .labelled("update statement"),
    );

    let r#break = as_node(
        Kind::StmtBreak,
        just(Kind::KwBreak)
            .then_ignore(ws())
            .then(just(Kind::SymSemi))
            .labelled("break statement"),
    );

    let r#continue = as_node(
        Kind::StmtContinue,
        just(Kind::KwContinue)
            .then_ignore(ws())
            .then(just(Kind::SymSemi))
            .labelled("continue statement"),
    );

    let r#return = as_node(
        Kind::StmtReturn,
        just(Kind::KwReturn)
            .then_ignore(ws())
            .ignore_then(expr().padded_by(ws()).or_not())
            .then_ignore(just(Kind::SymSemi))
            .labelled("return statement"),
    );

    let exp = as_node(
        Kind::StmtExpr,
        expr()
            .then_ignore(ws())
            .then_ignore(just(Kind::SymSemi))
            .labelled("expression statement"),
    );

    let cond = |kind| as_node(Kind::BranchCond, just(kind).then_ignore(ws()).then(expr()));

    let mut stmt = Recursive::declare();

    let stmts = stmt
        .clone()
        .padded_by(ws())
        .repeated()
        .labelled("statements")
        .boxed();

    let branch = as_node(
        Kind::Branch,
        cond(Kind::KwIf)
            .then_ignore(ws())
            .then(
                stmts
                    .clone()
                    .delimited_by(just(Kind::SymLBrace), just(Kind::SymRBrace)),
            )
            .labelled("if branch"),
    )
    .boxed();

    let r#if = as_node(
        Kind::StmtIf,
        branch
            .clone()
            .then(
                just(Kind::KwElse)
                    .ignore_then(ws())
                    .ignore_then(branch)
                    .padded_by(ws())
                    .repeated(),
            )
            .then(as_node(
                Kind::BranchElse,
                just(Kind::KwElse)
                    .then_ignore(ws())
                    .then(
                        stmts
                            .clone()
                            .delimited_by(just(Kind::SymLBrace), just(Kind::SymRBrace)),
                    )
                    .or_not(),
            ))
            .labelled("if statement"),
    );

    let r#while = as_node(
        Kind::StmtWhile,
        cond(Kind::KwWhile)
            .then_ignore(ws())
            .then(
                stmts
                    .clone()
                    .delimited_by(just(Kind::SymLBrace), just(Kind::SymRBrace)),
            )
            .labelled("while statement"),
    );

    let def = choice((
        r#if, r#while, r#break, r#continue, assign, update, r#return, exp,
    ))
    .labelled("statement")
    .boxed();

    stmt.define(def);
    stmt
}

pub(super) struct State<'t> {
    pub(super) cst: SyntaxNode<Kind>,
    pub(super) cache: NodeCache<'static>,
    pub(super) errs: Vec<Rich<'t, Span<Kind>>>,
}

impl<'t> State<'t> {
    fn parse_with<'s, P>(src: &'t str, tokens: &'t [Span<Kind>], parser: P) -> Self
    where
        P: Parser<'t, Tokens<'t>, (), ParseError<'t>>,
    {
        let mut builder = Builder::new(src);
        let (.., errs) = parser
            .parse_with_state(tokens.into(), &mut builder)
            .into_output_errors();
        let (cst, cache) = builder.finish();
        Self { cst, cache, errs }
    }

    pub(super) fn parse_expr(src: &'t str, tokens: &'t [Span<Kind>]) -> Self {
        Self::parse_with(src, tokens, expr())
    }

    pub(super) fn parse_stmt(src: &'t str, tokens: &'t [Span<Kind>]) -> Self {
        Self::parse_with(src, tokens, stmt())
    }
}
