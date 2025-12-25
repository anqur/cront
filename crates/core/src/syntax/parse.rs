use crate::syntax::lex::{Symbol, Token};
use crate::syntax::{Span, Spanned, SyntaxError};
use crate::{BuiltinType, Float, Integer, Type};
use chumsky::Parser;
use chumsky::extra::ParserExtra;
use chumsky::input::{MapExtra, ValueInput};
use chumsky::pratt::{infix, left};
use chumsky::prelude::{Input, IterParser, choice, just, recursive};
use chumsky::primitive::select;
use serde_json::from_str;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use strum::Display;
use ustr::Ustr;

#[derive(Clone, Eq)]
pub struct Id(Rc<Ustr>);

impl Id {
    fn bound(n: Ustr) -> Self {
        Self(Rc::new(n))
    }

    fn id(&self) -> usize {
        Rc::as_ptr(&self.0) as _
    }
}

impl Display for Id {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

impl Debug for Id {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}@{}", self.0, self.id())
    }
}

impl PartialEq for Id {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Hash for Id {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

#[derive(Debug, Clone, Display)]
pub enum Ident {
    #[strum(transparent)]
    Id(Id),
    #[strum(to_string = "_{0}")]
    Idx(usize),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Ident(Ident),

    BuiltinType(BuiltinType),
    Apply(Box<Spanned<Self>>, Vec<Spanned<Self>>),

    Integer(Integer),
    Float(Float),
    String(String),
    Boolean(bool),

    Call(Box<Spanned<Self>>, Vec<Spanned<Self>>),
    BinaryOp(Box<Spanned<Self>>, Symbol, Option<Type>, Box<Spanned<Self>>),
    Object(Box<Spanned<Self>>, Object),
    Access(Box<Spanned<Self>>, Access),
    Method {
        callee: Box<Spanned<Self>>,
        target: Option<Id>,
        method: Spanned<Ident>,
        args: Vec<Spanned<Self>>,
    },
}

impl Expr {
    fn binary<'src, 'b, I, E>(
        lhs: Spanned<Self>,
        op: Token,
        rhs: Spanned<Self>,
        e: &mut MapExtra<'src, 'b, I, E>,
    ) -> Spanned<Self>
    where
        I: Input<'src, Span = Span>,
        E: ParserExtra<'src, I>,
    {
        let Token::Symbol(sym) = op else {
            unreachable!()
        };
        Spanned::from_map_extra(Self::BinaryOp(Box::new(lhs), sym, None, Box::new(rhs)), e)
    }
}

#[derive(Debug, Clone)]
pub enum Object {
    Unordered(Vec<(Spanned<Ustr>, Spanned<Expr>)>),
    Ordered(Vec<Expr>),
}

#[derive(Debug, Clone)]
pub enum Access {
    Named(Spanned<Ustr>),
    Indexed(usize),
}

enum Chainer {
    Args(Vec<Spanned<Expr>>),
    Initialize(Vec<(Spanned<Ustr>, Spanned<Expr>)>),
    Access(Spanned<Ustr>),
    Method(Spanned<Id>, Vec<Spanned<Expr>>),
    TypeArgs(Vec<Spanned<Expr>>),
}

type ParseError<'a> = SyntaxError<'a, Token>;

fn grouped_by<'t, I, O, P>(
    lhs: Symbol,
    parser: P,
    sep: Symbol,
    rhs: Symbol,
) -> impl Parser<'t, I, Vec<O>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
    P: Parser<'t, I, O, ParseError<'t>> + Clone,
{
    parser
        .separated_by(just(Token::Symbol(sep)))
        .allow_trailing()
        .collect()
        .delimited_by(just(Token::Symbol(lhs)), just(Token::Symbol(rhs)))
}

fn name<'t, I>() -> impl Parser<'t, I, Spanned<Ustr>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    select(|x, _| match x {
        Token::Ident(n) => Some(n),
        _ => None,
    })
    .map_with(Spanned::from_map_extra)
    .labelled("name")
}

fn id<'t, I>() -> impl Parser<'t, I, Spanned<Id>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    name().map(|n| n.map(Id::bound)).labelled("identifier")
}

pub fn expr<'t, I>() -> impl Parser<'t, I, Spanned<Expr>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let constant = select(|x, _| {
        Some(match x {
            Token::Number(n) => {
                let s = n.as_str();
                from_str::<i64>(s)
                    .map(|n| Expr::Integer(Integer::I64(n)))
                    .unwrap_or_else(|_| Expr::Float(Float::F64(from_str(s).unwrap())))
            }
            Token::String(s) => Expr::String(s),
            Token::Boolean(b) => Expr::Boolean(b),
            Token::BuiltinType(t) => Expr::BuiltinType(t),
            _ => return None,
        })
    })
    .map_with(Spanned::from_map_extra)
    .labelled("constant expression");

    let ident = select(|x, _| match x {
        Token::Ident(n) => Some(Expr::Ident(Ident::Id(Id::bound(n)))),
        _ => None,
    })
    .map_with(Spanned::from_map_extra)
    .labelled("identifier expression");

    recursive(|expr| {
        let args = grouped_by(Symbol::LParen, expr.clone(), Symbol::Comma, Symbol::RParen)
            .labelled("arguments");
        let arguments = args
            .clone()
            .map(Chainer::Args)
            .labelled("arguments expression");
        let obj = grouped_by(
            Symbol::LBrace,
            name()
                .then_ignore(just(Token::Symbol(Symbol::Eq)))
                .then(expr.clone()),
            Symbol::Comma,
            Symbol::RBrace,
        )
        .map(Chainer::Initialize)
        .labelled("object expression");
        let method = just(Token::Symbol(Symbol::Dot))
            .ignore_then(id())
            .then(args)
            .map(|(id, args)| Chainer::Method(id, args))
            .labelled("method expression");
        let access = just(Token::Symbol(Symbol::Dot))
            .ignore_then(name())
            .map(Chainer::Access)
            .labelled("access expression");
        let type_args = grouped_by(Symbol::Lt, expr, Symbol::Comma, Symbol::Gt)
            .map(Chainer::TypeArgs)
            .labelled("type arguments");
        let chainer = choice((arguments, obj, method, access, type_args));

        let call = choice((constant, ident))
            .foldl_with(chainer.repeated(), |a, c, e| Spanned {
                span: e.span(),
                item: match c {
                    Chainer::Args(args) => Expr::Call(Box::new(a), args),
                    Chainer::Initialize(xs) => Expr::Object(Box::new(a), Object::Unordered(xs)),
                    Chainer::Access(m) => Expr::Access(Box::new(a), Access::Named(m)),
                    Chainer::Method(m, args) => Expr::Method {
                        callee: Box::new(a),
                        target: None,
                        method: m.map(Ident::Id),
                        args,
                    },
                    Chainer::TypeArgs(args) => Expr::Apply(Box::new(a), args),
                },
            })
            .labelled("call expression");

        call.pratt((
            infix(left(3), just(Token::Symbol(Symbol::Mul)), Expr::binary),
            infix(left(2), just(Token::Symbol(Symbol::Plus)), Expr::binary),
            infix(left(2), just(Token::Symbol(Symbol::Minus)), Expr::binary),
            infix(left(1), just(Token::Symbol(Symbol::Lt)), Expr::binary),
            infix(left(1), just(Token::Symbol(Symbol::Le)), Expr::binary),
            infix(left(1), just(Token::Symbol(Symbol::Gt)), Expr::binary),
            infix(left(1), just(Token::Symbol(Symbol::Ge)), Expr::binary),
            infix(left(1), just(Token::Symbol(Symbol::EqEq)), Expr::binary),
        ))
        .labelled("expression")
    })
}
