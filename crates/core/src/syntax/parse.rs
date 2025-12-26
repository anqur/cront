use crate::syntax::lex::{Keyword, Symbol, Token};
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

#[derive(Debug, Clone)]
pub enum Stmt {
    Expr(Expr),

    Assign {
        name: Spanned<Ident>,
        typ: Option<Spanned<Expr>>,
        rhs: Spanned<Expr>,
    },
    Update {
        name: Spanned<Ident>,
        rhs: Spanned<Expr>,
    },

    Return(Option<Spanned<Expr>>),
    If {
        then: Branch,
        elif: Vec<Branch>,
        els: Option<(Span, Vec<Spanned<Self>>)>,
    },
    While(Branch),
    Break,
    Continue,
}

#[derive(Debug, Clone)]
pub struct Branch {
    pub span: Span,
    pub cond: Spanned<Expr>,
    pub body: Vec<Spanned<Stmt>>,
}

#[derive(Debug)]
pub struct Decl {
    doc: Vec<String>,
    sig: Sig,
    def: Def,
}

#[derive(Debug)]
enum Sig {
    Func(FuncSig),
}

#[derive(Debug)]
struct FuncSig {
    name: Spanned<Id>,
    constrs: Vec<Spanned<Constr>>,
    params: Vec<Spanned<Param>>,
    ret: Option<Spanned<Expr>>,
}

#[derive(Debug)]
struct Param {
    name: Ident,
    typ: Spanned<Expr>,
}

#[derive(Debug)]
struct Constr {
    typ: Ident,
    constr: Spanned<Expr>,
}

#[derive(Debug)]
enum Def {
    Func { body: Vec<Spanned<Stmt>> },
}

#[derive(Default, Debug)]
pub struct File {
    decls: Vec<Spanned<Decl>>,
    main: Option<Id>,
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
            infix(left(4), just(Token::Symbol(Symbol::At)), Expr::binary),
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

pub fn stmt<'t, I>() -> impl Parser<'t, I, Spanned<Stmt>, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let assign = just(Token::Keyword(Keyword::Let))
        .ignore_then(id())
        .then(
            just(Token::Symbol(Symbol::Colon))
                .ignore_then(expr())
                .or_not(),
        )
        .then_ignore(just(Token::Symbol(Symbol::Eq)))
        .then(expr())
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|((id, typ), rhs)| Stmt::Assign {
            name: id.map(Ident::Id),
            typ,
            rhs,
        })
        .map_with(Spanned::from_map_extra)
        .labelled("assignment statement");

    let update = id()
        .then_ignore(just(Token::Symbol(Symbol::Eq)))
        .then(expr())
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|(id, rhs)| Stmt::Update {
            name: id.map(Ident::Id),
            rhs,
        })
        .map_with(Spanned::from_map_extra)
        .labelled("update statement");

    let ctrl = |kw, stmt: Stmt| {
        just(Token::Keyword(kw))
            .ignore_then(just(Token::Symbol(Symbol::Semi)))
            .ignored()
            .map(move |_| stmt.clone())
            .map_with(Spanned::from_map_extra)
    };

    let r#break = ctrl(Keyword::Break, Stmt::Break).labelled("break statement");

    let r#continue = ctrl(Keyword::Continue, Stmt::Continue).labelled("continue statement");

    let r#return = just(Token::Keyword(Keyword::Return))
        .ignore_then(expr().or_not())
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(Stmt::Return)
        .map_with(Spanned::from_map_extra)
        .labelled("return statement");

    let cmd = expr()
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|e| e.map(Stmt::Expr))
        .labelled("expression statement");

    let cond = |kw| {
        just(Token::Keyword(kw))
            .map_with(|_, e| e.span())
            .then(expr())
    };

    recursive(|stmt| {
        let stmts = stmt.repeated().collect::<Vec<_>>().labelled("statements");

        let branch = cond(Keyword::If)
            .then(stmts.clone().delimited_by(
                just(Token::Symbol(Symbol::LBrace)),
                just(Token::Symbol(Symbol::RBrace)),
            ))
            .map(|((span, cond), body)| Branch { span, cond, body })
            .labelled("if branch");

        let r#if = branch
            .clone()
            .then(
                just(Token::Keyword(Keyword::Else))
                    .ignore_then(branch)
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .then(
                just(Token::Keyword(Keyword::Else))
                    .map_with(|_, e| e.span())
                    .then(stmts.clone().delimited_by(
                        just(Token::Symbol(Symbol::LBrace)),
                        just(Token::Symbol(Symbol::RBrace)),
                    ))
                    .or_not(),
            )
            .map(|((then, elif), els)| Stmt::If { then, elif, els })
            .map_with(Spanned::from_map_extra)
            .labelled("if statement");

        let r#while = cond(Keyword::While)
            .then(stmts.clone().delimited_by(
                just(Token::Symbol(Symbol::LBrace)),
                just(Token::Symbol(Symbol::RBrace)),
            ))
            .map(|((span, cond), body)| Stmt::While(Branch { span, cond, body }))
            .map_with(Spanned::from_map_extra)
            .labelled("while statement");

        choice((
            r#if, r#while, r#break, r#continue, assign, update, r#return, cmd,
        ))
        .labelled("statement")
    })
}

fn docstring<'t, I>() -> impl Parser<'t, I, Vec<String>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    select(|x, _| match x {
        Token::Doc(s) => Some(s),
        _ => None,
    })
    .repeated()
    .collect::<Vec<_>>()
    .labelled("docstring")
}

fn type_params<'t, I>() -> impl Parser<'t, I, Vec<Spanned<Constr>>, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let param = id()
        .then(
            just(Token::Symbol(Symbol::Colon))
                .ignore_then(expr())
                .or_not(),
        )
        .map(|(id, constr)| Spanned {
            span: id.span,
            item: Constr {
                typ: Ident::Id(id.item),
                constr: constr.unwrap_or(Spanned {
                    span: id.span,
                    item: Expr::BuiltinType(BuiltinType::Type),
                }),
            },
        })
        .labelled("type parameter");
    grouped_by(Symbol::Lt, param, Symbol::Comma, Symbol::Gt)
        .or_not()
        .map(Option::unwrap_or_default)
        .labelled("type parameters")
}

fn func<'t, I>() -> impl Parser<'t, I, Spanned<Decl>, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let param = id()
        .then(just(Token::Symbol(Symbol::Colon)).ignore_then(expr()))
        .map(|(id, typ)| {
            id.map(|name| Param {
                name: Ident::Id(name),
                typ,
            })
        })
        .labelled("parameter");

    let params =
        grouped_by(Symbol::LParen, param, Symbol::Comma, Symbol::RParen).labelled("parameters");

    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Fun)))
        .then(id())
        .then(type_params())
        .then(params)
        .then(expr().or_not())
        .then(stmt().repeated().collect().delimited_by(
            just(Token::Symbol(Symbol::LBrace)),
            just(Token::Symbol(Symbol::RBrace)),
        ))
        .map(|(((((doc, name), constrs), params), ret), body)| Decl {
            doc,
            sig: Sig::Func(FuncSig {
                name,
                constrs,
                params,
                ret,
            }),
            def: Def::Func { body },
        })
        .map_with(Spanned::from_map_extra)
        .labelled("function definition")
}

pub fn file<'t, I>() -> impl Parser<'t, I, File, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    func()
        .repeated()
        .collect::<Vec<_>>()
        .map(|decls| File { decls, main: None })
        .labelled("file")
}
