use crate::syntax::lex::{Keyword, Symbol, Token};
use crate::syntax::{Spanned, SyntaxError};
use crate::{BuiltinType, Float, Integer, Type};
use chumsky::Parser;
use chumsky::extra::ParserExtra;
use chumsky::input::{MapExtra, ValueInput};
use chumsky::pratt::{infix, left, prefix};
use chumsky::prelude::{Input, IterParser, SimpleSpan, choice, just, recursive};
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

#[derive(Default, Debug)]
pub struct File {
    decls: Vec<Spanned<Doc<Decl>>>,
    main: Option<Id>,
}

#[derive(Debug)]
struct Doc<T> {
    doc: Vec<String>,
    item: T,
}

impl<T> Doc<T> {
    fn map<F, U>(self, f: F) -> Doc<U>
    where
        F: FnOnce(T) -> U,
    {
        Doc {
            doc: self.doc,
            item: f(self.item),
        }
    }
}

#[derive(Debug)]
pub struct Decl {
    sig: Sig,
    def: Def,
}

#[derive(Debug)]
enum Sig {
    Fun(Fun),
    Typ {
        name: Spanned<Ident>,
        constrs: Vec<Spanned<Doc<Constr>>>,
    },
    Struct {
        name: Spanned<Ident>,
        constrs: Vec<Spanned<Doc<Constr>>>,
        members: Vec<Spanned<Doc<Member>>>,
        optional: Option<Spanned<Doc<Param>>>,
    },
}

#[derive(Debug)]
struct Fun {
    name: Spanned<Ident>,
    constrs: Vec<Spanned<Doc<Constr>>>,
    params: Vec<Spanned<Doc<Param>>>,
    ret: Option<Spanned<Expr>>,
}

#[derive(Debug)]
struct Param {
    name: Spanned<Ident>,
    typ: Spanned<Expr>,
}

#[derive(Debug)]
struct Constr {
    typ: Spanned<Ident>,
    constr: Spanned<Expr>,
    default: Option<Spanned<Expr>>,
}

#[derive(Debug)]
enum Def {
    Fun(Vec<Spanned<Stmt>>),
    Typ(Spanned<Expr>),
    Struct,
}

#[derive(Debug)]
enum Member {
    Data(Param),
    Type(Constr),
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
        then: Spanned<Branch>,
        elif: Vec<Spanned<Branch>>,
        els: Option<Spanned<Vec<Spanned<Self>>>>,
    },
    While(Branch),
    Break,
    Continue,
}

#[derive(Debug, Clone)]
pub struct Branch {
    pub cond: Spanned<Expr>,
    pub body: Vec<Spanned<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Ident(Ident),

    BuiltinType(BuiltinType),
    Apply(Box<Spanned<Self>>, Vec<Spanned<Self>>),
    ArrayType {
        elem: Box<Spanned<Self>>,
        len: Option<Box<Spanned<Self>>>,
    },

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
        I: Input<'src, Span = SimpleSpan>,
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
    Method(Spanned<Ident>, Vec<Spanned<Expr>>),
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
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
    P: Parser<'t, I, O, ParseError<'t>> + Clone,
{
    parser
        .separated_by(just(Token::Symbol(sep)))
        .allow_trailing()
        .collect()
        .delimited_by(just(Token::Symbol(lhs)), just(Token::Symbol(rhs)))
}

fn grouped_with<'t, I, O, P>(
    lhs: Symbol,
    parser: P,
    rhs: Symbol,
) -> impl Parser<'t, I, Vec<O>, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
    P: Parser<'t, I, O, ParseError<'t>>,
{
    parser
        .repeated()
        .collect()
        .delimited_by(just(Token::Symbol(lhs)), just(Token::Symbol(rhs)))
}

fn name<'t, I>() -> impl Parser<'t, I, Spanned<Ustr>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    select(|x, _| match x {
        Token::Ident(n) => Some(n),
        _ => None,
    })
    .map_with(Spanned::from_map_extra)
    .labelled("name")
}

fn ident<'t, I>() -> impl Parser<'t, I, Spanned<Ident>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    name().map(|n| n.map(|n| Ident::Id(Id::bound(n))))
}

pub fn expr<'t, I>() -> impl Parser<'t, I, Spanned<Expr>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
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

    let i = ident()
        .map(|i| i.map(Expr::Ident))
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
            .ignore_then(ident())
            .then(args)
            .map(|(i, args)| Chainer::Method(i, args))
            .labelled("method expression");
        let access = just(Token::Symbol(Symbol::Dot))
            .ignore_then(name())
            .map(Chainer::Access)
            .labelled("access expression");
        let type_args = grouped_by(Symbol::Lt, expr.clone(), Symbol::Comma, Symbol::Gt)
            .map(Chainer::TypeArgs)
            .labelled("type arguments");
        let chainer = choice((arguments, obj, method, access, type_args));

        let call = choice((constant, i))
            .foldl_with(chainer.repeated(), |a, c, e| Spanned {
                span: e.span(),
                item: match c {
                    Chainer::Args(args) => Expr::Call(Box::new(a), args),
                    Chainer::Initialize(xs) => Expr::Object(Box::new(a), Object::Unordered(xs)),
                    Chainer::Access(m) => Expr::Access(Box::new(a), Access::Named(m)),
                    Chainer::Method(method, args) => Expr::Method {
                        callee: Box::new(a),
                        target: None,
                        method,
                        args,
                    },
                    Chainer::TypeArgs(args) => Expr::Apply(Box::new(a), args),
                },
            })
            .labelled("call expression");

        call.pratt((
            prefix(
                4,
                expr.or_not().delimited_by(
                    just(Token::Symbol(Symbol::LBracket)),
                    just(Token::Symbol(Symbol::RBracket)),
                ),
                |len: Option<_>, elem, e| {
                    Spanned::from_map_extra(
                        Expr::ArrayType {
                            elem: Box::new(elem),
                            len: len.map(Box::new),
                        },
                        e,
                    )
                },
            ),
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
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    let assign = just(Token::Keyword(Keyword::Let))
        .ignore_then(ident())
        .then(
            just(Token::Symbol(Symbol::Colon))
                .ignore_then(expr())
                .or_not(),
        )
        .then_ignore(just(Token::Symbol(Symbol::Eq)))
        .then(expr())
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|((name, typ), rhs)| Stmt::Assign { name, typ, rhs })
        .map_with(Spanned::from_map_extra)
        .labelled("assignment statement");

    let update = ident()
        .then_ignore(just(Token::Symbol(Symbol::Eq)))
        .then(expr())
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|(name, rhs)| Stmt::Update { name, rhs })
        .map_with(Spanned::from_map_extra)
        .labelled("update statement");

    let r#break = just(Token::Keyword(Keyword::Break))
        .then(just(Token::Symbol(Symbol::Semi)))
        .map(|_| Stmt::Break)
        .map_with(Spanned::from_map_extra)
        .labelled("break statement");

    let r#continue = just(Token::Keyword(Keyword::Continue))
        .then(just(Token::Symbol(Symbol::Semi)))
        .map(|_| Stmt::Continue)
        .map_with(Spanned::from_map_extra)
        .labelled("continue statement");

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
            .map(|((span, cond), body)| Spanned {
                span,
                item: Branch { cond, body },
            })
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
                    .map(|(span, item)| Spanned { span, item })
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
            .map(|((.., cond), body)| Stmt::While(Branch { cond, body }))
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
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    select(|x, _| match x {
        Token::Doc(s) => Some(s),
        _ => None,
    })
    .repeated()
    .collect::<Vec<_>>()
    .labelled("docstring")
}

fn constr<'t, I>() -> impl Parser<'t, I, Spanned<Constr>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    ident()
        .then(
            just(Token::Symbol(Symbol::Colon))
                .ignore_then(expr())
                .or_not(),
        )
        .then(just(Token::Symbol(Symbol::Eq)).ignore_then(expr()).or_not())
        .map(|((typ, constr), default)| Constr {
            constr: constr.unwrap_or(Spanned {
                span: typ.span,
                item: Expr::BuiltinType(BuiltinType::Type),
            }),
            typ,
            default,
        })
        .map_with(Spanned::from_map_extra)
}

fn constrs<'t, I>() -> impl Parser<'t, I, Vec<Spanned<Doc<Constr>>>, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    let constr = docstring()
        .then(constr())
        .map(|(doc, c)| c.map(|item| Doc { doc, item }))
        .labelled("constraint");
    grouped_by(Symbol::Lt, constr, Symbol::Comma, Symbol::Gt)
        .or_not()
        .map(Option::unwrap_or_default)
        .labelled("constraints")
}

fn param<'t, I>() -> impl Parser<'t, I, Spanned<Doc<Param>>, ParseError<'t>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    docstring()
        .then(ident())
        .then(just(Token::Symbol(Symbol::Colon)).ignore_then(expr()))
        .map(|((doc, name), typ)| Doc {
            doc,
            item: Param { name, typ },
        })
        .map_with(Spanned::from_map_extra)
}

fn func<'t, I>() -> impl Parser<'t, I, Spanned<Doc<Decl>>, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    let param = param().labelled("parameter");

    let params =
        grouped_by(Symbol::LParen, param, Symbol::Comma, Symbol::RParen).labelled("parameters");

    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Fun)))
        .then(ident())
        .then(constrs())
        .then(params)
        .then(expr().or_not())
        .then(stmt().repeated().collect().delimited_by(
            just(Token::Symbol(Symbol::LBrace)),
            just(Token::Symbol(Symbol::RBrace)),
        ))
        .map(|(((((doc, name), constrs), params), ret), body)| Doc {
            doc,
            item: Decl {
                sig: Sig::Fun(Fun {
                    name,
                    constrs,
                    params,
                    ret,
                }),
                def: Def::Fun(body),
            },
        })
        .map_with(Spanned::from_map_extra)
        .labelled("function definition")
}

fn typ<'t, I>() -> impl Parser<'t, I, Spanned<Doc<Decl>>, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Typ)))
        .then(ident())
        .then(constrs())
        .then_ignore(just(Token::Symbol(Symbol::Eq)))
        .then(expr())
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|(((doc, name), constrs), typ)| Doc {
            doc,
            item: Decl {
                sig: Sig::Typ { name, constrs },
                def: Def::Typ(typ),
            },
        })
        .map_with(Spanned::from_map_extra)
        .labelled("type alias definition")
}

fn r#struct<'t, I>() -> impl Parser<'t, I, Spanned<Doc<Decl>>, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    let data = param()
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|p| p.map(|p| p.map(Member::Data)))
        .labelled("data member");
    let typ = docstring()
        .then_ignore(just(Token::Keyword(Keyword::Typ)))
        .then(constr())
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|(doc, c)| Doc {
            doc,
            item: Member::Type(c.item),
        })
        .map_with(Spanned::from_map_extra)
        .labelled("type member");
    let optional = docstring()
        .then(ident())
        .then_ignore(just(Token::Symbol(Symbol::Question)))
        .then(just(Token::Symbol(Symbol::Colon)).ignore_then(expr()))
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|((doc, name), typ)| Doc {
            doc,
            item: Param { name, typ },
        })
        .map_with(Spanned::from_map_extra)
        .labelled("optional data member");

    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Struct)))
        .then(ident())
        .then(constrs())
        .then(
            choice((data, typ))
                .repeated()
                .collect()
                .then(optional.or_not())
                .delimited_by(
                    just(Token::Symbol(Symbol::LBrace)),
                    just(Token::Symbol(Symbol::RBrace)),
                ),
        )
        .map(|(((doc, name), constrs), (items, optional))| Doc {
            doc,
            item: Decl {
                sig: Sig::Struct {
                    name,
                    constrs,
                    members: items,
                    optional,
                },
                def: Def::Struct,
            },
        })
        .map_with(Spanned::from_map_extra)
        .labelled("struct definition")
}

pub fn file<'t, I>() -> impl Parser<'t, I, File, ParseError<'t>>
where
    I: ValueInput<'t, Token = Token, Span = SimpleSpan>,
{
    choice((func(), typ(), r#struct()))
        .repeated()
        .collect::<Vec<_>>()
        .map(|decls| File {
            decls,
            ..Default::default()
        })
        .labelled("file")
}
