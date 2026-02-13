use crate::frontend::ast::{
    Branch, Constr, Decl, Def, Doc, Expr, File, Fun, Ident, Member, Param, Sig, Stmt,
};
use crate::frontend::lex::{Keyword, Symbol, Token, lex};
use crate::frontend::{Span, SyntaxError};
use crate::{BuiltinType, Float, Integer};
use chumsky::Parser;
use chumsky::pratt::{infix, left, prefix};
use chumsky::prelude::{IterParser, choice, just, recursive};
use chumsky::primitive::select;
use serde_json::from_str;
use ustr::Ustr;

enum Chainer {
    Args(Vec<Span<Expr>>),
    Initialize(Vec<(Span<Ustr>, Span<Expr>)>),
    Access(Span<Ustr>),
    Method(Span<Ident>, Vec<Span<Expr>>),
    TypeArgs(Vec<Span<Expr>>),
}

type ParseError<'a> = SyntaxError<'a, Token>;

fn grouped_by<'t, O>(
    lhs: Symbol,
    parser: impl Parser<'t, &'t [Token], O, ParseError<'t>> + Clone,
    sep: Symbol,
    rhs: Symbol,
) -> impl Parser<'t, &'t [Token], Vec<O>, ParseError<'t>> + Clone {
    parser
        .separated_by(just(Token::Symbol(sep)))
        .allow_trailing()
        .collect()
        .delimited_by(just(Token::Symbol(lhs)), just(Token::Symbol(rhs)))
}

fn name<'t>() -> impl Parser<'t, &'t [Token], Span<Ustr>, ParseError<'t>> + Clone {
    select(|x, _| match x {
        Token::Ident(n) => Some(n),
        _ => None,
    })
    .map_with(Span::from_map_extra)
    .labelled("name")
}

fn ident<'t>() -> impl Parser<'t, &'t [Token], Span<Ident>, ParseError<'t>> + Clone {
    name().map(|n| n.map(Ident::unbound))
}

fn expr<'t>() -> impl Parser<'t, &'t [Token], Span<Expr>, ParseError<'t>> + Clone {
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
    .map_with(Span::from_map_extra)
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
            .foldl_with(chainer.repeated(), |a, c, e| {
                Span::new(
                    e.span(),
                    match c {
                        Chainer::Args(args) => Expr::Call {
                            callee: Box::new(a),
                            args,
                            checked: None,
                        },
                        Chainer::Initialize(xs) => Expr::Object(Box::new(a), xs),
                        Chainer::Access(m) => Expr::Access(Box::new(a), m),
                        Chainer::Method(method, args) => Expr::Method {
                            callee: Box::new(a),
                            target: None,
                            method,
                            args,
                        },
                        Chainer::TypeArgs(args) => Expr::Apply(Box::new(a), args),
                    },
                )
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
                    Span::from_map_extra(
                        Expr::ArrayType {
                            elem: Box::new(elem),
                            len: len.map(Box::new),
                        },
                        e,
                    )
                },
            ),
            prefix(4, just(Token::Symbol(Symbol::And)), |_, t, e| {
                Span::from_map_extra(Expr::RefType(Box::new(t)), e)
            }),
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

fn stmt<'t>() -> impl Parser<'t, &'t [Token], Span<Stmt>, ParseError<'t>> {
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
        .map(|((name, typ), rhs)| Stmt::Assign {
            name,
            typ,
            rhs,
            checked: None,
        })
        .map_with(Span::from_map_extra)
        .labelled("assignment statement");

    let update = ident()
        .then_ignore(just(Token::Symbol(Symbol::Eq)))
        .then(expr())
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|(name, rhs)| Stmt::Update { name, rhs })
        .map_with(Span::from_map_extra)
        .labelled("update statement");

    let r#break = just(Token::Keyword(Keyword::Break))
        .then(just(Token::Symbol(Symbol::Semi)))
        .map(|_| Stmt::Break)
        .map_with(Span::from_map_extra)
        .labelled("break statement");

    let r#continue = just(Token::Keyword(Keyword::Continue))
        .then(just(Token::Symbol(Symbol::Semi)))
        .map(|_| Stmt::Continue)
        .map_with(Span::from_map_extra)
        .labelled("continue statement");

    let r#return = just(Token::Keyword(Keyword::Return))
        .ignore_then(expr().or_not())
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(Stmt::Return)
        .map_with(Span::from_map_extra)
        .labelled("return statement");

    let cmd = expr()
        .then_ignore(just(Token::Symbol(Symbol::Semi)))
        .map(|e| e.map(Stmt::Expr))
        .labelled("command statement");

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
            .map(|((span, cond), body)| Span::new(span, Branch { cond, body }))
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
                    .map(|(span, item)| Span::new(span, item))
                    .or_not(),
            )
            .map(|((then, elif), els)| Stmt::If { then, elif, els })
            .map_with(Span::from_map_extra)
            .labelled("if statement");

        let r#while = cond(Keyword::While)
            .then(stmts.clone().delimited_by(
                just(Token::Symbol(Symbol::LBrace)),
                just(Token::Symbol(Symbol::RBrace)),
            ))
            .map(|((.., cond), body)| Stmt::While {
                branch: Branch { cond, body },
                exit: None,
            })
            .map_with(Span::from_map_extra)
            .labelled("while statement");

        choice((
            r#if, r#while, r#break, r#continue, assign, update, r#return, cmd,
        ))
        .labelled("statement")
    })
}

fn docstring<'t>() -> impl Parser<'t, &'t [Token], Vec<String>, ParseError<'t>> + Clone {
    select(|x, _| match x {
        Token::Doc(s) => Some(s),
        _ => None,
    })
    .repeated()
    .collect::<Vec<_>>()
    .labelled("docstring")
}

fn constr<'t>() -> impl Parser<'t, &'t [Token], Span<Constr>, ParseError<'t>> + Clone {
    ident()
        .then(
            just(Token::Symbol(Symbol::Colon))
                .ignore_then(expr())
                .or_not(),
        )
        .then(just(Token::Symbol(Symbol::Eq)).ignore_then(expr()).or_not())
        .map(|((typ, constr), default)| Constr {
            constr: constr.unwrap_or(Span::new(typ.span, Expr::BuiltinType(BuiltinType::Type))),
            typ,
            default,
        })
        .map_with(Span::from_map_extra)
}

fn constrs<'t>() -> impl Parser<'t, &'t [Token], Vec<Span<Doc<Constr>>>, ParseError<'t>> {
    let constr = docstring()
        .then(constr())
        .map(|(doc, c)| c.map(|item| Doc { doc, item }))
        .labelled("constraint");
    grouped_by(Symbol::Lt, constr, Symbol::Comma, Symbol::Gt)
        .or_not()
        .map(Option::unwrap_or_default)
        .labelled("constraints")
}

fn param<'t>() -> impl Parser<'t, &'t [Token], Span<Doc<Param>>, ParseError<'t>> + Clone {
    docstring()
        .then(ident())
        .then(just(Token::Symbol(Symbol::Colon)).ignore_then(expr()))
        .map(|((doc, name), typ)| Doc {
            doc,
            item: Param { name, typ },
        })
        .map_with(Span::from_map_extra)
}

fn func<'t>() -> impl Parser<'t, &'t [Token], Span<Doc<Decl>>, ParseError<'t>> {
    let param = param().labelled("parameter");

    let params =
        grouped_by(Symbol::LParen, param, Symbol::Comma, Symbol::RParen).labelled("parameters");

    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Fun)))
        .then(
            ident()
                .then_ignore(just(Token::Symbol(Symbol::ColonColon)))
                .or_not(),
        )
        .then(ident())
        .then(constrs())
        .then(params)
        .then(expr().or_not())
        .then(stmt().repeated().collect().delimited_by(
            just(Token::Symbol(Symbol::LBrace)),
            just(Token::Symbol(Symbol::RBrace)),
        ))
        .map(
            |((((((doc, binder), name), constrs), params), ret), body)| Doc {
                doc,
                item: Decl {
                    sig: Sig::Fun(Fun {
                        binder,
                        name,
                        constrs,
                        params,
                        ret,
                    }),
                    def: Def::Fun(body),
                },
            },
        )
        .map_with(Span::from_map_extra)
        .labelled("function definition")
}

fn typ<'t>() -> impl Parser<'t, &'t [Token], Span<Doc<Decl>>, ParseError<'t>> {
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
                sig: Sig::Typ { name, constrs, typ },
                def: Def::Typ,
            },
        })
        .map_with(Span::from_map_extra)
        .labelled("type alias definition")
}

fn r#struct<'t>() -> impl Parser<'t, &'t [Token], Span<Doc<Decl>>, ParseError<'t>> {
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
        .map_with(Span::from_map_extra)
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
        .map_with(Span::from_map_extra)
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
        .map_with(Span::from_map_extra)
        .labelled("struct definition")
}

fn file<'t>() -> impl Parser<'t, &'t [Token], File, ParseError<'t>> {
    choice((func(), typ(), r#struct()))
        .repeated()
        .collect::<Vec<_>>()
        .map(|decls| File {
            decls,
            ..Default::default()
        })
        .labelled("file")
}

pub fn parse(text: &str) -> File {
    // TODO: Errors.
    let tokens = lex().parse(text).unwrap();
    file().parse(tokens.tokens.as_slice()).unwrap()
}
