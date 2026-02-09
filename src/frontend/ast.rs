use crate::frontend::lex::{Symbol, Token};
use crate::{BuiltinType, Float, Integer, Span, Type};
use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::cmp::Ordering;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::str::FromStr;
use strum::{Display, EnumString};
use ustr::Ustr;

#[derive(Default, Debug, Copy, Clone)]
pub(crate) struct Idents(u64);

impl Idents {
    pub(crate) fn fresh(&mut self, ident: &mut Ident) {
        self.0 += 1;
        ident.fresh(self.0);
    }

    pub(crate) fn intermediate(&mut self, text: &str) -> Ident {
        let mut i = Ident::unbound(text.into());
        self.fresh(&mut i);
        i
    }
}

#[derive(Copy, Clone, Eq)]
pub struct Ident {
    pub(crate) text: Ustr,
    pub(crate) id: u64,
}

impl Ident {
    pub(crate) fn unbound(text: Ustr) -> Self {
        Self {
            text,
            id: Default::default(),
        }
    }

    pub(crate) fn fresh(&mut self, id: u64) {
        self.id = id
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.text)
    }
}

impl Debug for Ident {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}@{}", self.text, self.id)
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Hash for Ident {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl PartialOrd for Ident {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ident {
    fn cmp(&self, other: &Self) -> Ordering {
        self.id.cmp(&other.id)
    }
}

#[repr(u64)]
#[derive(Debug, Copy, Clone, Display, EnumString, IntoPrimitive, TryFromPrimitive)]
pub(crate) enum Builtin {
    #[strum(serialize = "assert")]
    Assert,
    CInt,
}

impl Builtin {
    pub(crate) fn from_raw(text: &str) -> Option<u64> {
        Self::from_str(text).ok().map(|b| u64::MAX - b as u64)
    }

    pub(crate) fn from_id(id: u64) -> Option<Self> {
        Self::try_from(u64::MAX - id).ok()
    }
}

#[derive(Default, Debug)]
pub struct File {
    pub(crate) idents: Idents,
    pub(crate) decls: Vec<Span<Doc<Decl>>>,
    pub(crate) main: Option<Ident>,
}

#[derive(Debug)]
pub(crate) struct Doc<T> {
    pub(crate) doc: Vec<String>,
    pub(crate) item: T,
}

impl<T> Span<Doc<T>> {
    pub(crate) fn inner(&self) -> &T {
        &self.item.item
    }

    pub(crate) fn inner_mut(&mut self) -> &mut T {
        &mut self.item.item
    }
}

impl<T> Doc<T> {
    pub(crate) fn map<F, U>(self, f: F) -> Doc<U>
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
    pub(crate) sig: Sig,
    pub(crate) def: Def,
}

#[derive(Debug)]
pub(crate) enum Sig {
    Fun(Fun),
    Typ {
        name: Span<Ident>,
        constrs: Vec<Span<Doc<Constr>>>,
        typ: Span<Expr>,
    },
    #[allow(dead_code)]
    Struct {
        name: Span<Ident>,
        constrs: Vec<Span<Doc<Constr>>>,
        members: Vec<Span<Doc<Member>>>,
        optional: Option<Span<Doc<Param>>>,
    },
}

#[derive(Debug)]
pub(crate) struct Fun {
    pub(crate) binder: Option<Span<Ident>>,
    pub(crate) name: Span<Ident>,
    pub(crate) constrs: Vec<Span<Doc<Constr>>>,
    pub(crate) params: Vec<Span<Doc<Param>>>,
    pub(crate) ret: Option<Span<Expr>>,
}

#[derive(Debug)]
pub(crate) struct Param {
    pub(crate) name: Span<Ident>,
    pub(crate) typ: Span<Expr>,
}

#[derive(Debug)]
pub(crate) struct Constr {
    pub(crate) typ: Span<Ident>,
    pub(crate) constr: Span<Expr>,
    pub(crate) default: Option<Span<Expr>>,
}

#[derive(Debug)]
pub(crate) enum Def {
    Fun(Vec<Span<Stmt>>),
    Typ,
    Struct,
}

#[derive(Debug)]
#[allow(dead_code)]
pub(crate) enum Member {
    Data(Param),
    Type(Constr),
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Expr(Expr),

    Assign {
        name: Span<Ident>,
        typ: Option<Span<Expr>>,
        rhs: Span<Expr>,
        checked: Option<Span<Type>>,
    },
    Update {
        name: Span<Ident>,
        rhs: Span<Expr>,
    },

    Return(Option<Span<Expr>>),
    If {
        then: Span<Branch>,
        elif: Vec<Span<Branch>>,
        els: Option<Span<Vec<Span<Self>>>>,
    },
    While {
        branch: Branch,
        exit: Option<Span<Ident>>,
    },
    Break,
    Continue,

    Decl {
        name: Span<Ident>,
        checked: Span<Type>,
    },
}

#[derive(Debug, Clone)]
pub struct Branch {
    pub cond: Span<Expr>,
    pub body: Vec<Span<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Ident(Ident),

    BuiltinType(BuiltinType),
    Apply(Box<Span<Self>>, Vec<Span<Self>>),
    RefType(Box<Span<Self>>),
    ArrayType {
        elem: Box<Span<Self>>,
        len: Option<Box<Span<Self>>>,
    },

    Integer(Integer),
    Float(Float),
    String(String),
    Boolean(bool),

    Call {
        callee: Box<Span<Self>>,
        args: Vec<Span<Self>>,
        checked: Option<Span<Type>>,
    },
    BinaryOp {
        lhs: Box<Span<Self>>,
        op: Symbol,
        rhs: Box<Span<Self>>,
        checked: Option<Span<Type>>,
    },
    Object(Box<Span<Self>>, Vec<(Span<Ustr>, Span<Expr>)>),
    #[allow(dead_code)]
    Access(Box<Span<Self>>, Span<Ustr>),
    #[allow(dead_code)]
    Method {
        callee: Box<Span<Self>>,
        target: Option<Ident>,
        method: Span<Ident>,
        args: Vec<Span<Self>>,
    },
}

impl Expr {
    pub(crate) fn binary<'src, 'b, I, E>(
        lhs: Span<Self>,
        op: Token,
        rhs: Span<Self>,
        e: &mut MapExtra<'src, 'b, I, E>,
    ) -> Span<Self>
    where
        I: Input<'src, Span = SimpleSpan>,
        E: ParserExtra<'src, I>,
    {
        let Token::Symbol(op) = op else {
            unreachable!()
        };
        Span::from_map_extra(
            Self::BinaryOp {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
                checked: None,
            },
            e,
        )
    }
}
