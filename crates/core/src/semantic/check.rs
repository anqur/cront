use crate::syntax::lex::Symbol;
use crate::syntax::parse::{
    Branch, Builtin, Constr, Def, Doc, Expr, File, Fun, Ident, Idents, Member, Sig, Stmt,
};
use crate::{BuiltinType, CheckErr, Error, Float, FunType, Integer, Result, Span, Type};
use chumsky::prelude::SimpleSpan;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::mem::take;

pub fn check(file: &mut File) -> Result<Items> {
    Checker::default().file(file)
}

#[derive(Default)]
pub struct Items {
    pub(crate) idents: Idents,
    pub(crate) main: Option<Ident>,
    pub(crate) fns: Vec<Span<Item<FunItem>>>,
    pub(crate) structs: Vec<Span<Item<StructItem>>>,
}

#[derive(Clone)]
struct Inferred {
    lhs: Type,
    rhs: Type,
}

impl Inferred {
    fn constr(typ: Type, constr: Type) -> Self {
        Self {
            lhs: typ,
            rhs: constr,
        }
    }

    fn typ(typ: Type) -> Self {
        Self::constr(typ, Type::Builtin(BuiltinType::Type))
    }

    fn value(typ: Type) -> Self {
        Self {
            lhs: Type::Unknown,
            rhs: typ,
        }
    }
}

#[derive(Default)]
struct Checker {
    globals: HashMap<Ident, Inferred>,
    constrs: HashMap<Ident, Type>,
    locals: HashMap<Ident, Type>,
    items: Items,
    errs: Vec<Span<CheckErr>>,
    mono: HashMap<Ident, HashMap<Vec<Type>, Ident>>,
    structs: HashMap<Ident, Item<StructItem>>,
}

impl Checker {
    fn file(mut self, file: &mut File) -> Result<Items> {
        self.items.idents = file.idents;
        self.items.main = file.main;

        let mut fns = Vec::default();
        let mut structs = Vec::default();

        file.decls.iter_mut().for_each(|decl| {
            let span = decl.span;
            match &mut decl.inner_mut().sig {
                Sig::Fun(fun) => {
                    let span = fun.ret.as_ref().map(|s| s.span).unwrap_or(span);
                    let item = self.fun(fun);
                    let f = Type::Fun(Box::new(FunType {
                        params: item
                            .item
                            .params
                            .iter()
                            .map(|(.., typ)| typ.clone())
                            .collect(),
                        ret: item.item.ret.clone(),
                    }));
                    let got = Type::generic(item.constrs.clone(), f.clone());
                    if file.main.as_ref() == Some(&fun.name.item) {
                        self.check_arity(fun.name.span, fun.params.len(), 0);
                        if !matches!(item.item.ret, Type::CType { to, .. } if to == "int") {
                            self.type_mismatch_msg(span, &item.item.ret, "CInt".to_string());
                        }
                    }
                    fns.push(item);
                    self.globals.insert(fun.name.item, Inferred::constr(f, got));
                }
                Sig::Typ { name, constrs, typ } => {
                    let constrs = self.constrs(constrs);
                    let typ =
                        self.with_constrs(&constrs, |s| s.check_type(typ.span, &mut typ.item));
                    let got = Type::generic(constrs, Type::Builtin(BuiltinType::Type));
                    self.globals.insert(name.item, Inferred::constr(typ, got));
                }
                Sig::Struct {
                    name,
                    constrs,
                    members,
                    optional,
                } => {
                    let constrs = self.constrs(constrs);
                    let typ = Type::Struct(name.item);
                    let (types, data, optional) = self.with_constrs(&constrs, |s| {
                        let mut types = HashMap::default();
                        let mut data = HashMap::default();
                        members
                            .iter_mut()
                            .enumerate()
                            .for_each(|(i, m)| match m.inner_mut() {
                                Member::Data(p) => {
                                    data.insert(
                                        p.name.item,
                                        (s.check_type(p.typ.span, &mut p.typ.item), i),
                                    );
                                }
                                Member::Type(c) => {
                                    types.insert(
                                        c.typ.item,
                                        s.check_type(c.constr.span, &mut c.constr.item),
                                    );
                                }
                            });
                        let optional = optional.as_mut().map(|t| {
                            let span = t.span;
                            let param = t.inner_mut();
                            let typ = s.check_type(span, &mut param.typ.item);
                            (param.name.item, typ)
                        });
                        (types, data, optional)
                    });
                    let got = Type::generic(constrs.clone(), Type::Builtin(BuiltinType::Type));
                    structs.push(name.clone());
                    self.globals.insert(name.item, Inferred::constr(typ, got));
                    self.structs.insert(
                        name.item,
                        Item {
                            name: name.item,
                            constrs,
                            mono: Default::default(),
                            item: StructItem {
                                types,
                                data,
                                optional,
                            },
                        },
                    );
                }
            }
        });

        debug_assert!(self.constrs.is_empty());

        let mut fns = fns.into_iter();

        file.decls.iter_mut().for_each(|decl| {
            let span = decl.span;
            match &mut decl.inner_mut().def {
                Def::Fun(body) => {
                    let mut item = fns.next().unwrap();
                    self.with_constrs(&item.constrs, |s| {
                        let mut local = Block::func(item.item.ret.clone());
                        item.item.params.clone().into_iter().for_each(|(i, p)| {
                            s.insert(&mut local, i, p);
                        });
                        let got = s.block(local, body);
                        s.isa(span, &got, &item.item.ret);
                    });
                    item.item.body = take(body);
                    self.items.fns.push(decl.with(item));
                }
                Def::Typ | Def::Struct => (),
            }
        });

        if self.errs.is_empty() {
            self.items.fns.iter_mut().for_each(|f| {
                if let Some(mono) = self.mono.remove(&f.item.name) {
                    f.item.mono = mono.into_iter().collect();
                }
            });
            self.items.structs = structs
                .into_iter()
                .map(|name| name.map(|n| self.structs.remove(&n).unwrap()))
                .collect();
            debug_assert!(self.structs.is_empty());
            Ok(self.items)
        } else {
            Err(Error::Check(self.errs))
        }
    }

    fn fun(&mut self, fun: &mut Fun) -> Item<FunItem> {
        let name = fun.name.item;
        let constrs = self.constrs(&mut fun.constrs);
        let (params, ret) = self.with_constrs(&constrs, |s| {
            (
                fun.params
                    .iter_mut()
                    .map(|p| {
                        let p = p.inner_mut();
                        (p.name.item, s.check_type(p.typ.span, &mut p.typ.item))
                    })
                    .collect(),
                fun.ret
                    .as_mut()
                    .map(|t| s.check_type(t.span, &mut t.item))
                    .unwrap_or(Type::Builtin(BuiltinType::Void)),
            )
        });
        Item {
            name,
            constrs,
            mono: Default::default(),
            item: FunItem {
                params,
                ret,
                body: Default::default(),
            },
        }
    }

    fn constrs(&mut self, constrs: &mut [Span<Doc<Constr>>]) -> Vec<(Ident, Type)> {
        constrs
            .iter_mut()
            .map(|p| {
                let p = p.inner_mut();
                (
                    p.typ.item,
                    self.check_type(p.constr.span, &mut p.constr.item),
                )
            })
            .collect()
    }

    fn with_constrs<R, F: FnOnce(&mut Self) -> R>(&mut self, constrs: &[(Ident, Type)], f: F) -> R {
        for (typ, constr) in constrs {
            let old = self.constrs.insert(*typ, constr.clone());
            debug_assert!(old.is_none());
        }
        let ret = f(self);
        for (typ, ..) in constrs {
            self.constrs.remove(typ);
        }
        ret
    }

    fn insert(&mut self, block: &mut Block, ident: Ident, typ: Type) {
        block.olds.push((ident, self.locals.insert(ident, typ)));
    }

    fn ident(&mut self, ident: &Ident) -> Inferred {
        self.locals
            .get(ident)
            .cloned()
            .map(Inferred::value)
            .or_else(|| {
                self.constrs
                    .get(ident)
                    .map(|_| Inferred::typ(Type::Ident(*ident)))
            })
            .or_else(|| self.globals.get(ident).cloned())
            .or_else(|| Builtin::from_id(ident.id).map(|b| self.builtin(b)))
            .unwrap()
    }

    fn builtin(&mut self, b: Builtin) -> Inferred {
        match b {
            Builtin::Assert => Inferred::value(Type::Fun(Box::new(FunType {
                params: vec![Type::Builtin(BuiltinType::Bool)],
                ret: Type::Builtin(BuiltinType::Void),
            }))),
            Builtin::CInt => {
                let typ = self.items.idents.intermediate("t");
                Inferred::constr(
                    Type::CType {
                        from: Box::new(Type::Ident(typ)),
                        to: "int",
                    },
                    Type::Generic {
                        typ,
                        constr: Box::new(Type::Builtin(BuiltinType::Type)),
                        ret: Box::new(Type::Builtin(BuiltinType::Type)),
                    },
                )
            }
        }
    }

    fn block(&mut self, mut block: Block, stmts: &mut [Span<Stmt>]) -> Type {
        let typ = stmts
            .iter_mut()
            .map(|stmt| self.stmt(&mut block, stmt))
            .last()
            .unwrap_or(Type::Builtin(BuiltinType::Void));
        for (ident, old) in block.olds {
            match old {
                None => self.locals.remove(&ident),
                Some(old) => self.locals.insert(ident, old),
            };
        }
        typ
    }

    fn stmt(&mut self, block: &mut Block, stmt: &mut Span<Stmt>) -> Type {
        match &mut stmt.item {
            Stmt::Expr(e) => self.infer(stmt.span, e).rhs,
            Stmt::Assign { name, typ, rhs, .. } => {
                let rhs_type = typ
                    .as_mut()
                    .map(|t| {
                        let want = self.check_type(t.span, &mut t.item);
                        self.check(rhs.span, &mut rhs.item, &want);
                        want
                    })
                    .unwrap_or_else(|| self.infer(rhs.span, &mut rhs.item).rhs);
                self.insert(block, name.item, rhs_type.clone());
                *typ = Some(rhs_type.to_expr(typ.as_ref().map(|t| t.span).unwrap_or(name.span)));
                rhs_type
            }
            Stmt::Update { name, rhs } => {
                let want = self.ident(&name.item).rhs;
                self.check(rhs.span, &mut rhs.item, &want);
                want
            }
            Stmt::Return(e) => match e {
                None => {
                    let got = Type::Builtin(BuiltinType::Void);
                    self.isa(stmt.span, &got, &block.ret);
                    // FIXME: should be a placeholder.
                    got
                }
                Some(e) => {
                    self.check(e.span, &mut e.item, &block.ret);
                    // FIXME: should be a placeholder.
                    block.ret.clone()
                }
            },
            Stmt::If { then, elif, els } => {
                let want = self.branch(block, &mut then.item);
                elif.iter_mut().for_each(|b| {
                    let got = self.branch(block, &mut b.item);
                    self.isa(b.span, &got, &want)
                });
                if let Some(els) = els {
                    let got = self.block(block.local(), &mut els.item);
                    self.isa(els.span, &got, &want)
                }
                want
            }
            Stmt::While { branch, .. } => self.branch(block, branch),
            Stmt::Break | Stmt::Continue => Type::Builtin(BuiltinType::Void),
            Stmt::Decl { .. } => unreachable!(),
        }
    }

    fn branch(&mut self, block: &Block, branch: &mut Branch) -> Type {
        self.check(
            branch.cond.span,
            &mut branch.cond.item,
            &Type::Builtin(BuiltinType::Bool),
        );
        self.block(block.local(), &mut branch.body)
    }

    fn check(&mut self, span: SimpleSpan, expr: &mut Expr, want: &Type) -> Type {
        if let Expr::Integer(Integer::I64(n)) = expr
            && let Some(t) = want.to_builtin()
            && t.is_integer()
            && let Some(n) = t.narrow_integer(*n)
        {
            *expr = Expr::Integer(n);
            return Type::Unknown;
        }

        if let Expr::Float(Float::F64(n)) = expr
            && let Some(t) = want.to_builtin()
            && t.is_float()
        {
            *expr = Expr::Float(t.narrow_float(*n));
            return Type::Unknown;
        }

        let got = self.infer(span, expr);
        self.isa(span, &got.rhs, want);
        got.lhs
    }

    fn check_type(&mut self, span: SimpleSpan, expr: &mut Expr) -> Type {
        let want = Type::Builtin(BuiltinType::Type);
        self.check(span, expr, &want)
    }

    fn check_args<'a, I: Iterator<Item = &'a mut Span<Expr>>>(
        &mut self,
        span: SimpleSpan,
        got: usize,
        args: I,
        params: &[Type],
    ) {
        self.check_arity(span, got, params.len());
        args.zip(params.iter()).for_each(|(got, want)| {
            self.check(got.span, &mut got.item, want);
        })
    }

    fn check_arity(&mut self, span: SimpleSpan, got: usize, want: usize) {
        if got != want {
            self.errs
                .push(Span::new(span, CheckErr::ArityMismatch { got, want }))
        }
    }

    fn check_number(
        &mut self,
        lhs: &mut Span<Expr>,
        rhs: &mut Span<Expr>,
        typ: &mut Option<Box<Span<Expr>>>,
    ) -> Type {
        let got = self.infer(lhs.span, &mut lhs.item).rhs;
        if self.is_number_type(&got) {
            self.check(rhs.span, &mut rhs.item, &got);
        } else {
            self.type_mismatch_msg(lhs.span, &got, "number".to_string());
        }
        *typ = Some(Box::new(got.to_expr(lhs.span)));
        got
    }

    fn is_number_type(&self, got: &Type) -> bool {
        match got {
            Type::Builtin(t) => t.is_integer() || t.is_float(),
            Type::Ident(t) => matches!(
                self.constrs.get(t),
                Some(Type::Builtin(BuiltinType::Number))
            ),
            _ => false,
        }
    }

    fn infer(&mut self, span: SimpleSpan, expr: &mut Expr) -> Inferred {
        Inferred::value(match expr {
            Expr::Ident(ident) => return self.ident(ident),
            Expr::BuiltinType(t) => return Inferred::typ(Type::Builtin(*t)),
            Expr::RefType(t) => {
                let t = self.check_type(t.span, &mut t.item);
                return Inferred::typ(Type::Ref(Box::new(t)));
            }
            Expr::ArrayType { elem, len } => {
                let elem = Box::new(self.check_type(elem.span, &mut elem.item));
                let len = len.as_mut().map(|len| {
                    let got = self.infer(len.span, &mut len.item).rhs;
                    if !matches!(got, Type::Builtin(b) if b.is_unsigned_integer()) {
                        // TODO: Should be a compile-time constant.
                        self.type_mismatch_msg(len.span, &got, "number".to_string());
                    }
                    Box::new(got)
                });
                return Inferred::typ(Type::Array { elem, len });
            }
            Expr::Apply(t, args) => {
                let Inferred { mut lhs, rhs } = self.infer(t.span, &mut t.item);
                let Type::Generic { typ, mut ret, .. } = rhs else {
                    self.type_mismatch_msg(t.span, &rhs, "generic".to_string());
                    return Inferred::value(rhs);
                };
                let types = args
                    .iter_mut()
                    .map(|arg| {
                        // FIXME: Constraint checking.
                        let arg = self.check_type(arg.span, &mut arg.item);
                        lhs.apply(typ, arg.clone());
                        ret.apply(typ, arg.clone());
                        arg
                    })
                    .collect();
                if let Type::Fun(..) = lhs
                    && let Expr::Ident(name) = &mut t.item
                {
                    let mono = self.mono.entry(*name).or_default();
                    match mono.entry(types) {
                        Entry::Occupied(found) => *name = *found.get(),
                        Entry::Vacant(entry) => {
                            self.items.idents.fresh(name);
                            entry.insert(*name);
                        }
                    }
                }
                return Inferred::constr(lhs, *ret);
            }
            Expr::Integer(n) => {
                debug_assert!(matches!(n, Integer::I64(..)));
                Type::Builtin(BuiltinType::I64)
            }
            Expr::Float(n) => {
                debug_assert!(matches!(n, Float::F64(..)));
                Type::Builtin(BuiltinType::F64)
            }
            Expr::String(..) => Type::Builtin(BuiltinType::Str),
            Expr::Boolean(..) => Type::Builtin(BuiltinType::Bool),
            Expr::Call { callee, args, typ } => {
                let ret = match self.infer(callee.span, &mut callee.item).rhs {
                    Type::Fun(typ) => {
                        self.check_args(span, args.len(), args.iter_mut(), &typ.params);
                        typ.ret
                    }
                    got => {
                        self.type_mismatch_msg(span, &got, "function".to_string());
                        got
                    }
                };
                *typ = Some(Box::new(ret.to_expr(span)));
                ret
            }
            Expr::BinaryOp { lhs, op, typ, rhs } => match op {
                Symbol::EqEq => {
                    let got = self.infer(lhs.span, &mut lhs.item).rhs;
                    self.check(rhs.span, &mut rhs.item, &got);
                    *typ = Some(Box::new(got.to_expr(lhs.span)));
                    Type::Builtin(BuiltinType::Bool)
                }
                Symbol::Lt | Symbol::Gt | Symbol::Le | Symbol::Ge => {
                    self.check_number(lhs, rhs, typ);
                    Type::Builtin(BuiltinType::Bool)
                }
                Symbol::Plus | Symbol::Minus | Symbol::Mul => self.check_number(lhs, rhs, typ),
                _ => unreachable!(),
            },
            Expr::Object(..) => todo!(),
            Expr::Access(..) => todo!(),
            Expr::Method { .. } => todo!(),
        })
    }

    fn isa(&mut self, span: SimpleSpan, got: &Type, want: &Type) {
        match (got, want) {
            (Type::Builtin(a), Type::Builtin(b)) if a == b => (),
            (Type::Fun(a), Type::Fun(b)) if a.params.len() == b.params.len() => {
                a.params
                    .iter()
                    .zip(b.params.iter())
                    .for_each(|(a, b)| self.isa(span, a, b));
                self.isa(span, &a.ret, &b.ret)
            }
            (Type::Ref(a), Type::Ref(b)) => self.isa(span, a, b),
            (Type::Array { elem: a, len: None }, Type::Array { elem: b, len: None }) => {
                self.isa(span, a, b)
            }
            (
                Type::Array {
                    elem: a,
                    len: Some(x),
                },
                Type::Array {
                    elem: b,
                    len: Some(y),
                },
            ) => {
                self.isa(span, a, b);
                self.isa(span, x, y)
            }
            (Type::Ident(a), Type::Ident(b)) | (Type::Struct(a), Type::Struct(b)) if a == b => (),
            (Type::CType { from: a, to: x }, Type::CType { from: b, to: y }) if x == y => {
                self.isa(span, a, b)
            }
            _ => self.type_mismatch(span, got, want),
        }
    }

    fn type_mismatch(&mut self, span: SimpleSpan, got: &Type, want: &Type) {
        if matches!(want, Type::Unknown) {
            return;
        }
        self.type_mismatch_msg(span, got, want.to_string());
    }

    fn type_mismatch_msg(&mut self, span: SimpleSpan, got: &Type, want: String) {
        if matches!(got, Type::Unknown) {
            return;
        }
        let got = got.to_string();
        self.errs
            .push(Span::new(span, CheckErr::TypeMismatch { got, want }))
    }
}

pub(crate) struct Item<T> {
    pub(crate) name: Ident,
    pub(crate) constrs: Vec<(Ident, Type)>,
    pub(crate) mono: Vec<(Vec<Type>, Ident)>,
    pub(crate) item: T,
}

impl<T> Item<T> {
    pub(crate) fn mono_env(&self, types: &[Type]) -> impl Iterator<Item = (Ident, Type)> {
        self.constrs
            .iter()
            .map(|(name, ..)| *name)
            .zip(types.iter().cloned())
    }
}

pub(crate) struct FunItem {
    pub(crate) params: Vec<(Ident, Type)>,
    pub(crate) ret: Type,
    pub(crate) body: Vec<Span<Stmt>>,
}

#[allow(dead_code)]
pub(crate) struct StructItem {
    pub(crate) types: HashMap<Ident, Type>,
    pub(crate) data: HashMap<Ident, (Type, usize)>,
    pub(crate) optional: Option<(Ident, Type)>,
}

struct Block {
    ret: Type,
    olds: Vec<(Ident, Option<Type>)>,
}

impl Block {
    fn func(ret: Type) -> Self {
        Self {
            ret,
            olds: Default::default(),
        }
    }

    fn local(&self) -> Self {
        Self::func(self.ret.clone())
    }
}

#[derive(Default)]
struct Applier(HashMap<Ident, Type>);

impl Applier {
    fn apply(&mut self, t: &mut Type) {
        match t {
            Type::Unknown | Type::Builtin(..) | Type::Struct(..) => (),
            Type::Fun(f) => {
                f.params.iter_mut().for_each(|p| self.apply(p));
                self.apply(&mut f.ret);
            }
            Type::Ref(x) => self.apply(x),
            Type::Array { elem, len } => {
                self.apply(elem);
                if let Some(len) = len {
                    self.apply(len);
                }
            }
            Type::Generic { constr, ret, .. } => {
                self.apply(constr);
                self.apply(ret);
            }
            Type::Ident(id) => *t = self.0.get(id).cloned().unwrap(),
            Type::CType { from, .. } => self.apply(from),
        }
    }
}

impl Type {
    fn apply(&mut self, ident: Ident, typ: Self) {
        Applier(HashMap::from([(ident, typ)])).apply(self)
    }
}
