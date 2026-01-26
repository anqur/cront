use crate::syntax::parse::{
    Branch, Builtin, Constr, Def, Doc, Expr, File, Fun, Ident, Idents, Member, Param, Sig, Stmt,
};
use crate::{Error, Result};
use crate::{ResolveErr, Span};
use chumsky::prelude::SimpleSpan;
use ustr::{Ustr, UstrMap, UstrSet};

pub fn resolve(file: &mut File) -> Result<()> {
    Resolver::default().file(file)
}

#[derive(Default)]
struct Resolver {
    idents: Idents,
    globals: UstrMap<u64>,
    constrs: UstrMap<u64>,
    locals: UstrMap<u64>,
    errs: Vec<Span<ResolveErr>>,
}

impl Resolver {
    fn file(mut self, file: &mut File) -> Result<()> {
        {
            let mut names = UstrSet::default();
            file.decls.iter_mut().for_each(|decl| {
                let name = match &mut decl.inner_mut().sig {
                    Sig::Fun(fun) => {
                        self.fun(fun);
                        Some(fun.name.clone())
                    }
                    Sig::Typ { name, constrs, typ } => {
                        self.fresh(name);
                        self.constrs(constrs);
                        self.with_constrs(constrs, |s| s.expr(typ.span, &mut typ.item));
                        Some(name.clone())
                    }
                    Sig::Struct {
                        name,
                        constrs,
                        members,
                        optional,
                    } => {
                        self.fresh(name);
                        self.constrs(constrs);
                        self.with_constrs(constrs, |s| {
                            members.iter_mut().for_each(|m| {
                                let mut names = UstrSet::default();
                                let m = m.inner_mut();
                                let name = match m {
                                    Member::Data(p) => {
                                        s.param(p);
                                        &p.name
                                    }
                                    Member::Type(c) => {
                                        s.constr(c);
                                        &c.typ
                                    }
                                };
                                s.check_duplicate_name(&mut names, name);
                            });
                            if let Some(optional) = optional {
                                s.param(optional.inner_mut())
                            }
                        });
                        Some(name.clone())
                    }
                };
                let Some(name) = name else { return };
                if self.check_duplicate_name(&mut names, &name) {
                    self.globals.insert(name.item.text, name.item.id);
                }
            });
        }
        file.decls.iter_mut().for_each(|decl| {
            let decl = decl.inner_mut();
            match &mut decl.def {
                Def::Fun(body) => {
                    let Sig::Fun(fun) = &mut decl.sig else {
                        unreachable!()
                    };
                    self.with_constrs(&fun.constrs, |s| {
                        let mut block = Block::default();
                        fun.params
                            .iter()
                            .for_each(|p| s.local(&mut block, &p.inner().name));
                        s.block(block, body);
                    })
                }
                Def::Typ | Def::Struct => (),
            }
        });

        file.main = {
            let raw = Ustr::from("main");
            self.globals.get(&raw).cloned().map(|id| {
                let mut i = Ident::unbound(raw);
                i.fresh(id);
                i
            })
        };
        file.idents = self.idents;

        if self.errs.is_empty() {
            Ok(())
        } else {
            Err(Error::Resolve(self.errs))
        }
    }

    fn fun(&mut self, fun: &mut Fun) {
        if let Some(binder) = &mut fun.binder {
            self.name(binder.span, &mut binder.item);
        }
        self.fresh(&mut fun.name);
        self.constrs(&mut fun.constrs);
        self.with_constrs(&fun.constrs, |s| {
            fun.params.iter_mut().for_each(|p| s.param(p.inner_mut()));
            if let Some(ret) = &mut fun.ret {
                s.expr(ret.span, &mut ret.item)
            }
        });
    }

    fn param(&mut self, p: &mut Param) {
        self.fresh(&mut p.name);
        self.expr(p.typ.span, &mut p.typ.item)
    }

    fn constrs(&mut self, cs: &mut [Span<Doc<Constr>>]) {
        cs.iter_mut().for_each(|p| self.constr(p.inner_mut()))
    }

    fn constr(&mut self, c: &mut Constr) {
        self.fresh(&mut c.typ);
        self.expr(c.constr.span, &mut c.constr.item);
        if let Some(default) = &mut c.default {
            self.expr(default.span, &mut default.item);
        }
    }

    fn with_constrs<R, F: FnOnce(&mut Self) -> R>(&mut self, cs: &[Span<Doc<Constr>>], f: F) -> R {
        let olds = cs
            .iter()
            .map(|p| {
                let typ = p.inner().typ.item;
                self.constrs.insert(typ.text, typ.id)
            })
            .collect::<Vec<_>>();
        let ret = f(self);
        cs.iter().zip(olds).for_each(|(p, old)| {
            let raw = p.inner().typ.item.text;
            match old {
                None => self.constrs.remove(&raw),
                Some(old) => self.constrs.insert(raw, old),
            };
        });
        ret
    }

    fn check_duplicate_name(&mut self, names: &mut UstrSet, name: &Span<Ident>) -> bool {
        let inserted = names.insert(name.item.text);
        if !inserted {
            self.errs.push(Span::new(
                name.span,
                ResolveErr::DuplicateName(name.item.text),
            ));
        }
        inserted
    }

    fn name(&mut self, span: SimpleSpan, name: &mut Ident) {
        let raw = name.text;
        match self
            .locals
            .get(&raw)
            .cloned()
            .or_else(|| self.constrs.get(&raw).cloned())
            .or_else(|| self.globals.get(&raw).cloned())
            .or_else(|| Builtin::from_raw(&raw))
        {
            Some(found) => name.id = found,
            None => self.errs.push(Span::new(span, ResolveErr::UndefName(raw))),
        }
    }

    fn fresh(&mut self, raw: &mut Span<Ident>) {
        self.idents.fresh(&mut raw.item);
    }

    fn block(&mut self, mut block: Block, stmts: &mut [Span<Stmt>]) {
        stmts
            .iter_mut()
            .for_each(|stmt| self.stmt(&mut block, stmt));
        for (raw, old) in block.locals {
            match old {
                None => self.locals.remove(&raw),
                Some(old) => self.locals.insert(raw, old),
            };
        }
    }

    fn local(&mut self, block: &mut Block, raw: &Span<Ident>) {
        let text = raw.item.text;
        block
            .locals
            .push((text, self.locals.insert(text, raw.item.id)));
    }

    fn stmt(&mut self, block: &mut Block, stmt: &mut Span<Stmt>) {
        match &mut stmt.item {
            Stmt::Expr(e) => self.expr(stmt.span, e),
            Stmt::Assign { name, typ, rhs } => {
                self.fresh(name);
                if let Some(typ) = typ {
                    self.expr(typ.span, &mut typ.item);
                }
                self.expr(rhs.span, &mut rhs.item);
                self.local(block, name);
            }
            Stmt::Update { name, rhs } => {
                self.name(name.span, &mut name.item);
                self.expr(rhs.span, &mut rhs.item);
            }
            Stmt::Return(e) => {
                if let Some(e) = e {
                    self.expr(e.span, &mut e.item);
                }
            }
            Stmt::If { then, elif, els } => {
                self.branch(&mut then.item);
                elif.iter_mut().for_each(|b| self.branch(&mut b.item));
                if let Some(els) = els {
                    self.block(Block::default(), &mut els.item);
                }
            }
            Stmt::While { branch, .. } => self.branch(branch),
            Stmt::Break | Stmt::Continue => (),
            Stmt::Decl { .. } => unreachable!(),
        }
    }

    fn branch(&mut self, branch: &mut Branch) {
        self.expr(branch.cond.span, &mut branch.cond.item);
        self.block(Block::default(), &mut branch.body)
    }

    fn expr(&mut self, span: SimpleSpan, expr: &mut Expr) {
        match expr {
            Expr::Ident(name) => self.name(span, name),
            Expr::Apply(callee, args) | Expr::Call { callee, args, .. } => {
                self.expr(callee.span, &mut callee.item);
                args.iter_mut().for_each(|x| self.expr(x.span, &mut x.item));
            }
            Expr::RefType(t) => self.expr(t.span, &mut t.item),
            Expr::ArrayType { elem, len } => {
                self.expr(elem.span, &mut elem.item);
                if let Some(len) = len {
                    self.expr(len.span, &mut len.item);
                }
            }
            Expr::BinaryOp { lhs, rhs, .. } => {
                self.expr(lhs.span, &mut lhs.item);
                self.expr(rhs.span, &mut rhs.item);
            }
            Expr::Object(a, o) => {
                self.expr(a.span, &mut a.item);
                o.iter_mut()
                    .for_each(|(.., e)| self.expr(e.span, &mut e.item));
            }
            Expr::Access(e, ..) => self.expr(e.span, &mut e.item),
            Expr::Method { callee, args, .. } => {
                self.expr(callee.span, &mut callee.item);
                args.iter_mut().for_each(|e| self.expr(e.span, &mut e.item))
            }

            Expr::BuiltinType(..)
            | Expr::Integer(..)
            | Expr::Float(..)
            | Expr::String(..)
            | Expr::Boolean(..) => (),
        }
    }
}

#[derive(Default)]
struct Block {
    locals: Vec<(Ustr, Option<u64>)>,
}
