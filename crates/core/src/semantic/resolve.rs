use crate::syntax::parse::{Branch, Constr, Def, Doc, Expr, File, Fun, Ident, Sig, Stmt};
use crate::{Error, Result};
use crate::{ResolveErr, Span};
use chumsky::prelude::SimpleSpan;
use ustr::{Ustr, UstrMap, UstrSet};

pub fn resolve(file: &mut File) -> Result<()> {
    Resolver::default().file(file)
}

#[derive(Default)]
struct Resolver {
    next_id: u64,
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
                    Sig::Typ { name, constrs } => {
                        self.fresh(name);
                        self.constrs(constrs);
                        Some(name.clone())
                    }
                    Sig::Struct { .. } => todo!(),
                };
                let Some(name) = name else { return };
                if !names.insert(name.item.text) {
                    return self.duplicate_name(name);
                }
                self.globals.insert(name.item.text, name.item.id);
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
                Def::Typ(t) => {
                    let Sig::Typ { constrs, .. } = &mut decl.sig else {
                        unreachable!()
                    };
                    self.with_constrs(constrs, |s| s.expr(t.span, &mut t.item));
                }
                Def::Struct => (),
            }
        });
        if self.errs.is_empty() {
            Ok(())
        } else {
            Err(Error::Resolve(self.errs))
        }
    }

    fn fun(&mut self, fun: &mut Fun) {
        self.fresh(&mut fun.name);
        self.constrs(&mut fun.constrs);
        self.with_constrs(&fun.constrs, |s| {
            fun.params.iter_mut().for_each(|p| {
                let p = p.inner_mut();
                s.fresh(&mut p.name);
                s.expr(p.typ.span, &mut p.typ.item)
            });
            if let Some(ret) = &mut fun.ret {
                s.expr(ret.span, &mut ret.item)
            }
        });
    }

    fn constrs(&mut self, cs: &mut [Span<Doc<Constr>>]) {
        cs.iter_mut().for_each(|p| {
            let c = p.inner_mut();
            self.fresh(&mut c.typ);
            self.expr(c.constr.span, &mut c.constr.item);
            if let Some(default) = &mut c.default {
                self.expr(default.span, &mut default.item);
            }
        })
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

    fn duplicate_name(&mut self, name: Span<Ident>) {
        self.errs
            .push(name.map(|n| ResolveErr::DuplicateName(n.text)))
    }

    fn name(&mut self, span: SimpleSpan, name: &mut Ident) {
        let raw = name.text;
        match self
            .locals
            .get(&raw)
            .or_else(|| self.constrs.get(&raw))
            .or_else(|| self.globals.get(&raw))
            .cloned()
        {
            Some(found) => name.id = found,
            None => self.errs.push(Span {
                span,
                item: ResolveErr::UndefName(raw),
            }),
        }
    }

    fn fresh(&mut self, raw: &mut Span<Ident>) {
        self.next_id += 1;
        raw.item.fresh(self.next_id);
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
            Stmt::While(b) => self.branch(b),
            Stmt::Break => (),
            Stmt::Continue => (),
        }
    }

    fn branch(&mut self, branch: &mut Branch) {
        self.expr(branch.cond.span, &mut branch.cond.item);
        self.block(Block::default(), &mut branch.body)
    }

    fn expr(&mut self, span: SimpleSpan, expr: &mut Expr) {
        match expr {
            Expr::Ident(name) => self.name(span, name),
            Expr::BuiltinType(..) => (),
            Expr::Apply(f, xs) | Expr::Call(f, xs) => {
                self.expr(f.span, &mut f.item);
                xs.iter_mut().for_each(|x| self.expr(x.span, &mut x.item));
            }
            Expr::RefType(t) => self.expr(t.span, &mut t.item),
            Expr::ArrayType { elem, len } => {
                self.expr(elem.span, &mut elem.item);
                if let Some(len) = len {
                    self.expr(len.span, &mut len.item);
                }
            }
            Expr::Integer(..) => (),
            Expr::Float(..) => (),
            Expr::String(..) => (),
            Expr::Boolean(..) => (),
            Expr::BinaryOp(a, .., b) => {
                self.expr(a.span, &mut a.item);
                self.expr(b.span, &mut b.item);
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
        }
    }
}

#[derive(Default)]
struct Block {
    locals: Vec<(Ustr, Option<u64>)>,
}
