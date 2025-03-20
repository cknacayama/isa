use super::{
    ast::typed::{TypedExpr, TypedExprKind, TypedModule, TypedParam, TypedPat, TypedPatKind},
    ctx::TypeCtx,
    error::InferError,
    types::Ty,
};
use crate::span::{Span, Spanned};
use std::{fmt::Display, rc::Rc};

pub type InferResult<T> = Result<T, Spanned<InferError>>;

#[derive(Debug, Clone)]
pub struct Subs {
    old: Rc<Ty>,
    new: Rc<Ty>,
}

impl Subs {
    #[must_use]
    pub fn new(old: Rc<Ty>, new: Rc<Ty>) -> Self {
        Self { old, new }
    }
}

pub trait Substitute {
    fn substitute<S>(self, subs: &mut S, env: &mut TypeCtx) -> Self
    where
        S: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>;

    /// Used mainly for type inference and unification of constraint sets
    fn substitute_eq(self, subs: &Subs, env: &mut TypeCtx) -> Self
    where
        Self: Sized,
    {
        self.substitute(
            &mut move |t, _| {
                let t: *const Ty = t;
                let old: *const Ty = &*subs.old;
                if t == old {
                    Some(subs.new.clone())
                } else {
                    None
                }
            },
            env,
        )
    }

    fn substitute_many(self, subs: &[Subs], env: &mut TypeCtx) -> Self
    where
        Self: Sized,
    {
        subs.into_iter()
            .fold(self, |res, subs| res.substitute_eq(subs, env))
    }
}

impl Substitute for &mut TypedParam {
    fn substitute<S>(self, subs: &mut S, env: &mut TypeCtx) -> Self
    where
        S: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        self.ty = self.ty.clone().substitute(subs, env);
        self
    }
}

impl Substitute for &mut TypedExpr {
    fn substitute<S>(self, subs: &mut S, env: &mut TypeCtx) -> Self
    where
        S: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        match &mut self.kind {
            TypedExprKind::Let {
                params, expr, body, ..
            } => {
                params.iter_mut().for_each(|p| {
                    p.substitute(subs, env);
                });
                expr.substitute(subs, env);
                if let Some(body) = body.as_mut() {
                    body.substitute(subs, env);
                }
            }

            TypedExprKind::Fn { param, expr } => {
                param.substitute(subs, env);
                expr.substitute(subs, env);
            }

            TypedExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                cond.substitute(subs, env);
                then.substitute(subs, env);
                otherwise.substitute(subs, env);
            }

            TypedExprKind::Call { callee, arg } => {
                callee.substitute(subs, env);
                arg.substitute(subs, env);
            }

            TypedExprKind::Match { expr, arms } => {
                expr.substitute(subs, env);
                arms.iter_mut().for_each(|arm| {
                    arm.pat.substitute(subs, env);
                    arm.expr.substitute(subs, env);
                });
            }

            TypedExprKind::Semi(semi) => {
                semi.substitute(subs, env);
            }
            TypedExprKind::Type { constructors, .. } => {
                constructors.iter_mut().for_each(|c| {
                    c.params.iter_mut().for_each(|t| {
                        *t = t.clone().substitute(subs, env);
                    })
                });
            }

            TypedExprKind::Unit
            | TypedExprKind::Int(_)
            | TypedExprKind::Bool(_)
            | TypedExprKind::Ident(_)
            | TypedExprKind::BinOp(_)
            | TypedExprKind::UnOp(_) => (),
        }

        self.ty = self.ty.clone().substitute(subs, env);
        self
    }
}

impl Substitute for &mut TypedModule {
    fn substitute<S>(self, subs: &mut S, env: &mut TypeCtx) -> Self
    where
        S: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        self.exprs.iter_mut().for_each(|e| {
            e.substitute(subs, env);
        });
        self.declared.values_mut().for_each(|ty| {
            *ty = ty.clone().substitute(subs, env);
        });
        self
    }
}

impl Substitute for &mut TypedPat {
    fn substitute<S>(self, subs: &mut S, env: &mut TypeCtx) -> Self
    where
        S: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        match &mut self.kind {
            TypedPatKind::Or(args) | TypedPatKind::Type { args, .. } => {
                args.iter_mut().for_each(|p| {
                    p.substitute(subs, env);
                });
            }

            TypedPatKind::Wild
            | TypedPatKind::Unit
            | TypedPatKind::Int(_)
            | TypedPatKind::Bool(_)
            | TypedPatKind::Ident(_) => (),
        }
        self.ty = self.ty.clone().substitute(subs, env);
        self
    }
}

impl Substitute for Rc<Ty> {
    fn substitute<Subs>(self, subs: &mut Subs, env: &mut TypeCtx) -> Self
    where
        Subs: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        let ty = match self.as_ref() {
            Ty::Fn { param, ret } => {
                let ty = Ty::Fn {
                    param: param.clone().substitute(subs, env),
                    ret:   ret.clone().substitute(subs, env),
                };
                env.intern_type(ty)
            }
            Ty::Scheme { quant, ty } => {
                let ty = ty.clone().substitute(subs, env);
                let quant = quant.clone();
                let ty = Ty::Scheme { quant, ty };
                env.intern_type(ty)
            }
            Ty::Named { name, args } => {
                let ty = Ty::Named {
                    name: *name,
                    args: args
                        .into_iter()
                        .cloned()
                        .map(|arg| arg.substitute(subs, env))
                        .collect(),
                };
                env.intern_type(ty)
            }
            _ => self,
        };

        if let Some(new) = subs(ty.as_ref(), env) {
            new
        } else {
            ty
        }
    }
}

#[derive(Debug, Clone)]
pub struct Constr {
    lhs:  Rc<Ty>,
    rhs:  Rc<Ty>,
    span: Span,
}

impl Substitute for Constr {
    fn substitute<Subs>(self, subs: &mut Subs, env: &mut TypeCtx) -> Self
    where
        Subs: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        Self {
            lhs:  self.lhs.substitute(subs, env),
            rhs:  self.rhs.substitute(subs, env),
            span: self.span,
        }
    }
}

impl Constr {
    #[must_use]
    pub fn new(lhs: Rc<Ty>, rhs: Rc<Ty>, span: Span) -> Self {
        Self { lhs, rhs, span }
    }

    #[must_use]
    pub fn satisfied(&self) -> bool {
        self.lhs == self.rhs
    }

    #[must_use]
    pub fn lhs(&self) -> &Ty {
        &self.lhs
    }

    #[must_use]
    pub fn rhs(&self) -> &Ty {
        &self.rhs
    }
}

#[derive(Debug, Clone, Default)]
pub struct ConstrSet {
    constrs: Vec<Constr>,
}

impl Substitute for &mut ConstrSet {
    fn substitute<Subs>(self, subs: &mut Subs, env: &mut TypeCtx) -> Self
    where
        Subs: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        for c in &mut self.constrs {
            *c = c.clone().substitute(subs, env);
        }
        self
    }
}

impl ConstrSet {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn append(&mut self, mut other: Self) {
        self.constrs.append(&mut other.constrs);
    }

    pub fn len(&self) -> usize {
        self.constrs.len()
    }

    pub fn push(&mut self, c: Constr) {
        self.constrs.push(c);
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constr> {
        self.constrs.iter()
    }

    pub fn unify(&mut self, env: &mut TypeCtx) -> InferResult<Vec<Subs>> {
        let mut subs = Vec::new();

        while let Some(c) = self.constrs.pop() {
            let span = c.span;
            match (c.lhs.as_ref(), c.rhs.as_ref()) {
                (
                    lhs @ (Ty::Int | Ty::Bool | Ty::Var(_)),
                    rhs @ (Ty::Int | Ty::Bool | Ty::Var(_)),
                ) if lhs == rhs => {}
                (Ty::Var(var), new) | (new, Ty::Var(var)) if !new.occurs(*var) => {
                    let new = env.intern_type(new.clone());
                    let old = env.intern_type(Ty::Var(*var));

                    let s = Subs { old, new };

                    self.substitute_eq(&s, env);

                    subs.push(s);
                }
                (Ty::Fn { param: i1, ret: o1 }, Ty::Fn { param: i2, ret: o2 }) => {
                    let c1 = Constr::new(i1.clone(), i2.clone(), span);
                    let c2 = Constr::new(o1.clone(), o2.clone(), span);

                    self.push(c1);
                    self.push(c2);
                }
                (
                    Ty::Named {
                        name: n1,
                        args: args1,
                    },
                    Ty::Named {
                        name: n2,
                        args: args2,
                    },
                ) if n1 == n2 && args1.len() == args2.len() => {
                    for (a1, a2) in args1.iter().zip(args2) {
                        let c = Constr::new(a1.clone(), a2.clone(), span);
                        self.push(c);
                    }
                }
                _ => return Err(Spanned::new(InferError::Uninferable(c), span)),
            }
        }

        Ok(subs)
    }
}

impl Display for Subs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{} |-> ({})", self.old, self.new)
    }
}

impl Display for Constr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

impl Display for ConstrSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.constrs.iter().try_for_each(|c| write!(f, "{c}, "))
    }
}
