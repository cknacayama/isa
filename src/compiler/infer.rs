#![allow(
    clippy::return_self_not_must_use,
    reason = "Substitute trait is implemented on some &mut ref"
)]

use std::fmt::Display;
use std::rc::Rc;

use super::ast::typed::{
    TypedExpr, TypedExprKind, TypedModule, TypedParam, TypedPat, TypedPatKind,
};
use super::ctx::TypeCtx;
use super::error::InferError;
use super::types::Ty;
use crate::span::{Span, Spanned};

pub type InferResult<T> = Result<T, Spanned<InferError>>;

#[derive(Debug, Clone)]
pub struct Subs {
    old: u64,
    new: Rc<Ty>,
}

impl Subs {
    #[must_use]
    pub const fn new(old: u64, new: Rc<Ty>) -> Self {
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
            &mut |t, _| match t {
                Ty::Var(id) if *id == subs.old => Some(subs.new.clone()),
                _ => None,
            },
            env,
        )
    }

    fn substitute_many(self, subs: &[Subs], env: &mut TypeCtx) -> Self
    where
        Self: Sized,
    {
        subs.iter()
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
                    });
                });
            }
            TypedExprKind::Bin { lhs, rhs, .. } => {
                lhs.substitute(subs, env);
                rhs.substitute(subs, env);
            }
            TypedExprKind::Un { expr, .. } => {
                expr.substitute(subs, env);
            }

            TypedExprKind::Unit
            | TypedExprKind::Int(_)
            | TypedExprKind::Bool(_)
            | TypedExprKind::Ident(_) => (),
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
        Subs: FnMut(&Ty, &mut TypeCtx) -> Option<Self>,
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
                        .iter()
                        .cloned()
                        .map(|arg| arg.substitute(subs, env))
                        .collect(),
                };
                env.intern_type(ty)
            }
            _ => self,
        };

        subs(ty.as_ref(), env).unwrap_or(ty)
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
    pub const fn new(lhs: Rc<Ty>, rhs: Rc<Ty>, span: Span) -> Self {
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

impl<T> From<T> for ConstrSet
where
    Vec<Constr>: From<T>,
{
    fn from(value: T) -> Self {
        Self {
            constrs: Vec::from(value),
        }
    }
}

impl From<Constr> for ConstrSet {
    fn from(value: Constr) -> Self {
        Self {
            constrs: vec![value],
        }
    }
}

pub fn unify<C>(cset: C, type_ctx: &mut TypeCtx) -> InferResult<Vec<Subs>>
where
    ConstrSet: From<C>,
{
    let mut cset = ConstrSet::from(cset);
    let mut subs = Vec::new();

    while let Some(c) = cset.constrs.pop() {
        let span = c.span;
        match (c.lhs.as_ref(), c.rhs.as_ref()) {
            (lhs @ (Ty::Int | Ty::Bool | Ty::Var(_)), rhs @ (Ty::Int | Ty::Bool | Ty::Var(_)))
                if lhs == rhs => {}
            (Ty::Var(var), new) | (new, Ty::Var(var)) if !new.occurs(*var) => {
                let old = *var;
                let new = type_ctx.intern_type(new.clone());

                let s = Subs { old, new };

                cset.substitute_eq(&s, type_ctx);

                subs.push(s);
            }
            (Ty::Fn { param: i1, ret: o1 }, Ty::Fn { param: i2, ret: o2 }) => {
                let c1 = Constr::new(i1.clone(), i2.clone(), span);
                let c2 = Constr::new(o1.clone(), o2.clone(), span);

                cset.push(c1);
                cset.push(c2);
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
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    cset.push(Constr::new(a1.clone(), a2.clone(), span));
                }
            }
            _ => return Err(Spanned::new(InferError::Uninferable(c), span)),
        }
    }

    Ok(subs)
}

impl ConstrSet {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn append(&mut self, mut other: Self) {
        self.constrs.append(&mut other.constrs);
    }

    pub fn push(&mut self, c: Constr) {
        self.constrs.push(c);
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constr> {
        self.constrs.iter()
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
