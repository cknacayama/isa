#![allow(
    clippy::return_self_not_must_use,
    reason = "Substitute trait is implemented on some &mut ref"
)]

use std::fmt::Display;
use std::rc::Rc;

use super::ast::Constructor;
use super::ast::typed::{
    TypedExpr, TypedExprKind, TypedModule, TypedParam, TypedPat, TypedPatKind,
};
use super::ast::untyped::{UntypedExpr, UntypedExprKind};
use super::error::{InferError, InferErrorKind};
use super::types::Ty;
use crate::span::Span;

pub type InferResult<T> = Result<T, InferError>;

#[derive(Debug, Clone)]
pub struct Subs {
    old: u64,
    new: Ty,
}

impl Subs {
    #[must_use]
    pub const fn new(old: u64, new: Ty) -> Self {
        Self { old, new }
    }
}

pub trait Substitute {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>;

    /// Used mainly for type inference and unification of constraint sets
    fn substitute_eq(self, subs: &Subs) -> Self
    where
        Self: Sized,
    {
        self.substitute(&mut |t| match t {
            Ty::Var(id) if *id == subs.old => Some(subs.new.clone()),
            _ => None,
        })
    }

    fn substitute_many<'a, T>(self, subs: T) -> Self
    where
        Self: Sized,
        T: IntoIterator<Item = &'a Subs>,
    {
        subs.into_iter().fold(self, Self::substitute_eq)
    }
}

impl Substitute for &mut TypedParam {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.ty = self.ty.clone().substitute(subs);
        self
    }
}

impl Substitute for &mut Constructor {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.params
            .iter_mut()
            .for_each(|param| *param = param.clone().substitute(subs));
        self
    }
}

impl Substitute for &mut UntypedExpr {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match &mut self.kind {
            UntypedExprKind::Semi(semi) => {
                semi.substitute(subs);
            }
            UntypedExprKind::Type { constructors, .. } => {
                constructors.iter_mut().for_each(|c| {
                    c.params.iter_mut().for_each(|t| {
                        *t = t.clone().substitute(subs);
                    });
                });
            }
            UntypedExprKind::Val { ty, .. } => {
                *ty = ty.clone().substitute(subs);
            }
            _ => (),
        }

        self
    }
}

impl Substitute for &mut TypedExpr {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match &mut self.kind {
            TypedExprKind::Let {
                params, expr, body, ..
            } => {
                params.iter_mut().for_each(|p| {
                    p.substitute(subs);
                });
                expr.substitute(subs);
                if let Some(body) = body.as_mut() {
                    body.substitute(subs);
                }
            }
            TypedExprKind::Fn { param, expr } => {
                param.substitute(subs);
                expr.substitute(subs);
            }
            TypedExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                cond.substitute(subs);
                then.substitute(subs);
                otherwise.substitute(subs);
            }
            TypedExprKind::Call { callee, arg } => {
                callee.substitute(subs);
                arg.substitute(subs);
            }
            TypedExprKind::Match { expr, arms } => {
                expr.substitute(subs);
                arms.iter_mut().for_each(|arm| {
                    arm.pat.substitute(subs);
                    arm.expr.substitute(subs);
                });
            }
            TypedExprKind::Semi(semi) => {
                semi.substitute(subs);
            }
            TypedExprKind::Type { constructors, .. } => {
                constructors.iter_mut().for_each(|c| {
                    c.params.iter_mut().for_each(|t| {
                        *t = t.clone().substitute(subs);
                    });
                });
            }
            TypedExprKind::Val { ty, .. } => {
                *ty = ty.clone().substitute(subs);
            }
            TypedExprKind::Bin { lhs, rhs, .. } => {
                lhs.substitute(subs);
                rhs.substitute(subs);
            }
            TypedExprKind::Un { expr, .. } => {
                expr.substitute(subs);
            }

            TypedExprKind::Unit
            | TypedExprKind::Int(_)
            | TypedExprKind::Bool(_)
            | TypedExprKind::Ident(_)
            | TypedExprKind::Acess(_) => (),
        }

        self.ty = self.ty.clone().substitute(subs);
        self
    }
}

impl Substitute for &mut TypedModule {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.exprs.iter_mut().for_each(|e| {
            e.substitute(subs);
        });
        self.declared.values_mut().for_each(|var| {
            *var.ty_mut() = var.ty().clone().substitute(subs);
        });
        self
    }
}

impl Substitute for &mut TypedPat {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match &mut self.kind {
            TypedPatKind::Or(args) | TypedPatKind::Constructor { args, .. } => {
                args.iter_mut().for_each(|p| {
                    p.substitute(subs);
                });
            }

            TypedPatKind::Wild
            | TypedPatKind::Unit
            | TypedPatKind::Int(_)
            | TypedPatKind::Bool(_)
            | TypedPatKind::Ident(_)
            | TypedPatKind::Module(_)
            | TypedPatKind::IntRange(_) => (),
        }
        self.ty = self.ty.clone().substitute(subs);
        self
    }
}

impl Substitute for Ty {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Self) -> Option<Self>,
    {
        let ty = match self {
            Self::Fn { param, ret } => Self::Fn {
                param: param.substitute(subs),
                ret:   ret.substitute(subs),
            },
            Self::Scheme { quant, ty } => {
                let ty = ty.substitute(subs);
                Self::Scheme { quant, ty }
            }
            Self::Named { name, args } => Self::Named {
                name,
                args: args
                    .iter()
                    .cloned()
                    .map(|arg| arg.substitute(subs))
                    .collect(),
            },
            _ => self,
        };

        subs(&ty).unwrap_or(ty)
    }
}

impl Substitute for Rc<Ty> {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        let ty = match self.as_ref() {
            Ty::Fn { param, ret } => {
                let ty = Ty::Fn {
                    param: param.clone().substitute(subs),
                    ret:   ret.clone().substitute(subs),
                };
                Self::new(ty)
            }
            Ty::Scheme { quant, ty } => {
                let ty = ty.clone().substitute(subs);
                let quant = quant.clone();
                let ty = Ty::Scheme { quant, ty };
                Self::new(ty)
            }
            Ty::Named { name, args } => {
                let ty = Ty::Named {
                    name: *name,
                    args: args
                        .iter()
                        .cloned()
                        .map(|arg| arg.substitute(subs))
                        .collect(),
                };
                Self::new(ty)
            }
            _ => self,
        };

        subs(ty.as_ref()).map(Self::new).unwrap_or(ty)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ConstraintSpan {
    pub sub_exprs: Option<(Option<Span>, Span)>,
    pub expr:      Span,
}

impl ConstraintSpan {
    #[must_use]
    pub fn new(sub_exprs: Option<(Option<Span>, Span)>, expr: Span) -> Self {
        Self { sub_exprs, expr }
    }
}

impl From<Span> for ConstraintSpan {
    fn from(value: Span) -> Self {
        Self::new(None, value)
    }
}

impl From<[Span; 2]> for ConstraintSpan {
    fn from(value: [Span; 2]) -> Self {
        Self::new(Some((None, value[0])), value[1])
    }
}

impl From<[Span; 3]> for ConstraintSpan {
    fn from(value: [Span; 3]) -> Self {
        Self::new(Some((Some(value[0]), value[1])), value[2])
    }
}

impl From<ConstraintSpan> for Vec<Span> {
    fn from(value: ConstraintSpan) -> Self {
        match value.sub_exprs {
            None => vec![value.expr],
            Some((None, rhs)) => vec![rhs, value.expr],
            Some((Some(lhs), rhs)) => vec![lhs, rhs, value.expr],
        }
    }
}

#[derive(Debug, Clone)]
pub struct Constraint {
    lhs:       Ty,
    rhs:       Ty,
    parent:    Option<Rc<Constraint>>,
    pub spans: ConstraintSpan,
}

impl Substitute for Constraint {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        Self {
            lhs:    self.lhs.substitute(subs),
            rhs:    self.rhs.substitute(subs),
            parent: self.parent,
            spans:  self.spans,
        }
    }
}

impl Constraint {
    #[must_use]
    pub fn new<T>(lhs: Ty, rhs: Ty, spans: T) -> Self
    where
        ConstraintSpan: From<T>,
    {
        Self {
            lhs,
            rhs,
            parent: None,
            spans: ConstraintSpan::from(spans),
        }
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

    pub fn parent(&self) -> Option<&Self> {
        self.parent.as_ref().map(Rc::as_ref)
    }

    fn with_parent(self, parent: Rc<Self>) -> Self {
        Self {
            parent: Some(Self::eldest(parent)),
            ..self
        }
    }

    fn eldest(mut parent: Rc<Self>) -> Rc<Self> {
        while let Some(ref grand) = parent.parent {
            parent = grand.clone();
        }
        parent
    }
}

#[derive(Debug, Clone, Default)]
pub struct ConstraintSet {
    constrs: Vec<Constraint>,
}

impl Substitute for &mut ConstraintSet {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        for c in &mut self.constrs {
            *c = c.clone().substitute(subs);
        }
        self
    }
}

impl<T> From<T> for ConstraintSet
where
    Vec<Constraint>: From<T>,
{
    fn from(value: T) -> Self {
        Self {
            constrs: Vec::from(value),
        }
    }
}

impl From<Constraint> for ConstraintSet {
    fn from(value: Constraint) -> Self {
        Self {
            constrs: vec![value],
        }
    }
}

pub fn unify<C>(cset: C) -> InferResult<Vec<Subs>>
where
    ConstraintSet: From<C>,
{
    let mut cset = ConstraintSet::from(cset);
    let mut subs = Vec::new();

    while let Some(c) = cset.constrs.pop() {
        let spans = c.spans;
        match (&c.lhs, &c.rhs) {
            (lhs @ (Ty::Int | Ty::Bool | Ty::Var(_)), rhs @ (Ty::Int | Ty::Bool | Ty::Var(_)))
                if lhs == rhs => {}
            (Ty::Var(old), new) | (new, Ty::Var(old)) if !new.occurs(*old) => {
                let s = Subs {
                    old: *old,
                    new: new.clone(),
                };

                cset.substitute_eq(&s);

                subs.push(s);
            }
            (Ty::Fn { param: i1, ret: o1 }, Ty::Fn { param: i2, ret: o2 }) => {
                let c1 = Constraint::new(i1.as_ref().clone(), i2.as_ref().clone(), spans);
                let c2 = Constraint::new(o1.as_ref().clone(), o2.as_ref().clone(), spans);
                let parent = Rc::new(c);

                cset.push(c1.with_parent(parent.clone()));
                cset.push(c2.with_parent(parent));
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
                let args1 = args1.clone();
                let args2 = args2.clone();
                let parent = Rc::new(c);
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    cset.push(
                        Constraint::new(a1.clone(), a2.clone(), spans).with_parent(parent.clone()),
                    );
                }
            }
            _ => {
                let c = if let Some(parent) = c.parent {
                    parent.as_ref().clone().substitute_many(&subs)
                } else {
                    c
                };
                return Err(InferError::new(InferErrorKind::Uninferable(c), spans.expr));
            }
        }
    }

    Ok(subs)
}

impl ConstraintSet {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn append(&mut self, mut other: Self) {
        self.constrs.append(&mut other.constrs);
    }

    pub fn push(&mut self, c: Constraint) {
        self.constrs.push(c);
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constraint> {
        self.constrs.iter()
    }
}

impl Display for Subs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{} |-> ({})", self.old, self.new)
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

impl Display for ConstraintSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.constrs.iter().try_for_each(|c| write!(f, "{c}, "))
    }
}
