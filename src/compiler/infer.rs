use std::fmt::Display;
use std::rc::Rc;

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
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>;

    /// Used mainly for type inference and unification of constraint sets
    fn substitute_eq(&mut self, subs: &Subs)
    where
        Self: Sized,
    {
        self.substitute(&mut |t| match t {
            Ty::Var(id) if *id == subs.old => Some(subs.new.clone()),
            _ => None,
        });
    }

    fn substitute_many<'a, T>(&mut self, subs: T)
    where
        Self: Sized,
        T: IntoIterator<Item = &'a Subs>,
    {
        for s in subs {
            self.substitute_eq(s);
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ConstraintSpan {
    pub sub_exprs: Option<(Option<Span>, Span)>,
    pub expr:      Span,
}

impl ConstraintSpan {
    #[must_use]
    pub const fn new(sub_exprs: Option<(Option<Span>, Span)>, expr: Span) -> Self {
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
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.lhs.substitute(subs);
        self.rhs.substitute(subs);
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
    pub const fn lhs(&self) -> &Ty {
        &self.lhs
    }

    #[must_use]
    pub const fn rhs(&self) -> &Ty {
        &self.rhs
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

impl Substitute for ConstraintSet {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        for c in &mut self.constrs {
            c.substitute(subs);
        }
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
                    let mut parent = parent.as_ref().clone();
                    parent.substitute_many(&subs);
                    parent
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

    pub fn push(&mut self, c: Constraint) {
        self.constrs.push(c);
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
