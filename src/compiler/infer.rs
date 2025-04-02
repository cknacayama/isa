use std::fmt::Display;
use std::rc::Rc;

use super::error::Uninferable;
use super::types::Ty;
use crate::span::Span;

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

#[derive(Debug, Clone)]
pub struct Constraint {
    lhs:    Ty,
    rhs:    Ty,
    span:   Span,
    parent: Option<Rc<Constraint>>,
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
    pub const fn new(lhs: Ty, rhs: Ty, span: Span) -> Self {
        Self {
            lhs,
            rhs,
            span,
            parent: None,
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

    pub const fn span(&self) -> Span {
        self.span
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

pub fn unify<C>(cset: C) -> Result<Vec<Subs>, Uninferable>
where
    ConstraintSet: From<C>,
{
    let mut cset = ConstraintSet::from(cset);
    let mut subs = Vec::new();

    while let Some(c) = cset.constrs.pop() {
        let span = c.span;
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
                let c1 = Constraint::new(i1.as_ref().clone(), i2.as_ref().clone(), c.span);
                let c2 = Constraint::new(o1.as_ref().clone(), o2.as_ref().clone(), c.span);
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
                        Constraint::new(a1.clone(), a2.clone(), span).with_parent(parent.clone()),
                    );
                }
            }
            (Ty::Scheme { quant: q1, ty: t1 }, Ty::Scheme { quant: q2, ty: t2 })
                if q1.len() == q2.len() =>
            {
                let constr = Constraint::new(t1.as_ref().clone(), t2.as_ref().clone(), span);
                let parent = Rc::new(c);
                cset.push(constr.with_parent(parent));
            }

            _ => {
                let c = if let Some(parent) = c.parent {
                    let mut parent = parent.as_ref().clone();
                    parent.substitute_many(&subs);
                    parent
                } else {
                    c
                };
                return Err(Uninferable::new(c, subs));
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
