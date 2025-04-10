use std::collections::VecDeque;
use std::fmt::Display;
use std::rc::Rc;

use super::error::Uninferable;
use super::types::Ty;
use crate::global::Symbol;
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

    #[must_use]
    pub const fn old(&self) -> u64 {
        self.old
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

    fn substitute_param(&mut self, subs: &[(Symbol, u64)])
    where
        Self: Sized,
    {
        self.substitute(&mut |ty| {
            ty.get_name().and_then(|name| {
                subs.iter()
                    .find_map(|(s, v)| if *s == name { Some(Ty::Var(*v)) } else { None })
            })
        });
    }
}

#[derive(Debug, Clone)]
pub struct EqConstraint {
    lhs:    Ty,
    rhs:    Ty,
    span:   Span,
    parent: Option<Rc<EqConstraint>>,
}

impl Substitute for EqConstraint {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.lhs.substitute(subs);
        self.rhs.substitute(subs);
    }
}

impl EqConstraint {
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
pub struct EqConstraintSet {
    constrs: VecDeque<EqConstraint>,
}

impl Substitute for EqConstraintSet {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        for c in &mut self.constrs {
            c.substitute(subs);
        }
    }
}

impl<T> From<T> for EqConstraintSet
where
    VecDeque<EqConstraint>: From<T>,
{
    fn from(value: T) -> Self {
        Self {
            constrs: VecDeque::from(value),
        }
    }
}

impl From<EqConstraint> for EqConstraintSet {
    fn from(value: EqConstraint) -> Self {
        Self {
            constrs: VecDeque::from([value]),
        }
    }
}

pub fn unify<C>(cset: C) -> Result<Vec<Subs>, Uninferable>
where
    EqConstraintSet: From<C>,
{
    let mut cset = EqConstraintSet::from(cset);
    let mut subs = Vec::new();

    while let Some(c) = cset.constrs.pop_front() {
        let span = c.span;
        match (&c.lhs, &c.rhs) {
            (
                lhs @ (Ty::Int | Ty::Bool | Ty::Unit | Ty::Var(_)),
                rhs @ (Ty::Int | Ty::Bool | Ty::Unit | Ty::Var(_)),
            ) if lhs == rhs => {}
            (new, Ty::Var(old)) | (Ty::Var(old), new) if !new.occurs(*old) => {
                let s = Subs {
                    old: *old,
                    new: new.clone(),
                };

                cset.substitute_eq(&s);

                subs.push(s);
            }
            (Ty::Fn { param: i1, ret: o1 }, Ty::Fn { param: i2, ret: o2 }) => {
                let c1 = EqConstraint::new(i1.as_ref().clone(), i2.as_ref().clone(), c.span);
                let c2 = EqConstraint::new(o1.as_ref().clone(), o2.as_ref().clone(), c.span);
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
                        EqConstraint::new(a1.clone(), a2.clone(), span).with_parent(parent.clone()),
                    );
                }
            }
            (Ty::Tuple(t1), Ty::Tuple(t2)) if t1.len() == t2.len() => {
                let args1 = t1.clone();
                let args2 = t2.clone();
                let parent = Rc::new(c);
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    cset.push(
                        EqConstraint::new(a1.clone(), a2.clone(), span).with_parent(parent.clone()),
                    );
                }
            }
            (Ty::Scheme { quant: q1, ty: t1 }, Ty::Scheme { quant: q2, ty: t2 })
                if q1.len() == q2.len() =>
            {
                let constr = EqConstraint::new(t1.as_ref().clone(), t2.as_ref().clone(), span);
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

impl EqConstraintSet {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, c: EqConstraint) {
        self.constrs.push_back(c);
    }
}

impl Display for Subs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{} |-> ({})", self.old, self.new)
    }
}

impl Display for EqConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

impl Display for EqConstraintSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.constrs.iter().try_for_each(|c| write!(f, "{c}, "))
    }
}
