use std::collections::VecDeque;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use super::ast::{Ident, Path};
use super::ctx::Ctx;
use super::error::Uninferable;
use super::types::{Ty, TyId};
use crate::global::Span;

#[derive(Debug, Clone)]
pub struct Subs {
    old:  TyId,
    subs: Ty,
}

impl Subs {
    #[must_use]
    pub const fn new(old: TyId, new: Ty) -> Self {
        Self { old, subs: new }
    }

    #[must_use]
    pub const fn old(&self) -> TyId {
        self.old
    }

    pub const fn subs(&self) -> &Ty {
        &self.subs
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
        if &Ty::Var(subs.old) == subs.subs() {
            return;
        }
        self.substitute(&mut |t| match t {
            Ty::Var(id) if *id == subs.old => Some(subs.subs.clone()),
            Ty::Generic { var, args } if *var == subs.old => match subs.subs.clone() {
                Ty::Var(new) => Some(Ty::Generic {
                    var:  new,
                    args: args.clone(),
                }),
                Ty::Named { name, args: named } => {
                    let mut named = named.to_vec();
                    named.extend_from_slice(args);
                    Some(Ty::Named {
                        name,
                        args: named.into(),
                    })
                }
                Ty::Generic { var, args: generic } => {
                    let mut generic = generic.to_vec();
                    generic.extend_from_slice(args);
                    Some(Ty::Generic {
                        var,
                        args: generic.into(),
                    })
                }
                _ => None,
            },
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

    fn substitute_self(&mut self, instance: &Ty)
    where
        Self: Sized,
    {
        self.substitute(&mut |ty| match ty {
            Ty::This(args) if args.is_empty() => Some(instance.clone()),
            Ty::This(args) => match instance.clone() {
                Ty::Var(new) => Some(Ty::Generic {
                    var:  new,
                    args: args.clone(),
                }),
                Ty::Named { name, args: named } => {
                    let mut named = named.to_vec();
                    named.extend_from_slice(args);
                    Some(Ty::Named {
                        name,
                        args: named.into(),
                    })
                }
                Ty::Generic { var, args: generic } => {
                    let mut generic = generic.to_vec();
                    generic.extend_from_slice(args);
                    Some(Ty::Generic {
                        var,
                        args: generic.into(),
                    })
                }
                _ => None,
            },

            _ => None,
        });
    }

    fn substitute_param(&mut self, subs: &[(Ident, TyId)])
    where
        Self: Sized,
    {
        if subs.is_empty() {
            return;
        }
        self.substitute(&mut |ty| match ty {
            Ty::Named { name, args } if args.is_empty() => subs
                .iter()
                .find_map(|(s, v)| name.is_ident(*s).then_some(Ty::Var(*v))),
            Ty::Named { name, args } => subs.iter().find_map(|(s, v)| {
                name.is_ident(*s).then(|| Ty::Generic {
                    var:  *v,
                    args: args.clone(),
                })
            }),
            _ => None,
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

impl IntoIterator for EqConstraintSet {
    type Item = EqConstraint;
    type IntoIter = std::collections::vec_deque::IntoIter<EqConstraint>;

    fn into_iter(self) -> Self::IntoIter {
        self.constrs.into_iter()
    }
}

impl Deref for EqConstraintSet {
    type Target = VecDeque<EqConstraint>;

    fn deref(&self) -> &Self::Target {
        &self.constrs
    }
}

impl DerefMut for EqConstraintSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.constrs
    }
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

#[derive(Debug, Clone)]
pub struct ClassConstraint {
    class: Path,
    ty:    Ty,
    span:  Span,
}

impl Eq for ClassConstraint {
}

impl PartialEq for ClassConstraint {
    fn eq(&self, other: &Self) -> bool {
        self.class == other.class && self.ty == other.ty
    }
}

impl ClassConstraint {
    pub const fn new(class: Path, ty: Ty, span: Span) -> Self {
        Self { class, ty, span }
    }

    pub const fn class(&self) -> &Path {
        &self.class
    }

    pub const fn get_mut(&mut self) -> (&mut Path, &mut Ty) {
        (&mut self.class, &mut self.ty)
    }

    pub const fn ty(&self) -> &Ty {
        &self.ty
    }

    pub const fn span(&self) -> Span {
        self.span
    }

    pub const fn span_mut(&mut self) -> &mut Span {
        &mut self.span
    }
}

impl Substitute for ClassConstraint {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.ty.substitute(subs);
    }
}

#[derive(Debug, Clone)]
pub enum Constraint {
    Eq(Box<EqConstraint>),
    Class(Box<ClassConstraint>),
}

impl Constraint {
    pub fn span(&self) -> Span {
        match self {
            Self::Eq(eq_constraint) => eq_constraint.span(),
            Self::Class(class_constraint) => class_constraint.span(),
        }
    }

    #[must_use]
    pub const fn is_class(&self) -> bool {
        matches!(self, Self::Class(..))
    }
}

#[derive(Debug, Clone)]
pub struct ClassConstraintSet {
    constrs: Vec<ClassConstraint>,
}

impl IntoIterator for ClassConstraintSet {
    type Item = ClassConstraint;
    type IntoIter = std::vec::IntoIter<ClassConstraint>;

    fn into_iter(self) -> Self::IntoIter {
        self.constrs.into_iter()
    }
}

impl Deref for ClassConstraintSet {
    type Target = Vec<ClassConstraint>;
    fn deref(&self) -> &Self::Target {
        &self.constrs
    }
}

impl DerefMut for ClassConstraintSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.constrs
    }
}

impl ClassConstraintSet {
    pub const fn new() -> Self {
        Self {
            constrs: Vec::new(),
        }
    }

    pub fn join(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<T> From<T> for ClassConstraintSet
where
    Vec<ClassConstraint>: From<T>,
{
    fn from(value: T) -> Self {
        Self {
            constrs: Vec::from(value),
        }
    }
}

impl From<ClassConstraint> for ClassConstraintSet {
    fn from(value: ClassConstraint) -> Self {
        Self {
            constrs: Vec::from([value]),
        }
    }
}

fn unify_eq(
    c: EqConstraint,
    cset: &mut EqConstraintSet,
    subs: &mut Vec<Subs>,
) -> Result<(), Uninferable> {
    let span = c.span;
    match (&c.lhs, &c.rhs) {
        (Ty::Int, Ty::Int) | (Ty::Bool, Ty::Bool) | (Ty::Char, Ty::Char) | (Ty::Real, Ty::Real) => {
        }

        (Ty::Var(v1), Ty::Var(v2)) if v1 == v2 => {}

        (new, Ty::Var(old)) | (Ty::Var(old), new) if !new.occurs(*old) => {
            let s = Subs::new(*old, new.clone());

            cset.substitute_eq(&s);

            subs.push(s);
        }
        (
            Ty::Generic {
                var: v1,
                args: args1,
            },
            Ty::Generic {
                var: v2,
                args: args2,
            },
        ) if args1.len() == args2.len() => {
            let args1 = args1.clone();
            let args2 = args2.clone();
            let v1 = *v1;
            let v2 = *v2;
            let parent = Rc::new(c);
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                cset.push_back(
                    EqConstraint::new(a1.clone(), a2.clone(), span).with_parent(parent.clone()),
                );
            }
            if v1 != v2 {
                let s = Subs::new(v2, Ty::Var(v1));
                cset.substitute_eq(&s);
                subs.push(s);
            }
        }
        (Ty::Generic { var, args: vars }, Ty::Named { name, args: named })
        | (Ty::Named { name, args: named }, Ty::Generic { var, args: vars })
            if vars.len() <= named.len() =>
        {
            let var = *var;
            let name = *name;
            let vars = vars.clone();
            let named = named.clone();
            let parent = Rc::new(c);
            let mut named_iter = named.iter().rev();
            for arg in vars.iter().rev() {
                let named = named_iter.next().unwrap();
                cset.push_back(
                    EqConstraint::new(arg.clone(), named.clone(), span).with_parent(parent.clone()),
                );
            }
            let args = named_iter.cloned().rev().collect();
            let s = Subs::new(var, Ty::Named { name, args });
            cset.substitute_eq(&s);

            subs.push(s);
        }
        (Ty::Fn { param: i1, ret: o1 }, Ty::Fn { param: i2, ret: o2 }) => {
            let c1 = EqConstraint::new(i1.into(), i2.into(), c.span);
            let c2 = EqConstraint::new(o1.into(), o2.into(), c.span);
            let parent = Rc::new(c);

            cset.push_back(c1.with_parent(parent.clone()));
            cset.push_back(c2.with_parent(parent));
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
                cset.push_back(
                    EqConstraint::new(a1.clone(), a2.clone(), span).with_parent(parent.clone()),
                );
            }
        }
        (Ty::Tuple(t1), Ty::Tuple(t2)) if t1.len() == t2.len() => {
            let args1 = t1.clone();
            let args2 = t2.clone();
            let parent = Rc::new(c);
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                cset.push_back(
                    EqConstraint::new(a1.clone(), a2.clone(), span).with_parent(parent.clone()),
                );
            }
        }
        (Ty::Scheme { quant: q1, ty: t1 }, Ty::Scheme { quant: q2, ty: t2 })
            if q1.len() == q2.len() =>
        {
            let constr = EqConstraint::new(t1.into(), t2.into(), span);
            let parent = Rc::new(c);
            cset.push_back(constr.with_parent(parent));
        }

        _ => {
            let c = if let Some(parent) = c.parent {
                let mut parent = parent.as_ref().clone();
                parent.substitute_many(subs.as_slice());
                parent
            } else {
                c
            };
            return Err(Uninferable::new(
                Constraint::Eq(Box::new(c)),
                std::mem::take(subs),
            ));
        }
    }

    Ok(())
}

impl Ctx {
    fn unify_class(
        &self,
        classes: ClassConstraintSet,
    ) -> Result<ClassConstraintSet, Box<ClassConstraint>> {
        let mut constrs = Vec::new();

        for sets in classes
            .constrs
            .into_iter()
            .map(|c| self.instantiate_class(c.class(), c.ty(), c.span()).unwrap())
        {
            if let Some(constr) = sets
                .iter()
                .map(|(_, c)| c)
                .find(|c| c.constrs.iter().all(|c| c.ty().is_var()))
            {
                constrs.extend_from_slice(&constr.constrs);
            } else {
                let constr = sets
                    .into_iter()
                    .map(|(_, c)| c)
                    .find_map(|c| c.constrs.into_iter().find(|c| !c.ty().is_var()))
                    .unwrap();
                return Err(Box::new(constr));
            }
        }

        Ok(ClassConstraintSet { constrs })
    }

    pub fn unify(
        &mut self,
        mut cset: EqConstraintSet,
        mut classes: ClassConstraintSet,
    ) -> Result<(Vec<Subs>, ClassConstraintSet), Uninferable> {
        let mut subs = Vec::new();

        while let Some(c) = cset.constrs.pop_front() {
            unify_eq(c, &mut cset, &mut subs)?;
        }

        classes.substitute_many(&subs);

        let constrs = self
            .unify_class(classes)
            .map_err(|c| Uninferable::new(Constraint::Class(c), subs.clone()))?;

        self.substitute_many(&subs);

        Ok((subs, constrs))
    }
}

impl EqConstraintSet {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl Substitute for ClassConstraintSet {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        for ty in &mut self.constrs {
            ty.substitute(subs);
        }
    }
}
