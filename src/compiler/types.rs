use std::fmt::Display;
use std::rc::Rc;

use super::ast::PathIdent;
use super::infer::Substitute;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Unit,
    Int,
    Bool,
    Var(u64),
    Fn { param: Rc<Ty>, ret: Rc<Ty> },
    Scheme { quant: Rc<[u64]>, ty: Rc<Ty> },
    Named { name: PathIdent, args: Rc<[Ty]> },
}

impl Ty {
    #[must_use]
    pub fn occurs(&self, var: u64) -> bool {
        match self {
            Self::Fn { param, ret } => param.occurs(var) || ret.occurs(var),
            Self::Var(n) => *n == var,
            Self::Scheme { ty, .. } => ty.occurs(var),
            Self::Named { args, .. } => args.iter().any(|t| t.occurs(var)),

            _ => false,
        }
    }

    /// Returns `true` if the ty is [`Fn`].
    ///
    /// [`Fn`]: Ty::Fn
    #[must_use]
    pub const fn is_fn(&self) -> bool {
        matches!(self, Self::Fn { .. })
    }

    #[must_use]
    pub const fn as_var(&self) -> Option<u64> {
        if let Self::Var(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    #[must_use]
    pub fn free_type_variables(&self) -> Vec<u64> {
        match self {
            Self::Unit | Self::Int | Self::Bool => Vec::new(),
            Self::Named { args, .. } if args.is_empty() => Vec::new(),
            Self::Var(id) => vec![*id],
            Self::Fn { param, ret } => {
                let mut param = param.free_type_variables();
                for r in ret.free_type_variables() {
                    if !param.contains(&r) {
                        param.push(r);
                    }
                }
                param
            }
            Self::Scheme { quant, ty } => {
                let mut ty = ty.free_type_variables();
                ty.retain(|t| !quant.contains(t));
                ty
            }
            Self::Named { args, .. } => {
                let mut iter = args.iter();
                let first = iter.next().unwrap().free_type_variables();
                iter.fold(first, |mut acc, arg| {
                    for t in arg.free_type_variables() {
                        if !acc.contains(&t) {
                            acc.push(t);
                        }
                    }
                    acc
                })
            }
        }
    }
}

impl Substitute for Ty {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Self) -> Option<Self>,
    {
        match self {
            Self::Fn { param, ret } => {
                param.substitute(subs);
                ret.substitute(subs);
            }
            Self::Scheme { ty, .. } => {
                ty.substitute(subs);
            }
            Self::Named { args, .. } => {
                let mut new = args.to_vec();
                for arg in &mut new {
                    arg.substitute(subs);
                }
                if args.as_ref() != new.as_slice() {
                    *args = new.into();
                }
            }
            _ => (),
        }

        if let Some(ty) = subs(self) {
            *self = ty;
        }
    }
}

impl Substitute for Rc<Ty> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        let mut ty = match self.as_ref() {
            Ty::Fn { param, ret } => {
                let mut new_param = param.as_ref().clone();
                let mut new_ret = ret.as_ref().clone();
                new_param.substitute(subs);
                new_ret.substitute(subs);

                let param = Self::new(new_param);
                let ret = Self::new(new_ret);

                Ty::Fn { param, ret }
            }
            Ty::Scheme { quant, ty } => {
                let mut new_ty = ty.as_ref().clone();
                new_ty.substitute(subs);

                let ty = Self::new(new_ty);

                Ty::Scheme {
                    quant: quant.clone(),
                    ty,
                }
            }
            Ty::Named { name, args } => {
                let mut new_args = args.to_vec();
                for arg in &mut new_args {
                    arg.substitute(subs);
                }
                let args = Rc::from(new_args);
                Ty::Named { name: *name, args }
            }
            _ => {
                if let Some(new) = subs(self) {
                    *self = Self::new(new);
                }
                return;
            }
        };

        if let Some(new) = subs(&ty) {
            ty = new;
        }
        if self.as_ref() != &ty {
            *self = Self::new(ty);
        }
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Int => write!(f, "int"),
            Self::Bool => write!(f, "bool"),
            Self::Fn { param, ret } => write!(f, "({param} -> {ret})"),
            Self::Var(var) => write!(f, "'{var}"),
            Self::Scheme { quant, ty } => {
                for n in quant.iter() {
                    write!(f, "'{n} ")?;
                }
                write!(f, ". {ty}")
            }
            Self::Named { name, args } => {
                write!(f, "({name}")?;
                for arg in args.iter() {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
        }
    }
}
