use std::rc::Rc;

use super::ast::{Path, mod_path};
use super::ctx::Generator;
use super::infer::{Subs, Substitute};
use super::token::Ident;
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Int,
    Bool,
    Char,
    Real,
    Var(u64),
    Tuple(Rc<[Ty]>),
    Fn { param: Rc<Ty>, ret: Rc<Ty> },
    Scheme { quant: Rc<[u64]>, ty: Rc<Ty> },
    Named { name: Path, args: Rc<[Ty]> },
    Generic { var: u64, args: Rc<[Ty]> },
}

impl From<Rc<Self>> for Ty {
    fn from(value: Rc<Self>) -> Self {
        value.as_ref().clone()
    }
}

impl From<&Rc<Self>> for Ty {
    fn from(value: &Rc<Self>) -> Self {
        value.as_ref().clone()
    }
}

impl Ty {
    #[must_use]
    pub fn occurs(&self, var: u64) -> bool {
        match self {
            Self::Fn { param, ret } => param.occurs(var) || ret.occurs(var),
            Self::Var(n) => *n == var,
            Self::Scheme { ty, .. } => ty.occurs(var),
            Self::Tuple(args) | Self::Named { args, .. } => args.iter().any(|t| t.occurs(var)),
            Self::Generic { var: n, args } => *n == var || args.iter().any(|t| t.occurs(var)),

            Self::Int | Self::Char | Self::Bool | Self::Real => false,
        }
    }

    pub fn contains_name(&self, path: &Path) -> Option<Span> {
        match self {
            Self::Fn { param, ret } => param
                .contains_name(path)
                .or_else(|| ret.contains_name(path)),
            Self::Scheme { ty, .. } => ty.contains_name(path),
            Self::Tuple(args) | Self::Generic { args, .. } => {
                args.iter().find_map(|t| t.contains_name(path))
            }
            Self::Named { name, args } => {
                if name == path {
                    return Some(name.span());
                }
                args.iter().find_map(|t| t.contains_name(path))
            }

            Self::Int | Self::Char | Self::Bool | Self::Real | Self::Var(_) => None,
        }
    }

    pub fn instantiate(self, generator: &mut impl Generator) -> (Self, Vec<Subs>) {
        let Self::Scheme { quant, ty } = self else {
            return (self, Vec::new());
        };

        let subs: Vec<_> = quant
            .iter()
            .map(|q| Subs::new(*q, generator.gen_type_var()))
            .collect();
        let mut ty = ty.as_ref().clone();

        ty.substitute_many(&subs);

        (ty, subs)
    }

    pub fn list(ty: Self) -> Self {
        Self::Named {
            name: mod_path!(list::List),
            args: Rc::new([ty]),
        }
    }

    pub fn equivalent(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Named { name: n1, args: a1 }, Self::Named { name: n2, args: a2 }) => {
                n1 == n2
                    && a1.len() == a2.len()
                    && a1.iter().zip(a2.iter()).all(|(t1, t2)| t1.equivalent(t2))
            }

            (Self::Generic { args: a1, .. }, Self::Generic { args: a2, .. })
            | (Self::Tuple(a1), Self::Tuple(a2)) => {
                a1.len() == a2.len() && a1.iter().zip(a2.iter()).all(|(t1, t2)| t1.equivalent(t2))
            }

            (Self::Fn { param: p1, ret: r1 }, Self::Fn { param: p2, ret: r2 }) => {
                p1.equivalent(p2) && r1.equivalent(r2)
            }

            (Self::Scheme { quant: q1, ty: t1 }, Self::Scheme { quant: q2, ty: t2 }) => {
                q1.len() == q2.len() && t1.equivalent(t2)
            }

            (Self::Var(_), Self::Var(_)) => true,

            (lhs, rhs) => lhs == rhs,
        }
    }

    pub fn function<I>(params: I, ret: Self) -> Self
    where
        I: IntoIterator<Item = Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        params.into_iter().rev().fold(ret, |ret, param| Self::Fn {
            param: Rc::new(param),
            ret:   Rc::new(ret),
        })
    }

    #[must_use]
    pub const fn is_fn(&self) -> bool {
        matches!(self, Self::Fn { .. })
    }

    #[must_use]
    pub const fn is_char(&self) -> bool {
        matches!(self, Self::Char)
    }

    pub const fn is_simple_fmt(&self) -> bool {
        matches!(
            self,
            Self::Generic { .. }
                | Self::Named { .. }
                | Self::Int
                | Self::Bool
                | Self::Char
                | Self::Real
                | Self::Var(_)
                | Self::Tuple(_)
        )
    }

    pub fn get_ident(&self) -> Option<Ident> {
        if let Self::Named { name, .. } = self {
            name.as_ident()
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_var(&self) -> Option<u64> {
        if let Self::Var(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    fn free_type_variables_inner(&self, free: &mut Vec<u64>) {
        match self {
            Self::Int | Self::Bool | Self::Char | Self::Real => (),
            Self::Named { args, .. } if args.is_empty() => (),
            Self::Var(id) if free.contains(id) => (),

            Self::Var(id) => {
                free.push(*id);
            }

            Self::Fn { param, ret } => {
                param.free_type_variables_inner(free);
                ret.free_type_variables_inner(free);
            }

            Self::Scheme { quant, ty } => {
                ty.free_type_variables_inner(free);
                while let Some(pos) = free.iter().position(|f| quant.contains(f)) {
                    free.swap_remove(pos);
                }
            }

            Self::Named { args, .. } | Self::Tuple(args) => {
                for arg in args.iter() {
                    arg.free_type_variables_inner(free);
                }
            }

            Self::Generic { var, args } => {
                for arg in args.iter() {
                    arg.free_type_variables_inner(free);
                }
                if !free.contains(var) {
                    free.push(*var);
                }
            }
        }
    }

    #[must_use]
    pub fn free_type_variables(&self) -> Vec<u64> {
        let mut free = Vec::new();
        self.free_type_variables_inner(&mut free);
        free
    }

    pub fn param_iter(&self) -> impl Iterator<Item = Self> {
        ParamIter { ty: self.clone() }
    }

    #[must_use]
    pub const fn is_scheme(&self) -> bool {
        matches!(self, Self::Scheme { .. })
    }

    #[must_use]
    pub const fn is_var(&self) -> bool {
        matches!(self, Self::Var(..))
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
            Self::Generic { args, .. } | Self::Named { args, .. } | Self::Tuple(args) => {
                let mut new = args.to_vec();
                for arg in &mut new {
                    arg.substitute(subs);
                }
                if args.as_ref() != new.as_slice() {
                    *args = new.into();
                }
            }

            Self::Int | Self::Bool | Self::Char | Self::Real | Self::Var(_) => (),
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

                let param = if param.as_ref() == &new_param {
                    param.clone()
                } else {
                    Self::new(new_param)
                };
                let ret = if ret.as_ref() == &new_ret {
                    ret.clone()
                } else {
                    Self::new(new_ret)
                };

                Ty::Fn { param, ret }
            }
            Ty::Scheme { quant, ty } => {
                let mut new_ty = ty.as_ref().clone();
                new_ty.substitute(subs);

                let ty = if ty.as_ref() == &new_ty {
                    ty.clone()
                } else {
                    Self::new(new_ty)
                };

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
                let args = if args.as_ref() == new_args {
                    args.clone()
                } else {
                    Rc::from(new_args)
                };
                Ty::Named {
                    name: name.clone(),
                    args,
                }
            }
            Ty::Generic { var, args } => {
                let mut new_args = args.to_vec();
                for arg in &mut new_args {
                    arg.substitute(subs);
                }
                let args = if args.as_ref() == new_args {
                    args.clone()
                } else {
                    Rc::from(new_args)
                };
                Ty::Generic { var: *var, args }
            }
            Ty::Tuple(args) => {
                let mut new_args = args.to_vec();
                for arg in &mut new_args {
                    arg.substitute(subs);
                }
                let args = if args.as_ref() == new_args {
                    args.clone()
                } else {
                    Rc::from(new_args)
                };
                Ty::Tuple(args)
            }
            Ty::Int | Ty::Bool | Ty::Char | Ty::Real | Ty::Var(_) => {
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

#[derive(Debug, Clone)]
pub struct ParamIter {
    ty: Ty,
}

impl Iterator for ParamIter {
    type Item = Ty;

    fn next(&mut self) -> Option<Self::Item> {
        match &self.ty {
            Ty::Fn { param, ret } => {
                let param = param.as_ref().clone();
                self.ty = ret.as_ref().clone();
                Some(param)
            }
            Ty::Scheme { ty, .. } => {
                self.ty = ty.as_ref().clone();
                self.next()
            }
            _ => None,
        }
    }
}
