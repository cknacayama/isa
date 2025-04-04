use std::fmt::Display;
use std::rc::Rc;

use super::ast::PathIdent;
use super::infer::Substitute;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Unit,
    Int,
    Bool,
    Char,
    Var(u64),
    Tuple(Rc<[Ty]>),
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

    #[must_use]
    pub const fn is_fn(&self) -> bool {
        matches!(self, Self::Fn { .. })
    }

    #[must_use]
    pub const fn is_char(&self) -> bool {
        matches!(self, Self::Char)
    }

    fn is_simple_fmt(&self) -> bool {
        match self {
            Self::Named { args, .. } => args.is_empty(),
            Self::Unit | Self::Int | Self::Bool | Self::Char | Self::Var(_) | Self::Tuple(_) => {
                true
            }
            Self::Fn { .. } | Self::Scheme { .. } => false,
        }
    }

    pub const fn get_name(&self) -> Option<&PathIdent> {
        if let Self::Named { name, .. } = self {
            Some(name)
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
            Self::Unit | Self::Int | Self::Bool | Self::Char => (),
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
            Self::Named { args, .. } | Self::Tuple(args) => {
                let mut new = args.to_vec();
                for arg in &mut new {
                    arg.substitute(subs);
                }
                if args.as_ref() != new.as_slice() {
                    *args = new.into();
                }
            }

            Self::Unit | Self::Int | Self::Bool | Self::Char | Self::Var(_) => (),
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
            Ty::Tuple(args) => {
                let mut new_args = args.to_vec();
                for arg in &mut new_args {
                    arg.substitute(subs);
                }
                let args = Rc::from(new_args);
                Ty::Tuple(args)
            }
            Ty::Unit | Ty::Int | Ty::Bool | Ty::Char | Ty::Var(_) => {
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

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Int => write!(f, "int"),
            Self::Bool => write!(f, "bool"),
            Self::Char => write!(f, "char"),
            Self::Fn { param, ret } => {
                if param.is_simple_fmt() {
                    write!(f, "{param}")?;
                } else {
                    write!(f, "({param})")?;
                }
                write!(f, " -> {ret}")
            }
            Self::Var(var) => write!(f, "'{var}"),
            Self::Scheme { quant, ty } => {
                for n in quant.iter() {
                    write!(f, "'{n} ")?;
                }
                write!(f, ". {ty}")
            }
            Self::Named { name, args } => {
                write!(f, "{name}")?;
                for arg in args.iter() {
                    if arg.is_simple_fmt() {
                        write!(f, " {arg}")?;
                    } else {
                        write!(f, " ({arg})")?;
                    }
                }
                Ok(())
            }
            Self::Tuple(types) => {
                write!(f, "(")?;
                let mut first = true;
                for ty in types.iter() {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, ")")
            }
        }
    }
}
