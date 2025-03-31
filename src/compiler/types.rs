use std::fmt::Display;
use std::rc::Rc;

use super::ast::PathIdent;

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

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Int => write!(f, "int"),
            Self::Bool => write!(f, "bool"),
            Self::Fn { param, ret } => write!(f, "{param} -> {ret}"),
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
                    write!(f, " {arg}")?;
                }
                Ok(())
            }
        }
    }
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

    /// Returns `true` if the ty is [`Named`].
    ///
    /// [`Named`]: Ty::Named
    #[must_use]
    pub const fn is_named(&self) -> bool {
        matches!(self, Self::Named { .. })
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
                let first = iter
                    .next()
                    .unwrap_or_else(|| unreachable!())
                    .free_type_variables();
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

    /// Returns `true` if the ty is [`Scheme`].
    ///
    /// [`Scheme`]: Ty::Scheme
    #[must_use]
    pub fn is_scheme(&self) -> bool {
        matches!(self, Self::Scheme { .. })
    }
}
