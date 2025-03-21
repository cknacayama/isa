use std::fmt::Display;
use std::rc::Rc;

use crate::global::Symbol;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Unit,
    Int,
    Bool,
    Var(u64),
    Fn { param: Rc<Ty>, ret: Rc<Ty> },
    Scheme { quant: Rc<[u64]>, ty: Rc<Ty> },
    Named { name: Symbol, args: Rc<[Rc<Ty>]> },
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
}
