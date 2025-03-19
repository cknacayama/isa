use std::{fmt::Display, rc::Rc};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Unit,
    Int,
    Bool,
    Var(u64),
    Fn {
        param: Rc<Type>,
        ret:   Rc<Type>,
    },
    Generic {
        quant: Box<[u64]>,
        ty:    Rc<Type>,
    },
    Named {
        name: Rc<str>,
        args: Box<[Rc<Type>]>,
    },
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Int => write!(f, "int"),
            Self::Bool => write!(f, "bool"),
            Self::Fn { param, ret } => write!(f, "({param} -> {ret})"),
            Self::Var(var) => write!(f, "'{var}"),
            Self::Generic { quant, ty } => {
                for n in quant {
                    write!(f, "'{n} ")?;
                }
                write!(f, ". {ty}")
            }
            Self::Named { name, args } => {
                write!(f, "({name}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Type {
    #[must_use]
    pub fn is_simple(&self) -> bool {
        match self {
            Self::Int | Self::Bool | Self::Unit | Self::Var(_) => true,
            Self::Named { args, .. } => !args.iter().any(|t| !t.is_simple()),
            _ => false,
        }
    }

    #[must_use]
    pub fn occurs(&self, var: u64) -> bool {
        match self {
            Self::Fn { param, ret } => param.occurs(var) || ret.occurs(var),
            Self::Var(n) => *n == var,
            Self::Generic { ty, .. } => ty.occurs(var),
            Self::Named { args, .. } => args.iter().any(|t| t.occurs(var)),

            _ => false,
        }
    }
}
