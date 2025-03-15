use std::{fmt::Display, rc::Rc};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Fn {
    pub param: Rc<Type>,
    pub ret:   Rc<Type>,
}

impl Fn {
    pub fn new(param: Rc<Type>, ret: Rc<Type>) -> Self {
        Self { param, ret }
    }

    pub fn param(&self) -> &Type {
        &self.param
    }

    pub fn ret(&self) -> &Type {
        &self.ret
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Bool,
    Fn(Fn),
    Var(u64),
    Generic { quant: Vec<u64>, ty: Rc<Type> },
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Bool => write!(f, "bool"),
            Type::Fn(fun) => write!(f, "{} -> {}", fun.param, fun.ret),
            Type::Var(var) => write!(f, "'{}", var),
            Type::Generic { quant, ty } => {
                for n in quant {
                    write!(f, "'{} ", n)?;
                }
                write!(f, ". {}", ty)
            }
        }
    }
}

impl Type {
    pub fn is_simple(&self) -> bool {
        matches!(self, Self::Int | Self::Bool | Self::Var(_))
    }

    pub fn occurs(&self, var: u64) -> bool {
        match self {
            Type::Int => false,
            Type::Bool => false,
            Type::Fn(f) => f.param().occurs(var) || f.ret().occurs(var),
            Type::Var(n) => *n == var,
            Type::Generic { ty, .. } => ty.occurs(var),
        }
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(..))
    }

    pub fn is_fn(&self) -> bool {
        matches!(self, Self::Fn { .. })
    }
}
