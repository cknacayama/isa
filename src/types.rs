use std::rc::Rc;

use crate::error::{TypeError, TypeResult};

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
pub enum Type {
    #[default]
    Unknown,

    Unit,
    Int,
    Float,
    Char,
    Bool,
    String,

    Proc(Rc<ProcSig>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProcSig {
    pub params: Vec<Type>,
    pub ret: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Assign,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Neq,
    Lt,
    Leq,
    Gt,
    Geq,
    BitAnd,
    BitOr,
    BitXor,
    BitShl,
    BitShr,
    BoolAnd,
    BoolOr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    BitNot,
    BoolNot,
    Cast(Type),
}

impl Type {
    pub fn is_numeric(&self) -> bool {
        use Type::*;
        matches!(self, Int | Float | Char)
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, Type::Unknown)
    }
}

impl BinOp {
    pub fn type_of(&self, lhs: Type, rhs: Type) -> TypeResult<Type> {
        use BinOp::*;

        match self {
            Assign => {
                if lhs == rhs {
                    Ok(lhs)
                } else {
                    Err(TypeError::Mismatch(lhs, rhs))
                }
            }
            Add | Sub | Mul | Div | Mod => {
                if lhs == rhs {
                    if lhs.is_numeric() {
                        Ok(lhs)
                    } else {
                        Err(TypeError::ExpectedNumeric(lhs))
                    }
                } else {
                    Err(TypeError::Mismatch(lhs, rhs))
                }
            }
            Eq | Neq => {
                if lhs == rhs {
                    Ok(Type::Bool)
                } else {
                    Err(TypeError::Mismatch(lhs, rhs))
                }
            }
            Lt | Leq | Gt | Geq => {
                if lhs == rhs {
                    if lhs.is_numeric() {
                        Ok(Type::Bool)
                    } else {
                        Err(TypeError::ExpectedNumeric(lhs))
                    }
                } else {
                    Err(TypeError::Mismatch(lhs, rhs))
                }
            }
            BitAnd | BitOr | BitXor | BitShl | BitShr => match (&lhs, &rhs) {
                (Type::Int, Type::Int) => Ok(Type::Int),
                (_, _) if lhs == rhs => Err(TypeError::Expected(Type::Int, lhs)),
                _ => Err(TypeError::Mismatch(lhs, rhs)),
            },
            BoolAnd | BoolOr => match (&lhs, &rhs) {
                (Type::Bool, Type::Bool) => Ok(Type::Bool),
                (_, _) if lhs == rhs => Err(TypeError::Expected(Type::Bool, lhs)),
                _ => Err(TypeError::Mismatch(lhs, rhs)),
            },
        }
    }
}

impl UnOp {
    pub fn type_of(&self, ty: Type) -> TypeResult<Type> {
        use UnOp::*;

        match self {
            Neg => {
                if ty.is_numeric() {
                    Ok(ty)
                } else {
                    Err(TypeError::ExpectedNumeric(ty))
                }
            }
            BitNot => {
                if ty == Type::Int {
                    Ok(Type::Int)
                } else {
                    Err(TypeError::Expected(Type::Int, ty))
                }
            }
            BoolNot => {
                if ty == Type::Bool {
                    Ok(Type::Bool)
                } else {
                    Err(TypeError::Expected(Type::Bool, ty))
                }
            }
            Cast(to) => Ok(to.clone()),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type::*;
        match self {
            Unknown => write!(f, "unknown"),
            Unit => write!(f, "unit"),
            Int => write!(f, "int"),
            Float => write!(f, "float"),
            Char => write!(f, "char"),
            Bool => write!(f, "bool"),
            String => write!(f, "string"),
            Proc(sig) => {
                write!(f, "proc(")?;
                for (i, param) in sig.params.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i != sig.params.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ") -> {}", sig.ret)
            }
        }
    }
}
