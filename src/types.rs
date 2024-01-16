#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Type {
    #[default]
    Unit,

    Int,
    Float,
    Char,
    Bool,
    String,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    BitNot,
    BoolNot,
    Cast(Type),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    Mismatch(Type, Type),
    Expected(Type, Type),
    ExpectedOneOf(Vec<Type>, Type),
    ExpectedNumeric(Type),
}

impl Type {
    pub fn is_numeric(self) -> bool {
        use Type::*;
        match self {
            Int | Float | Char => true,
            _ => false,
        }
    }
}

impl BinOp {
    pub fn type_of(self, lhs: Type, rhs: Type) -> Result<Type, TypeError> {
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
            BitAnd | BitOr | BitXor | BitShl | BitShr => match (lhs, rhs) {
                (Type::Int, Type::Int) => Ok(Type::Int),
                (_, _) if lhs == rhs => Err(TypeError::Expected(Type::Int, lhs)),
                _ => Err(TypeError::Mismatch(lhs, rhs)),
            },
            BoolAnd | BoolOr => match (lhs, rhs) {
                (Type::Bool, Type::Bool) => Ok(Type::Bool),
                (_, _) if lhs == rhs => Err(TypeError::Expected(Type::Bool, lhs)),
                _ => Err(TypeError::Mismatch(lhs, rhs)),
            },
        }
    }
}

impl UnOp {
    pub fn type_of(self, ty: Type) -> Result<Type, TypeError> {
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
            Cast(to) => {
                if ty.is_numeric() && (to.is_numeric() || to == Type::Bool) {
                    Ok(to)
                } else {
                    Err(TypeError::ExpectedNumeric(ty))
                }
            }
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type::*;
        match self {
            Unit => write!(f, "unit"),
            Int => write!(f, "int"),
            Float => write!(f, "float"),
            Char => write!(f, "char"),
            Bool => write!(f, "bool"),
            String => write!(f, "string"),
        }
    }
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeError::*;
        match self {
            Mismatch(t1, t2) => write!(f, "mismatch ({} != {})", t1, t2),
            Expected(expected, actual) => write!(f, "expected {}, found {}", expected, actual),
            ExpectedOneOf(expected, actual) => {
                write!(f, "expected one of: ")?;
                for (i, ty) in expected.iter().enumerate() {
                    write!(f, "{}", ty)?;
                    if i != expected.len() - 1 {
                        write!(f, " | ")?;
                    }
                }
                write!(f, ", found {}", actual)
            }
            ExpectedNumeric(actual) => write!(f, "expected numeric type, found {}", actual),
        }
    }
}

impl std::error::Error for TypeError {
}
