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
