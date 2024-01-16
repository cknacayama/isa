use crate::{
    error::{Span, Spanned},
    types::{Type, TypeError},
};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Param<'a> {
    pub name: &'a str,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AstData<'a> {
    UnitExpr,
    BoolExpr(bool),
    IntExpr(u64),
    FloatExpr(f64),
    StringExpr(&'a str),
    CharExpr(char),
    IdentExpr(&'a str),

    BinExpr {
        op: BinOp,
        lhs: Box<Ast<'a>>,
        rhs: Box<Ast<'a>>,
    },

    UnExpr {
        op: UnOp,
        expr: Box<Ast<'a>>,
    },

    CallExpr {
        callee: &'a str,
        args: Vec<Ast<'a>>,
    },

    ReturnStmt(Option<Box<Ast<'a>>>),

    IfStmt {
        cond: Box<Ast<'a>>,
        then: Box<Ast<'a>>,
        else_: Option<Box<Ast<'a>>>,
    },

    WhileStmt {
        cond: Box<Ast<'a>>,
        body: Box<Ast<'a>>,
    },

    BlockStmt(Vec<Ast<'a>>),

    LetDecl {
        name: &'a str,
        ty: Type,
        is_mut: bool,
        value: Option<Box<Ast<'a>>>,
    },

    ProcDecl {
        name: &'a str,
        ret: Type,
        params: Vec<Param<'a>>,
        body: Vec<Ast<'a>>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ast<'a> {
    pub data: AstData<'a>,
    pub ty: Type,
    pub span: Span,
}

impl<'a> Ast<'a> {
    pub fn new(data: AstData<'a>, ty: Type, span: Span) -> Self {
        Self { data, ty, span }
    }
}

impl Spanned for Ast<'_> {
    #[inline(always)]
    fn span(&self) -> Span {
        self.span
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
