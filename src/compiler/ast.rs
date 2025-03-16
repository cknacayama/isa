use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

use crate::span::{Span, Spanned};

use super::{token::TokenKind, types::Type};

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
    And,
    Or,
}

impl BinOp {
    pub fn from_token(tk: TokenKind<'_>) -> Option<Self> {
        match tk {
            TokenKind::Plus => Some(BinOp::Add),
            TokenKind::Minus => Some(BinOp::Sub),
            TokenKind::Star => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            TokenKind::Percent => Some(BinOp::Rem),
            TokenKind::Caret => Some(BinOp::Pow),
            TokenKind::EqEq => Some(BinOp::Eq),
            TokenKind::BangEq => Some(BinOp::Ne),
            TokenKind::Gt => Some(BinOp::Gt),
            TokenKind::Ge => Some(BinOp::Ge),
            TokenKind::Lt => Some(BinOp::Lt),
            TokenKind::Le => Some(BinOp::Le),
            TokenKind::KwAnd => Some(BinOp::And),
            TokenKind::KwOr => Some(BinOp::Or),

            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Not,
    Neg,
}

impl UnOp {
    pub fn from_token(tk: TokenKind<'_>) -> Option<Self> {
        match tk {
            TokenKind::KwNot => Some(UnOp::Not),
            TokenKind::Minus => Some(UnOp::Neg),
            _ => None,
        }
    }
}

#[derive(Clone)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
    pub span: Span,
}

impl<'a> From<Spanned<ExprKind<'a>>> for Expr<'a> {
    fn from(value: Spanned<ExprKind<'a>>) -> Self {
        Self::new(value.data, value.span)
    }
}

impl Debug for Expr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr").field("kind", &self.kind).finish()
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind<'a> {
    Int(i64),

    Bool(bool),

    Ident(&'a str),

    BinOp(BinOp),

    UnOp(UnOp),

    Let {
        id:   &'a str,
        expr: Box<Expr<'a>>,
        body: Box<Expr<'a>>,
    },

    Fn {
        param: &'a str,
        expr:  Box<Expr<'a>>,
    },

    If {
        cond:      Box<Expr<'a>>,
        then:      Box<Expr<'a>>,
        otherwise: Box<Expr<'a>>,
    },

    Call {
        callee: Box<Expr<'a>>,
        arg:    Box<Expr<'a>>,
    },
}

impl<'a> Expr<'a> {
    pub fn new(kind: ExprKind<'a>, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn bin_expr(op: BinOp, lhs: Expr<'a>, rhs: Expr<'a>, span: Span) -> Self {
        let op = Self::new(ExprKind::BinOp(op), span);
        let lhs_span = lhs.span;
        let c1 = Self::new(
            ExprKind::Call {
                callee: Box::new(op),
                arg:    Box::new(lhs),
            },
            lhs_span,
        );
        Self::new(
            ExprKind::Call {
                callee: Box::new(c1),
                arg:    Box::new(rhs),
            },
            span,
        )
    }
}

#[derive(Clone)]
pub struct TypedExpr<'a> {
    pub kind: TypedExprKind<'a>,
    pub span: Span,
    pub ty:   Rc<Type>,
}

impl Debug for TypedExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr")
            .field("kind", &self.kind)
            .field("ty", &self.ty)
            .finish()
    }
}

impl<'a> TypedExpr<'a> {
    pub fn new(kind: TypedExprKind<'a>, span: Span, ty: Rc<Type>) -> Self {
        Self { kind, span, ty }
    }

    pub fn visit<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Self),
    {
        match &mut self.kind {
            TypedExprKind::Let { expr, body, .. } => {
                expr.visit(f);
                body.visit(f);
            }
            TypedExprKind::Fn { expr, .. } => {
                expr.visit(f);
            }
            TypedExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                cond.visit(f);
                then.visit(f);
                otherwise.visit(f);
            }
            TypedExprKind::Call { callee, arg } => {
                callee.visit(f);
                arg.visit(f);
            }
            _ => (),
        }
        f(self)
    }
}

#[derive(Debug, Clone)]
pub enum TypedExprKind<'a> {
    Int(i64),

    Bool(bool),

    Ident(&'a str),

    BinOp(BinOp),

    UnOp(UnOp),

    Let {
        id:   &'a str,
        expr: Box<TypedExpr<'a>>,
        body: Box<TypedExpr<'a>>,
    },

    Fn {
        param: &'a str,
        expr:  Box<TypedExpr<'a>>,
    },

    If {
        cond:      Box<TypedExpr<'a>>,
        then:      Box<TypedExpr<'a>>,
        otherwise: Box<TypedExpr<'a>>,
    },

    Call {
        callee: Box<TypedExpr<'a>>,
        arg:    Box<TypedExpr<'a>>,
    },
}

impl<'a> TokenKind<'a> {
    pub fn can_start_expr(&self) -> bool {
        matches!(
            self,
            TokenKind::Minus
                | TokenKind::LParen
                | TokenKind::Integer(_)
                | TokenKind::Ident(_)
                | TokenKind::KwTrue
                | TokenKind::KwFalse
                | TokenKind::KwLet
                | TokenKind::KwFn
                | TokenKind::KwNot
                | TokenKind::KwIf
        )
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Rem => write!(f, "%"),
            BinOp::Pow => write!(f, "^"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Ge => write!(f, ">="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::And => write!(f, "and"),
            BinOp::Or => write!(f, "or"),
        }
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "not"),
            UnOp::Neg => write!(f, "-"),
        }
    }
}

impl Display for TypedExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TypedExprKind::Int(i) => write!(f, "{}", i),
            TypedExprKind::Bool(b) => write!(f, "{}", b),
            TypedExprKind::Ident(id) => write!(f, "{}", id),
            TypedExprKind::BinOp(op) => write!(f, "{}", op),
            TypedExprKind::UnOp(op) => write!(f, "{}", op),
            TypedExprKind::Let { id, expr, body } => {
                write!(f, "(let {} = {} in {})", id, expr, body)
            }
            TypedExprKind::Fn { param, expr } => {
                write!(f, "(fn {} -> {})", param, expr)
            }
            TypedExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                write!(f, "(if {} then {} else {})", cond, then, otherwise)
            }
            TypedExprKind::Call { callee, arg } => {
                write!(f, "({} {})", callee, arg)
            }
        }
        .and_then(|()| write!(f, ": {}", self.ty))
    }
}
