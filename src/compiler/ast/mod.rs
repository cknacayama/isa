pub mod typed;
pub mod untyped;

use super::{token::TokenKind, types::Type};
use crate::global::Symbol;
use std::{fmt::Display, rc::Rc};

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
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
    #[must_use]
    pub fn from_token(tk: TokenKind<'_>) -> Option<Self> {
        match tk {
            TokenKind::Plus => Some(BinOp::Add),
            TokenKind::Minus => Some(BinOp::Sub),
            TokenKind::Star => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            TokenKind::Percent => Some(BinOp::Rem),
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

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Rem => write!(f, "%"),
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

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Not,
    Neg,
}

impl UnOp {
    #[must_use]
    pub fn from_token(tk: TokenKind<'_>) -> Option<Self> {
        match tk {
            TokenKind::KwNot => Some(UnOp::Not),
            TokenKind::Minus => Some(UnOp::Neg),
            _ => None,
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

impl TokenKind<'_> {
    #[must_use]
    pub fn can_start_expr(&self) -> bool {
        matches!(
            self,
            TokenKind::LParen
                | TokenKind::Integer(_)
                | TokenKind::Ident(_)
                | TokenKind::KwTrue
                | TokenKind::KwFalse
                | TokenKind::KwLet
                | TokenKind::KwFn
                | TokenKind::KwNot
                | TokenKind::KwType
                | TokenKind::KwMatch
                | TokenKind::KwIf
        )
    }

    #[must_use]
    pub fn can_start_type(&self) -> bool {
        matches!(
            self,
            TokenKind::LParen | TokenKind::Ident(_) | TokenKind::KwInt | TokenKind::KwBool
        )
    }
    #[must_use]
    pub fn can_start_pat(&self) -> bool {
        matches!(
            self,
            TokenKind::LParen
                | TokenKind::Underscore
                | TokenKind::Ident(_)
                | TokenKind::Integer(_)
                | TokenKind::KwTrue
                | TokenKind::KwFalse
                | TokenKind::KwNot
                | TokenKind::Minus
        )
    }
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub id:     Symbol,
    pub params: Box<[Rc<Type>]>,
}

impl Constructor {
    #[must_use]
    pub fn new(id: Symbol, params: Box<[Rc<Type>]>) -> Self {
        Self { id, params }
    }
}

impl Display for Constructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)?;
        self.params.iter().try_for_each(|p| write!(f, " {p}"))
    }
}
