pub mod typed;
pub mod untyped;

use std::fmt::Display;
use std::rc::Rc;

use super::token::TokenKind;
use super::types::Ty;
use crate::global::Symbol;

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
    pub const fn from_token(tk: TokenKind<'_>) -> Option<Self> {
        match tk {
            TokenKind::Plus => Some(Self::Add),
            TokenKind::Minus => Some(Self::Sub),
            TokenKind::Star => Some(Self::Mul),
            TokenKind::Slash => Some(Self::Div),
            TokenKind::Percent => Some(Self::Rem),
            TokenKind::EqEq => Some(Self::Eq),
            TokenKind::BangEq => Some(Self::Ne),
            TokenKind::Gt => Some(Self::Gt),
            TokenKind::Ge => Some(Self::Ge),
            TokenKind::Lt => Some(Self::Lt),
            TokenKind::Le => Some(Self::Le),
            TokenKind::KwAnd => Some(Self::And),
            TokenKind::KwOr => Some(Self::Or),

            _ => None,
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::Rem => write!(f, "%"),
            Self::Eq => write!(f, "=="),
            Self::Ne => write!(f, "!="),
            Self::Gt => write!(f, ">"),
            Self::Ge => write!(f, ">="),
            Self::Lt => write!(f, "<"),
            Self::Le => write!(f, "<="),
            Self::And => write!(f, "and"),
            Self::Or => write!(f, "or"),
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
    pub const fn from_token(tk: TokenKind<'_>) -> Option<Self> {
        match tk {
            TokenKind::KwNot => Some(Self::Not),
            TokenKind::Minus => Some(Self::Neg),
            _ => None,
        }
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Not => write!(f, "not"),
            Self::Neg => write!(f, "-"),
        }
    }
}

impl TokenKind<'_> {
    #[must_use]
    pub const fn can_start_expr(&self) -> bool {
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
    pub const fn can_start_type(&self) -> bool {
        matches!(
            self,
            TokenKind::LParen | TokenKind::Ident(_) | TokenKind::KwInt | TokenKind::KwBool
        )
    }

    #[must_use]
    pub const fn can_start_pat(&self) -> bool {
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
    pub params: Box<[Rc<Ty>]>,
}

impl Constructor {
    #[must_use]
    pub const fn new(id: Symbol, params: Box<[Rc<Ty>]>) -> Self {
        Self { id, params }
    }
}

impl Display for Constructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)?;
        self.params.iter().try_for_each(|p| write!(f, " {p}"))
    }
}
