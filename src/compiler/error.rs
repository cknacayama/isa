use crate::global::Symbol;

use super::{infer::Constr, token::TokenKind, types::Ty};
use std::{fmt::Display, rc::Rc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexError {
    InvalidChar(char),
}

impl Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidChar(c) => write!(f, "invalid character '{c}'"),
        }
    }
}

impl std::error::Error for LexError {
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseError {
    LexError(LexError),
    UnexpectedEof,
    ExpectedToken(TokenKind<'static>),
    ExpectedExpr,
    ExpectedId,
    ExpectedType,
    ExpectedPattern,
}

impl From<LexError> for ParseError {
    fn from(value: LexError) -> Self {
        Self::LexError(value)
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LexError(lex_error) => lex_error.fmt(f),
            Self::UnexpectedEof => write!(f, "unexpected end-of-file"),
            Self::ExpectedToken(token_kind) => write!(f, "expected '{token_kind}'"),
            Self::ExpectedExpr => write!(f, "expected expression"),
            Self::ExpectedId => write!(f, "expected identifier"),
            Self::ExpectedType => write!(f, "expected type"),
            Self::ExpectedPattern => write!(f, "expected pattern"),
        }
    }
}
impl std::error::Error for ParseError {
}

#[derive(Debug, Clone)]
pub enum InferError {
    Uninferable(Constr),
    Unbound(Symbol),
    Kind(Rc<Ty>),
}

impl Display for InferError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Uninferable(constr) => {
                write!(f, "expected '{}', got '{}'", constr.lhs(), constr.rhs())
            }
            Self::Unbound(id) => write!(f, "unbound identifier: {id}"),
            Self::Kind(kind) => write!(f, "kind error: {kind}"),
        }
    }
}

impl std::error::Error for InferError {
}
