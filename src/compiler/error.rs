use super::{infer::Constr, token::TokenKind, types::Type};
use std::{fmt::Display, rc::Rc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexError {
    InvalidChar(char),
}

impl Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexError::InvalidChar(c) => write!(f, "invalid character '{c}'"),
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
            ParseError::LexError(lex_error) => lex_error.fmt(f),
            ParseError::UnexpectedEof => write!(f, "unexpected end-of-file"),
            ParseError::ExpectedToken(token_kind) => write!(f, "expected '{token_kind}'"),
            ParseError::ExpectedExpr => write!(f, "expected expression"),
            ParseError::ExpectedId => write!(f, "expected identifier"),
            ParseError::ExpectedType => write!(f, "expected type"),
            ParseError::ExpectedPattern => write!(f, "expected pattern"),
        }
    }
}
impl std::error::Error for ParseError {
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferError {
    Uninferable(Constr),
    Unbound(Rc<str>),
    Kind(Rc<Type>),
}

impl Display for InferError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferError::Uninferable(constr) => {
                write!(f, "expected '{}', got '{}'", constr.lhs(), constr.rhs())
            }
            InferError::Unbound(id) => write!(f, "unbound identifier: {id}"),
            InferError::Kind(kind) => write!(f, "kind error: {kind}"),
        }
    }
}

impl std::error::Error for InferError {
}
