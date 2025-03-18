use std::rc::Rc;

use thiserror::Error;

use crate::compiler::token::TokenKind;

use super::infer::Constr;

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexError {
    #[error("invalid character '{0}'")]
    InvalidChar(char),
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseError {
    #[error("{0}")]
    LexError(#[from] LexError),
    #[error("unexpected end-of-file")]
    UnexpectedEof,
    #[error("expected '{0}'")]
    ExpectedToken(TokenKind<'static>),
    #[error("expected expression")]
    ExpectedExpr,
    #[error("expected identifier")]
    ExpectedId,
    #[error("expected type")]
    ExpectedType,
    #[error("expected pattern")]
    ExpectedPattern,
}

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum InferError {
    #[error("uninferable: {0}")]
    Uninferable(Constr),
    #[error("unbound identifier: {0}")]
    Unbound(Rc<str>),
}
