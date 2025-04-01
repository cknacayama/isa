use std::fmt::Display;

use super::exhaust::pat::WitnessPat;
use super::infer::Constraint;
use super::token::TokenKind;
use super::types::Ty;
use crate::global::Symbol;
use crate::span::Span;

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
    ExpectedToken {
        expected: TokenKind,
        got:      TokenKind,
    },
    ExpectedExpr(TokenKind),
    ExpectedId(TokenKind),
    ExpectedInt(TokenKind),
    ExpectedType(TokenKind),
    ExpectedPattern(TokenKind),
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
            Self::ExpectedToken { expected, got } => {
                write!(f, "expected '{expected}', got '{got}'")
            }
            Self::ExpectedExpr(got) => write!(f, "expected expression, got '{got}'"),
            Self::ExpectedId(got) => write!(f, "expected identifier, got '{got}'"),
            Self::ExpectedInt(got) => write!(f, "expected integer literal, got '{got}'"),
            Self::ExpectedType(got) => write!(f, "expected type, got '{got}'"),
            Self::ExpectedPattern(got) => write!(f, "expected pattern, got '{got}'"),
        }
    }
}
impl std::error::Error for ParseError {
}

#[derive(Debug, Clone)]
pub enum InferErrorKind {
    Uninferable(Constraint),
    Unbound(Symbol),
    UnboundModule(Symbol),
    NotConstructor(Symbol),
    Kind(Ty),
}

impl Display for InferErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Uninferable(constr) => {
                write!(
                    f,
                    "expected expression of type `{}`, got `{}`",
                    constr.lhs(),
                    constr.rhs()
                )
            }
            Self::Unbound(id) => write!(f, "unbound identifier: {id}"),
            Self::UnboundModule(module) => write!(f, "unbound module: {module}"),
            Self::NotConstructor(name) => write!(f, "'{name}' is not a constructor"),
            Self::Kind(ty) => write!(f, "`{ty}` is not of kind *"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct InferError {
    kind: InferErrorKind,
    span: Span,
}

impl Display for InferError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind())
    }
}

impl InferError {
    #[must_use]
    pub const fn new(kind: InferErrorKind, span: Span) -> Self {
        Self { kind, span }
    }

    #[must_use]
    pub const fn kind(&self) -> &InferErrorKind {
        &self.kind
    }

    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct MatchNonExhaustive {
    witnesses: Vec<WitnessPat>,
    span:      Span,
}

impl MatchNonExhaustive {
    #[must_use]
    pub const fn new(witnesses: Vec<WitnessPat>, span: Span) -> Self {
        Self { witnesses, span }
    }

    #[must_use]
    pub fn witnessess(&self) -> &[WitnessPat] {
        &self.witnesses
    }

    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }
}

impl Display for MatchNonExhaustive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.witnessess().len() > 1 {
            write!(f, "patterns")?;
        } else {
            write!(f, "pattern")?;
        }
        write!(f, " not covered")
    }
}

impl std::error::Error for InferErrorKind {
}

impl std::error::Error for InferError {
}

impl std::error::Error for MatchNonExhaustive {
}
