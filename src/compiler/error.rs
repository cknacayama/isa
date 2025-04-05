use std::fmt::Display;

use codespan_reporting::diagnostic::Label;

use super::exhaust::pat::WitnessPat;
use super::infer::{EqConstraint, Subs};
use super::token::TokenKind;
use super::types::Ty;
use crate::global::Symbol;
use crate::span::Span;

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexError {
    InvalidChar(char),
    UnterminatedChar,
    EmptyChar,
    UnrecognizedEscape,
}

impl Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidChar(c) => write!(f, "invalid character '{c}'"),
            Self::UnterminatedChar => write!(f, "unterminated character"),
            Self::EmptyChar => write!(f, "empty character"),
            Self::UnrecognizedEscape => write!(f, "unrecognized escape sequence"),
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
pub struct Uninferable {
    constr: EqConstraint,

    /// Substitutions applied up until the error
    subs: Vec<Subs>,
}

impl Uninferable {
    pub const fn new(constr: EqConstraint, subs: Vec<Subs>) -> Self {
        Self { constr, subs }
    }

    pub const fn constr(&self) -> &EqConstraint {
        &self.constr
    }

    pub fn subs(&self) -> &[Subs] {
        &self.subs
    }
}

#[derive(Debug, Clone)]
pub enum InferErrorKind {
    Unbound(Symbol),
    UnboundModule(Symbol),
    NotConstructor(Ty),
    Kind(Ty),
}

impl Display for InferErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unbound(id) => write!(f, "unbound identifier: {id}"),
            Self::UnboundModule(module) => write!(f, "unbound module: {module}"),
            Self::NotConstructor(name) => write!(f, "'{name}' is not a constructor"),
            Self::Kind(ty) => write!(f, "{ty} is not of kind *"),
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
pub struct DiagnosticLabel {
    message: String,
    span:    Span,
}

impl DiagnosticLabel {
    #[allow(clippy::needless_pass_by_value)]
    pub fn new(message: impl ToString, span: Span) -> Self {
        Self {
            message: message.to_string(),
            span,
        }
    }

    pub fn as_primary<FileId>(&self, file_id: FileId) -> Label<FileId> {
        Label::primary(file_id, self.span()).with_message(self.message())
    }

    pub fn as_secondary<FileId>(&self, file_id: FileId) -> Label<FileId> {
        Label::secondary(file_id, self.span()).with_message(self.message())
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub const fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct IsaError {
    message:       String,
    primary_label: DiagnosticLabel,
    labels:        Vec<DiagnosticLabel>,
    note:          Option<String>,
}

impl From<InferError> for IsaError {
    fn from(value: InferError) -> Self {
        match value.kind() {
            InferErrorKind::Unbound(symbol) => {
                let message = format!("undefined identifier {symbol}");
                let label = DiagnosticLabel::new("not previously defined", value.span());
                Self::new(message, label, Vec::new())
            }
            InferErrorKind::UnboundModule(symbol) => {
                let label = DiagnosticLabel::new(
                    format!("module{symbol} not previously defined"),
                    value.span(),
                );
                Self::new("undefined module", label, Vec::new())
            }
            InferErrorKind::NotConstructor(ty) => {
                let message = format!("{ty} is not a constructor");
                let label = DiagnosticLabel::new("expected a value constructor", value.span());
                Self::new(message, label, Vec::new())
            }
            InferErrorKind::Kind(ty) => {
                let label = DiagnosticLabel::new("pattern should have kind *", value.span());
                let snd_label = DiagnosticLabel::new(format!("this is of type {ty}"), value.span());
                Self::new("not matchable", label, vec![snd_label])
            }
        }
    }
}

impl From<Uninferable> for IsaError {
    fn from(value: Uninferable) -> Self {
        let fst = DiagnosticLabel::new(
            format!(
                "expected {}, got {}",
                value.constr().lhs(),
                value.constr().rhs()
            ),
            value.constr().span(),
        );
        Self::new("type mismatch", fst, Vec::new())
    }
}

impl IsaError {
    #[allow(clippy::needless_pass_by_value)]
    pub fn new(
        message: impl ToString,
        primary_label: DiagnosticLabel,
        labels: Vec<DiagnosticLabel>,
    ) -> Self {
        Self {
            message: message.to_string(),
            primary_label,
            labels,
            note: None,
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    pub fn with_note(self, note: impl ToString) -> Self {
        Self {
            note: Some(note.to_string()),
            ..self
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    pub fn with_label(mut self, label: DiagnosticLabel) -> Self {
        self.labels.push(label);
        self
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub const fn primary_label(&self) -> &DiagnosticLabel {
        &self.primary_label
    }

    pub fn labels(&self) -> &[DiagnosticLabel] {
        &self.labels
    }

    pub fn note(&self) -> Option<&str> {
        self.note.as_deref()
    }
}

impl Display for Uninferable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "uniferable")
    }
}

impl Display for IsaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.message.fmt(f)
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

impl std::error::Error for Uninferable {
}

impl std::error::Error for IsaError {
}

impl std::error::Error for MatchNonExhaustive {
}
