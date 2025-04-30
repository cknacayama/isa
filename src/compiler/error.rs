use std::fmt::Display;

use codespan_reporting::diagnostic::Label;

use super::ast::Path;
use super::exhaust::pat::WitnessPat;
use super::infer::{Constraint, Subs};
use super::token::{Ident, TokenKind};
use super::types::Ty;
use crate::global::Symbol;
use crate::span::Span;

#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
pub enum LexError {
    InvalidChar(char),
    UnterminatedChar,
    UnterminatedString,
    EmptyChar,
    UnrecognizedEscape(char),
}

impl Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidChar(c) => write!(f, "invalid character `{c}`"),
            Self::UnterminatedChar => write!(f, "unterminated character"),
            Self::UnterminatedString => write!(f, "unterminated string"),
            Self::EmptyChar => write!(f, "empty character"),
            Self::UnrecognizedEscape(c) => write!(f, "unrecognized escape sequence \\{c}"),
        }
    }
}

impl std::error::Error for LexError {
}

#[derive(Debug, Clone, Copy)]
pub enum ParseError {
    LexError(LexError),
    UnexpectedEof,
    ExpectedToken {
        expected: TokenKind,
        got:      Option<TokenKind>,
    },
    ExpectedExpr(TokenKind),
    ExpectedId(TokenKind),
    ExpectedInt(TokenKind),
    ExpectedType(TokenKind),
    ExpectedPattern(TokenKind),
    PrecendenceLimit(i64),
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
                write!(f, "expected `{expected}`")?;
                got.map_or(Ok(()), |got| write!(f, ", got `{got}`"))
            }
            Self::ExpectedExpr(got) => write!(f, "expected expression, got `{got}`"),
            Self::ExpectedId(got) => write!(f, "expected identifier, got `{got}`"),
            Self::ExpectedInt(got) => write!(f, "expected integer literal, got `{got}`"),
            Self::ExpectedType(got) => write!(f, "expected type, got `{got}`"),
            Self::ExpectedPattern(got) => write!(f, "expected pattern, got `{got}`"),
            Self::PrecendenceLimit(prec) => write!(f, "precedence limit exceded ({prec} > 255)"),
        }
    }
}
impl std::error::Error for ParseError {
}

#[derive(Debug, Clone)]
pub struct Uninferable {
    constr: Constraint,

    /// Substitutions applied up until the error
    subs: Box<[Subs]>,
}

impl Uninferable {
    pub fn new(constr: Constraint, subs: Vec<Subs>) -> Self {
        Self {
            constr,
            subs: subs.into_boxed_slice(),
        }
    }

    pub const fn constr(&self) -> &Constraint {
        &self.constr
    }

    pub fn subs(&self) -> &[Subs] {
        &self.subs
    }
}

#[derive(Debug, Clone)]
pub enum CheckErrorKind {
    InvalidPath(Path),
    InvalidImport(Path),
    Unbound(Symbol),
    NotModule(Symbol),
    SameNameConstructor(Symbol, Span),
    SameNameType(Symbol, Span),
    NotConstructor(Ty),
    NotConstructorName(Symbol),
    NotClass(Symbol),
    NotInstance(Ty, Path),
    MultipleInstances(Path, Ty, Span),
    Kind(Ty),
}

#[derive(Debug, Clone)]
pub struct CheckError {
    kind: CheckErrorKind,
    span: Span,
}

pub type CheckResult<T> = Result<T, CheckError>;

impl CheckError {
    #[must_use]
    pub const fn new(kind: CheckErrorKind, span: Span) -> Self {
        Self { kind, span }
    }

    #[must_use]
    pub const fn kind(&self) -> &CheckErrorKind {
        &self.kind
    }

    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }

    pub fn from_ident<F>(constructor: F, id: Ident) -> Self
    where
        F: FnOnce(Symbol) -> CheckErrorKind,
    {
        Self::new(constructor(id.ident), id.span)
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

    pub fn as_primary(&self) -> Label<usize> {
        Label::primary(self.span().file_id(), self.span()).with_message(self.message())
    }

    pub fn as_secondary(&self) -> Label<usize> {
        Label::secondary(self.span().file_id(), self.span()).with_message(self.message())
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

impl From<CheckError> for IsaError {
    fn from(value: CheckError) -> Self {
        match value.kind() {
            CheckErrorKind::InvalidPath(path) => {
                let message = format!("invalid path: `{path}`");
                let label = DiagnosticLabel::new("not valid", value.span());
                Self::new(message, label, Vec::new())
            }
            CheckErrorKind::InvalidImport(path) => {
                let message = format!("invalid import: `{path}`");
                let label = DiagnosticLabel::new("not valid", value.span());
                Self::new(message, label, Vec::new())
            }
            CheckErrorKind::Unbound(symbol) => {
                let message = format!("undefined identifier: `{symbol}`");
                let label = DiagnosticLabel::new("not defined", value.span());
                Self::new(message, label, Vec::new())
            }
            CheckErrorKind::SameNameConstructor(name, span) => {
                let label = DiagnosticLabel::new(
                    format!("constructor `{name}` already defined"),
                    value.span(),
                );
                let snd = DiagnosticLabel::new("previously defined here", *span);
                Self::new("constructor with same name", label, vec![snd])
            }
            CheckErrorKind::SameNameType(name, span) => {
                let label =
                    DiagnosticLabel::new(format!("type `{name}` already defined"), value.span());
                let snd = DiagnosticLabel::new("previously defined here", *span);
                Self::new("type with same name", label, vec![snd])
            }
            CheckErrorKind::NotConstructor(ty) => {
                let message = format!("not a constructor: `{ty}`");
                let label = DiagnosticLabel::new("expected a value constructor", value.span());
                Self::new(message, label, Vec::new())
            }
            CheckErrorKind::NotConstructorName(ty) => {
                let message = format!("not a constructor: `{ty}`");
                let label = DiagnosticLabel::new("expected a value constructor", value.span());
                Self::new(message, label, Vec::new())
            }
            CheckErrorKind::NotModule(name) => {
                let message = format!("not a module: `{name}`");
                let label = DiagnosticLabel::new("expected a module", value.span());
                Self::new(message, label, Vec::new())
            }
            CheckErrorKind::NotClass(name) => {
                let message = format!("not a class: `{name}`");
                let label = DiagnosticLabel::new("expected a class", value.span());
                Self::new(message, label, Vec::new())
            }
            CheckErrorKind::NotInstance(ty, class) => {
                let label = DiagnosticLabel::new(
                    format!("expected `{ty}` to be instance of `{class}`"),
                    value.span(),
                );
                Self::new("not a instance", label, Vec::new())
            }
            CheckErrorKind::Kind(ty) => {
                let label = DiagnosticLabel::new("pattern should have kind *", value.span());
                let snd_label =
                    DiagnosticLabel::new(format!("this is of type `{ty}`"), value.span());
                Self::new("kind error", label, vec![snd_label])
            }
            CheckErrorKind::MultipleInstances(ident, ty, span) => {
                let label = DiagnosticLabel::new(
                    format!("multiple instances of `{ident}` for `{ty}`"),
                    value.span(),
                );
                let snd_label = DiagnosticLabel::new("previous instantiation", *span);
                Self::new("multiple instances", label, vec![snd_label])
            }
        }
    }
}

impl From<Uninferable> for IsaError {
    fn from(value: Uninferable) -> Self {
        match value.constr() {
            Constraint::Eq(value) => {
                let fst = DiagnosticLabel::new(
                    format!("expected `{}`, got `{}`", value.lhs(), value.rhs()),
                    value.span(),
                );
                Self::new("type mismatch", fst, Vec::new())
            }
            Constraint::Class(class) => {
                let fst = DiagnosticLabel::new(
                    format!(
                        "type `{}` is not instance of class `{}`",
                        class.ty(),
                        class.class()
                    ),
                    class.span(),
                );
                Self::new("class mismatch", fst, Vec::new())
            }
        }
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

impl std::error::Error for Uninferable {
}

impl std::error::Error for IsaError {
}

impl std::error::Error for MatchNonExhaustive {
}
