use std::fmt::Display;

use crate::global::{Symbol, symbol};
use crate::span::{Span, Spanned};

#[derive(Clone, Copy, Debug, Eq, Default)]
pub struct Ident {
    pub ident: Symbol,
    pub span:  Span,
}

impl Ident {
    pub const fn new(ident: Symbol, span: Span) -> Self {
        Self { ident, span }
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
    }
}

impl std::hash::Hash for Ident {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
    }
}

pub type Token = Spanned<TokenKind>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenKind {
    Underscore,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    At,
    Eq,
    Bar,
    DotDot,
    DotDotEq,
    Arrow,
    Rocket,
    Comma,
    Semicolon,
    Colon,
    ColonColon,

    Integer(i64),
    Ident(Symbol),
    Operator(Symbol),
    Char(u8),

    KwTrue,
    KwFalse,

    KwType,
    KwAlias,
    KwLet,
    KwVal,
    KwIn,
    KwFn,
    KwModule,
    KwClass,
    KwInstance,
    KwOperator,

    KwInt,
    KwBool,
    KwChar,

    KwMatch,
    KwWith,
    KwIf,
    KwThen,
    KwElse,
}

impl TokenKind {
    #[must_use]
    pub fn keyword(s: &str) -> Self {
        match s {
            "true" => Self::KwTrue,
            "false" => Self::KwFalse,
            "type" => Self::KwType,
            "alias" => Self::KwAlias,
            "let" => Self::KwLet,
            "val" => Self::KwVal,
            "class" => Self::KwClass,
            "instance" => Self::KwInstance,
            "operator" => Self::KwOperator,
            "fn" => Self::KwFn,
            "match" => Self::KwMatch,
            "if" => Self::KwIf,
            "then" => Self::KwThen,
            "else" => Self::KwElse,
            "in" => Self::KwIn,
            "with" => Self::KwWith,
            "module" => Self::KwModule,
            "int" => Self::KwInt,
            "bool" => Self::KwBool,
            "char" => Self::KwChar,
            "_" => Self::Underscore,
            _ => Self::Ident(symbol!(s)),
        }
    }

    pub const fn operator_character(c: char) -> bool {
        matches!(
            c,
            '!' | '$' | '%' | '&' | '/' | '*' | '+' | '.' | '<' | '=' | '>' | '|' | '-'
        )
    }

    pub fn operator(op: &str) -> Self {
        match op {
            "=" => Self::Eq,
            "|" => Self::Bar,
            ".." => Self::DotDot,
            "..=" => Self::DotDotEq,
            "->" => Self::Arrow,
            "=>" => Self::Rocket,
            _ => Self::Operator(symbol!(op)),
        }
    }

    pub const fn as_operator(&self) -> Option<Symbol> {
        if let Self::Operator(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    pub const fn as_ident(&self) -> Option<Symbol> {
        if let Self::Ident(v) = self {
            Some(*v)
        } else {
            None
        }
    }
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Underscore => write!(f, "_"),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::LBracket => write!(f, "["),
            Self::RBracket => write!(f, "]"),
            Self::At => write!(f, "@"),
            Self::Bar => write!(f, "|"),
            Self::Comma => write!(f, ","),
            Self::Semicolon => write!(f, ";"),
            Self::Colon => write!(f, ":"),
            Self::ColonColon => write!(f, "::"),
            Self::DotDot => write!(f, ".."),
            Self::DotDotEq => write!(f, "..="),
            Self::Eq => write!(f, "="),
            Self::Arrow => write!(f, "->"),
            Self::Rocket => write!(f, "=>"),
            Self::Integer(v) => write!(f, "{v}"),
            Self::Ident(v) | Self::Operator(v) => write!(f, "{v}"),
            Self::Char(v) => write!(f, "{:?}", *v as char),
            Self::KwTrue => write!(f, "true"),
            Self::KwFalse => write!(f, "false"),
            Self::KwType => write!(f, "type"),
            Self::KwAlias => write!(f, "alias"),
            Self::KwLet => write!(f, "let"),
            Self::KwVal => write!(f, "val"),
            Self::KwIn => write!(f, "in"),
            Self::KwClass => write!(f, "class"),
            Self::KwInstance => write!(f, "instance"),
            Self::KwOperator => write!(f, "operator"),
            Self::KwFn => write!(f, "fn"),
            Self::KwModule => write!(f, "module"),
            Self::KwInt => write!(f, "int"),
            Self::KwBool => write!(f, "bool"),
            Self::KwChar => write!(f, "char"),
            Self::KwMatch => write!(f, "match"),
            Self::KwWith => write!(f, "with"),
            Self::KwIf => write!(f, "if"),
            Self::KwThen => write!(f, "then"),
            Self::KwElse => write!(f, "else"),
        }
    }
}
