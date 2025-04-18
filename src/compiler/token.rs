use std::fmt::Display;

use crate::global::Symbol;
use crate::span::{Span, Spanned};

#[derive(Clone, Copy, Debug, Eq, Default)]
pub struct Ident {
    pub ident: Symbol,
    pub span:  Span,
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
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Eq,
    Bang,
    BangEq,
    Gt,
    Ge,
    Lt,
    Le,
    Pipe,

    Underscore,

    LParen,
    RParen,
    LBrace,
    RBrace,

    Bar,
    BarBar,
    Amp,
    AmpAmp,

    Arrow,
    Rocket,
    Comma,
    Semicolon,
    Colon,
    ColonColon,
    Dot,
    DotDot,
    DotDotEq,

    Integer(i64),
    Ident(Symbol),
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
    pub fn keyword(s: &str) -> Option<Self> {
        match s {
            "true" => Some(Self::KwTrue),
            "false" => Some(Self::KwFalse),
            "type" => Some(Self::KwType),
            "alias" => Some(Self::KwAlias),
            "let" => Some(Self::KwLet),
            "val" => Some(Self::KwVal),
            "class" => Some(Self::KwClass),
            "instance" => Some(Self::KwInstance),
            "fn" => Some(Self::KwFn),
            "match" => Some(Self::KwMatch),
            "if" => Some(Self::KwIf),
            "then" => Some(Self::KwThen),
            "else" => Some(Self::KwElse),
            "in" => Some(Self::KwIn),
            "with" => Some(Self::KwWith),
            "module" => Some(Self::KwModule),
            "int" => Some(Self::KwInt),
            "bool" => Some(Self::KwBool),
            "char" => Some(Self::KwChar),
            "_" => Some(Self::Underscore),
            _ => None,
        }
    }
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Plus => write!(f, "+"),
            Self::Minus => write!(f, "-"),
            Self::Star => write!(f, "*"),
            Self::Slash => write!(f, "/"),
            Self::Percent => write!(f, "%"),
            Self::Eq => write!(f, "="),
            Self::Bang => write!(f, "!"),
            Self::BangEq => write!(f, "!="),
            Self::Gt => write!(f, ">"),
            Self::Ge => write!(f, ">="),
            Self::Lt => write!(f, "<"),
            Self::Le => write!(f, "<="),
            Self::Pipe => write!(f, "|>"),
            Self::Underscore => write!(f, "_"),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::Bar => write!(f, "|"),
            Self::BarBar => write!(f, "||"),
            Self::Amp => write!(f, "&"),
            Self::AmpAmp => write!(f, "&&"),
            Self::Comma => write!(f, ","),
            Self::Semicolon => write!(f, ";"),
            Self::Colon => write!(f, ":"),
            Self::ColonColon => write!(f, "::"),
            Self::Dot => write!(f, "."),
            Self::DotDot => write!(f, ".."),
            Self::DotDotEq => write!(f, "..="),
            Self::Arrow => write!(f, "->"),
            Self::Rocket => write!(f, "=>"),
            Self::Integer(v) => write!(f, "{v}"),
            Self::Ident(v) => write!(f, "{v}"),
            Self::Char(v) => write!(f, "{:?}", *v as char),
            Self::KwTrue => write!(f, "true"),
            Self::KwFalse => write!(f, "false"),
            Self::KwType => write!(f, "type"),
            Self::KwAlias => write!(f, "alias"),
            Self::KwLet => write!(f, "let"),
            Self::KwVal => write!(f, "val"),
            Self::KwIn => write!(f, "in"),
            Self::KwClass => write!(f, "trait"),
            Self::KwInstance => write!(f, "impl"),
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
