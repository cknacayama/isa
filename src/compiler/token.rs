use std::fmt::Display;

use crate::global::Symbol;
use crate::span::Spand;

pub type Token = Spand<TokenKind>;

#[derive(Debug, Clone, Copy, PartialEq)]
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

    Backslash,

    Integer(i64),
    Real(f64),
    Ident(Symbol),
    Operator(Symbol),
    String(Symbol),
    Char(u8),

    KwTrue,
    KwFalse,

    KwType,
    KwAlias,
    KwLet,
    KwVal,
    KwIn,
    KwModule,
    KwClass,
    KwInstance,
    KwInfix,
    KwInfixl,
    KwInfixr,
    KwPrefix,

    KwSelf,
    KwInt,
    KwBool,
    KwChar,
    KwReal,

    KwMatch,
    KwWith,
    KwIf,
    KwThen,
    KwElse,
}

impl std::hash::Hash for TokenKind {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}

impl TokenKind {
    #[must_use]
    pub fn keyword(s: &str) -> Self {
        match s {
            "_" => Self::Underscore,
            "let" => Self::KwLet,
            "val" => Self::KwVal,
            "if" => Self::KwIf,
            "then" => Self::KwThen,
            "true" => Self::KwTrue,
            "false" => Self::KwFalse,
            "int" => Self::KwInt,
            "bool" => Self::KwBool,
            "char" => Self::KwChar,
            "real" => Self::KwReal,
            "type" => Self::KwType,
            "alias" => Self::KwAlias,
            "class" => Self::KwClass,
            "instance" => Self::KwInstance,
            "infix" => Self::KwInfix,
            "infixl" => Self::KwInfixl,
            "infixr" => Self::KwInfixr,
            "prefix" => Self::KwPrefix,
            "match" => Self::KwMatch,
            "else" => Self::KwElse,
            "in" => Self::KwIn,
            "with" => Self::KwWith,
            "module" => Self::KwModule,
            "Self" => Self::KwSelf,
            _ => Self::Ident(Symbol::intern(s)),
        }
    }

    pub const fn identifier_character(c: char) -> bool {
        c == '_' || c.is_ascii_alphanumeric()
    }

    pub const fn operator_character(c: char) -> bool {
        matches!(
            c,
            '!' | '?' | '^' | '$' | '%' | '&' | '/' | '*' | '+' | '.' | '<' | '=' | '>' | '|' | '-'
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
            _ => Self::Operator(Symbol::intern(op)),
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
            Self::Underscore => write!(f, "`_`"),
            Self::LParen => write!(f, "`(`"),
            Self::RParen => write!(f, "`)`"),
            Self::LBrace => write!(f, "`{{`"),
            Self::RBrace => write!(f, "`}}`"),
            Self::LBracket => write!(f, "`[`"),
            Self::RBracket => write!(f, "`]`"),
            Self::At => write!(f, "`@`"),
            Self::Bar => write!(f, "`|`"),
            Self::Comma => write!(f, "`,`"),
            Self::Semicolon => write!(f, "`;`"),
            Self::Colon => write!(f, "`:`"),
            Self::ColonColon => write!(f, "`::`"),
            Self::DotDot => write!(f, "`..`"),
            Self::DotDotEq => write!(f, "`..=`"),
            Self::Eq => write!(f, "`=`"),
            Self::Arrow => write!(f, "`->`"),
            Self::Rocket => write!(f, "`=>`"),
            Self::Backslash => write!(f, "`\\`"),
            Self::Integer(_) => write!(f, "integer"),
            Self::Real(_) => write!(f, "real"),
            Self::String(_) => write!(f, "string"),
            Self::Ident(_) => write!(f, "identifier"),
            Self::Operator(_) => write!(f, "operator"),
            Self::Char(_) => write!(f, "character"),
            Self::KwTrue => write!(f, "`true`"),
            Self::KwFalse => write!(f, "`false`"),
            Self::KwType => write!(f, "`type`"),
            Self::KwAlias => write!(f, "`alias`"),
            Self::KwLet => write!(f, "`let`"),
            Self::KwVal => write!(f, "`val`"),
            Self::KwIn => write!(f, "`in`"),
            Self::KwClass => write!(f, "`class`"),
            Self::KwInstance => write!(f, "`instance`"),
            Self::KwInfix => write!(f, "`infix`"),
            Self::KwInfixl => write!(f, "`infixl`"),
            Self::KwInfixr => write!(f, "`infixr`"),
            Self::KwPrefix => write!(f, "`prefix`"),
            Self::KwModule => write!(f, "`module`"),
            Self::KwSelf => write!(f, "`Self`"),
            Self::KwInt => write!(f, "`int`"),
            Self::KwBool => write!(f, "`bool`"),
            Self::KwChar => write!(f, "`char`"),
            Self::KwReal => write!(f, "`real`"),
            Self::KwMatch => write!(f, "`match`"),
            Self::KwWith => write!(f, "`with`"),
            Self::KwIf => write!(f, "`if`"),
            Self::KwThen => write!(f, "`then`"),
            Self::KwElse => write!(f, "`else`"),
        }
    }
}
