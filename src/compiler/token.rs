use std::fmt::Display;

use crate::span::Spanned;

pub type Token<'a> = Spanned<TokenKind<'a>>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenKind<'a> {
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Eq,
    EqEq,
    Bang,
    BangEq,
    Gt,
    Ge,
    Lt,
    Le,

    Underscore,

    LParen,
    RParen,

    Bar,

    Arrow,
    Comma,
    Semicolon,

    Integer(&'a str),
    Ident(&'a str),

    KwTrue,
    KwFalse,

    KwType,
    KwLet,
    KwVal,
    KwIn,
    KwFn,
    KwModule,

    KwInt,
    KwBool,

    KwAnd,
    KwOr,
    KwNot,

    KwMatch,
    KwWith,
    KwIf,
    KwThen,
    KwElse,
}

impl TokenKind<'_> {
    #[must_use]
    pub fn keyword(s: &str) -> Option<TokenKind<'static>> {
        match s {
            "true" => Some(TokenKind::KwTrue),
            "false" => Some(TokenKind::KwFalse),
            "type" => Some(TokenKind::KwType),
            "let" => Some(TokenKind::KwLet),
            "val" => Some(TokenKind::KwVal),
            "fn" => Some(TokenKind::KwFn),
            "and" => Some(TokenKind::KwAnd),
            "or" => Some(TokenKind::KwOr),
            "not" => Some(TokenKind::KwNot),
            "match" => Some(TokenKind::KwMatch),
            "if" => Some(TokenKind::KwIf),
            "then" => Some(TokenKind::KwThen),
            "else" => Some(TokenKind::KwElse),
            "in" => Some(TokenKind::KwIn),
            "with" => Some(TokenKind::KwWith),
            "module" => Some(TokenKind::KwModule),
            "int" => Some(TokenKind::KwInt),
            "bool" => Some(TokenKind::KwBool),
            "_" => Some(TokenKind::Underscore),
            _ => None,
        }
    }
}

impl Display for TokenKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Percent => write!(f, "%"),
            TokenKind::Eq => write!(f, "="),
            TokenKind::EqEq => write!(f, "=="),
            TokenKind::Bang => write!(f, "!"),
            TokenKind::BangEq => write!(f, "!="),
            TokenKind::Gt => write!(f, ">"),
            TokenKind::Ge => write!(f, ">="),
            TokenKind::Lt => write!(f, "<"),
            TokenKind::Le => write!(f, "<="),
            TokenKind::Underscore => write!(f, "_"),
            TokenKind::LParen => write!(f, "("),
            TokenKind::RParen => write!(f, ")"),
            TokenKind::Bar => write!(f, "|"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Semicolon => write!(f, ";"),
            TokenKind::Arrow => write!(f, "->"),
            TokenKind::Integer(v) | TokenKind::Ident(v) => write!(f, "{v}"),
            TokenKind::KwTrue => write!(f, "true"),
            TokenKind::KwFalse => write!(f, "false"),
            TokenKind::KwType => write!(f, "type"),
            TokenKind::KwLet => write!(f, "let"),
            TokenKind::KwVal => write!(f, "val"),
            TokenKind::KwIn => write!(f, "in"),
            TokenKind::KwFn => write!(f, "fn"),
            TokenKind::KwModule => write!(f, "module"),
            TokenKind::KwInt => write!(f, "int"),
            TokenKind::KwBool => write!(f, "bool"),
            TokenKind::KwAnd => write!(f, "and"),
            TokenKind::KwOr => write!(f, "or"),
            TokenKind::KwNot => write!(f, "not"),
            TokenKind::KwMatch => write!(f, "match"),
            TokenKind::KwWith => write!(f, "with"),
            TokenKind::KwIf => write!(f, "if"),
            TokenKind::KwThen => write!(f, "then"),
            TokenKind::KwElse => write!(f, "else"),
        }
    }
}
