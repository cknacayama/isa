use crate::span::{Span, Spanned};

use phf::{phf_map, Map};

static KEYWORDS_MAP: Map<&'static str, TokenData<'static>> = phf_map! {
    "proc" => TokenData::KwProc,
    "struct" => TokenData::KwStruct,
    "let" => TokenData::KwLet,
    "mut" => TokenData::KwMut,
    "if" => TokenData::KwIf,
    "else" => TokenData::KwElse,
    "while" => TokenData::KwWhile,
    "return" => TokenData::KwReturn,

    // literals
    "true" => TokenData::KwTrue,
    "false" => TokenData::KwFalse,

    // types
    "int" => TokenData::KwInt,
    "float" => TokenData::KwFloat,
    "char" => TokenData::KwChar,
    "bool" => TokenData::KwBool,
    "string" => TokenData::KwString,
    "unit" => TokenData::KwUnit,
};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenData<'a> {
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    Comma,
    Semicolon,
    Colon,
    Arrow,
    Dot,

    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Caret,
    Amp,
    Pipe,
    Bang,
    Tilde,
    Question,

    Equal,
    EqualEqual,
    BangEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    GreaterGreater,
    LessLess,

    AmpAmp,
    PipePipe,

    Ident(&'a str),
    Int(u64),
    Float(f64),
    Char(char),
    String(&'a str),

    KwProc,
    KwStruct,
    KwLet,
    KwMut,
    KwIf,
    KwElse,
    KwWhile,
    KwReturn,

    KwTrue,
    KwFalse,

    KwInt,
    KwFloat,
    KwChar,
    KwBool,
    KwString,
    KwUnit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token<'a> {
    pub data: TokenData<'a>,
    pub span: Span,
}

impl Spanned for Token<'_> {
    #[inline(always)]
    fn span(&self) -> Span {
        self.span
    }
}

impl<'a> Token<'a> {
    pub fn new(data: TokenData<'a>, span: Span) -> Self {
        Self { data, span }
    }

    pub fn get_keyword(ident: &str) -> Option<TokenData<'static>> {
        KEYWORDS_MAP.get(ident).copied()
    }
}
