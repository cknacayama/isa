use crate::error::{Span, Spanned};

use phf::{phf_map, Map};

static KEYWORDS_MAP: Map<&'static str, TokenData<'static>> = phf_map! {
    "proc" => TokenData::KwProc,
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

impl<'a> std::fmt::Display for TokenData<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TokenData::*;
        match self {
            LParen => write!(f, "("),
            RParen => write!(f, ")"),
            LBrace => write!(f, "{{"),
            RBrace => write!(f, "}}"),
            LBracket => write!(f, "["),
            RBracket => write!(f, "]"),

            Comma => write!(f, ","),
            Semicolon => write!(f, ";"),
            Colon => write!(f, ":"),
            Arrow => write!(f, "->"),
            Dot => write!(f, "."),

            Plus => write!(f, "+"),
            Minus => write!(f, "-"),
            Star => write!(f, "*"),
            Slash => write!(f, "/"),
            Percent => write!(f, "%"),
            Caret => write!(f, "^"),
            Amp => write!(f, "&"),
            Pipe => write!(f, "|"),
            Bang => write!(f, "!"),
            Tilde => write!(f, "~"),
            Question => write!(f, "?"),

            Equal => write!(f, "="),
            EqualEqual => write!(f, "=="),
            BangEqual => write!(f, "!="),
            Less => write!(f, "<"),
            LessEqual => write!(f, "<="),
            Greater => write!(f, ">"),
            GreaterEqual => write!(f, ">="),

            GreaterGreater => write!(f, ">>"),
            LessLess => write!(f, "<<"),

            AmpAmp => write!(f, "&&"),
            PipePipe => write!(f, "||"),

            Ident(ident) => write!(f, "{}", ident),
            Int(int) => write!(f, "{}", int),
            Float(float) => write!(f, "{}", float),
            Char(char) => write!(f, "'{}'", char),
            String(string) => write!(f, "\"{}\"", string),

            KwProc => write!(f, "proc"),
            KwLet => write!(f, "let"),
            KwMut => write!(f, "mut"),
            KwIf => write!(f, "if"),
            KwElse => write!(f, "else"),
            KwWhile => write!(f, "while"),
            KwReturn => write!(f, "return"),

            KwTrue => write!(f, "true"),
            KwFalse => write!(f, "false"),

            KwInt => write!(f, "int"),
            KwFloat => write!(f, "float"),
            KwChar => write!(f, "char"),
            KwBool => write!(f, "bool"),
            KwString => write!(f, "string"),
            KwUnit => write!(f, "unit"),
        }
    }
}

impl std::fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} = {}", self.span, self.data)
    }
}
