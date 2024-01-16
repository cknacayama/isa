use crate::{token::TokenData, types::TypeError};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Loc {
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    pub start: Loc,
    pub end: Loc,
}

pub trait Spanned {
    fn span(&self) -> Span;
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseErrorData {
    InvalidEscape(char),
    InvalidChar(char),
    UnterminatedString,
    UnterminatedChar,

    ExpectedDecl,
    ExpectedIdent,
    ExpectedType,
    ExpectedExpr,
    UnexpectedEof,
    ExpectedToken(TokenData<'static>),

    TypeError(TypeError),

    AlreadyDefinedProc(String),
    AlreadyDefinedLocal(String),

    UndefinedProc(String),
    UndefinedLocal(String),
    WrongArgCount(usize, usize),

    ReturnOutsideProc,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub data: ParseErrorData,
    pub loc: Loc,
}

pub type ParseResult<T> = Result<T, ParseError>;

impl PartialOrd for Loc {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Loc {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.line == other.line {
            self.col.cmp(&other.col)
        } else {
            self.line.cmp(&other.line)
        }
    }
}

impl Spanned for Span {
    #[inline]
    fn span(&self) -> Span {
        *self
    }
}

impl Span {
    #[inline]
    pub fn new(start: Loc, end: Loc) -> Self {
        Self { start, end }
    }

    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            start: std::cmp::min(self.start, other.start),
            end: std::cmp::max(self.end, other.end),
        }
    }
}

impl ParseError {
    pub fn new(data: ParseErrorData, loc: Loc) -> Self {
        Self { data, loc }
    }
}

impl std::fmt::Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.line == 0 {
            return write!(f, "eof");
        }

        write!(f, "{}:{}", self.line, self.col)
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({})..({})", self.start, self.end)
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use ParseErrorData::*;
        match &self.data {
            InvalidEscape(c) => write!(f, "invalid escape character: {}", c),
            InvalidChar(c) => write!(f, "invalid character: {}", c),
            UnterminatedString => write!(f, "unterminated string"),
            UnterminatedChar => write!(f, "unterminated char"),
            ExpectedIdent => write!(f, "expected identifier"),
            ExpectedExpr => write!(f, "expected expression"),
            UnexpectedEof => write!(f, "unexpected end of file"),
            ExpectedToken(token) => write!(f, "expected token: {:?}", token),
            ExpectedType => write!(f, "expected type"),
            ExpectedDecl => write!(f, "expected declaration"),
            AlreadyDefinedProc(name) => write!(f, "procedure already defined: {}", name),
            AlreadyDefinedLocal(name) => write!(f, "local already defined: {}", name),
            UndefinedLocal(name) => write!(f, "undefined local: {}", name),
            UndefinedProc(name) => write!(f, "undefined procedure: {}", name),
            WrongArgCount(expected, actual) => write!(
                f,
                "wrong number of arguments: expected {}, found {}",
                expected, actual
            ),
            ReturnOutsideProc => write!(f, "return outside procedure"),
            TypeError(err) => write!(f, "type error: {}", err),
        }?;
        write!(f, " at {}", self.loc)
    }
}

impl std::error::Error for ParseError {
}
