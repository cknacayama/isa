use std::fmt::Display;

use crate::{span::*, token::TokenData, types::Type};

#[derive(Debug, Clone, PartialEq)]
pub enum ParseErrorData {
    InvalidEscape(char),
    InvalidChar(char),
    UnterminatedString,
    UnterminatedChar,

    ExpectedDecl,
    ExpectedIdent,
    ExpectedType,
    ExpectedInt,
    ExpectedExpr,
    UnexpectedEof,
    ExpectedToken(TokenData<'static>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    Mismatch(Type, Type),
    Expected(Type, Type),
    ExpectedOneOf(Vec<Type>, Type),
    ExpectedNumeric(Type),
    ExpectedProc(Type),
    ExpectedArray(Type),
    WrongArgCount(usize, usize),
    UnknownType,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub data: ParseErrorData,
    pub loc: Loc,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CheckErrorData {
    TypeError(TypeError),
    UndefinedSymbol(String),
    AlreadyDefinedLocal(String),
    AlreadyDefinedProc(String),
    AlreadyDefinedStruct(String),
    ExpectedLValue,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CheckError {
    pub data: CheckErrorData,
    pub span: Span,
}

pub type ParseResult<T> = Result<T, ParseError>;
pub type TypeResult<T> = Result<T, TypeError>;
pub type CheckResult<T> = Result<T, CheckError>;

impl ParseError {
    pub fn new(data: ParseErrorData, loc: Loc) -> Self {
        Self { data, loc }
    }
}

impl TypeError {
    pub fn into_check_error(self, span: Span) -> CheckError {
        CheckError::new(CheckErrorData::TypeError(self), span)
    }
}

impl CheckError {
    pub fn new(data: CheckErrorData, span: Span) -> Self {
        Self { data, span }
    }

    pub fn type_error(ty: TypeError, span: Span) -> Self {
        Self::new(CheckErrorData::TypeError(ty), span)
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use ParseErrorData::*;

        match &self.data {
            InvalidEscape(c) => write!(f, "invalid escape character: {}", c),
            InvalidChar(c) => write!(f, "invalid character: {}", c),
            UnterminatedString => write!(f, "unterminated string"),
            UnterminatedChar => write!(f, "unterminated char"),
            ExpectedIdent => write!(f, "expected identifier"),
            ExpectedExpr => write!(f, "expected expression"),
            ExpectedInt => write!(f, "expected integer"),
            UnexpectedEof => write!(f, "unexpected end of file"),
            ExpectedToken(token) => write!(f, "expected token: {:?}", token),
            ExpectedType => write!(f, "expected type"),
            ExpectedDecl => write!(f, "expected declaration"),
        }?;

        write!(f, " at {}", self.loc)
    }
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeError::*;
        match self {
            Mismatch(t1, t2) => write!(f, "mismatch ({} != {})", t1, t2),
            Expected(expected, actual) => write!(f, "expected {}, found {}", expected, actual),
            WrongArgCount(expected, actual) => {
                write!(f, "expected {} arguments, found {}", expected, actual)
            }
            ExpectedOneOf(expected, actual) => {
                write!(f, "expected one of: ")?;
                for (i, ty) in expected.iter().enumerate() {
                    write!(f, "{}", ty)?;
                    if i != expected.len() - 1 {
                        write!(f, " | ")?;
                    }
                }
                write!(f, ", found {}", actual)
            }
            ExpectedNumeric(actual) => write!(f, "expected numeric type, found {}", actual),
            ExpectedProc(actual) => write!(f, "expected proc type, found {}", actual),
            ExpectedArray(actual) => write!(f, "expected array type, found {}", actual),
            UnknownType => write!(f, "unknown type"),
        }
    }
}

impl std::fmt::Display for CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CheckErrorData::*;

        match &self.data {
            TypeError(err) => write!(f, "{}", err),
            UndefinedSymbol(name) => write!(f, "undefined symbol: {}", name),
            AlreadyDefinedLocal(name) => write!(f, "already defined local: {}", name),
            AlreadyDefinedProc(name) => write!(f, "already defined proc: {}", name),
            AlreadyDefinedStruct(name) => write!(f, "already defined struct: {}", name),
            ExpectedLValue => write!(f, "expected lvalue"),
        }?;

        write!(f, " at {}", self.span)
    }
}

impl std::error::Error for ParseError {
}

impl std::error::Error for TypeError {
}

impl std::error::Error for CheckError {
}

impl From<TypeError> for CheckErrorData {
    fn from(err: TypeError) -> Self {
        Self::TypeError(err)
    }
}
