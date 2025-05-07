use std::str::Chars;

use super::error::LexError;
use super::token::{Token, TokenKind};
use crate::span::{Span, SpanData, Spanned};

const EOF: char = '\0';

#[derive(Debug)]
pub struct Lexer<'a> {
    file_id: usize,
    chars:   Chars<'a>,
    input:   &'a str,
    start:   usize,
    cur:     usize,
}

pub type LexResult<T> = Result<T, Spanned<LexError>>;

impl<'a> Lexer<'a> {
    #[must_use]
    pub fn new(file_id: usize, input: &'a str) -> Self {
        Self {
            file_id,
            input,
            chars: input.chars(),
            start: 0,
            cur: 0,
        }
    }

    fn first(&self) -> char {
        self.chars.clone().next().unwrap_or(EOF)
    }

    fn second(&self) -> char {
        let mut iter = self.chars.clone();
        iter.next();
        iter.next().unwrap_or(EOF)
    }

    fn is_eof(&self) -> bool {
        self.chars.as_str().is_empty()
    }

    fn bump(&mut self) -> Option<char> {
        self.cur += 1;
        self.chars.next()
    }

    fn bump_twice(&mut self) -> Option<(char, char)> {
        self.cur += 2;
        let c1 = self.chars.next()?;
        let c2 = self.chars.next()?;
        Some((c1, c2))
    }

    fn match_cur(&mut self, to_match: char) -> bool {
        if self.first() == to_match {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_while<P>(&mut self, pred: P)
    where
        P: Fn(char) -> bool,
    {
        while pred(self.first()) && !self.is_eof() {
            self.bump();
        }
    }

    fn make_token(&self, kind: TokenKind) -> Token {
        let span = SpanData::new(self.file_id, self.start, self.cur);
        let span = Span::intern(span);
        Token::new(kind, span)
    }

    fn make_err(&self, kind: LexError) -> Spanned<LexError> {
        let span = SpanData::new(self.file_id, self.start, self.cur);
        let span = Span::intern(span);
        Spanned::new(kind, span)
    }

    fn skip_whitespace(&mut self) {
        while !self.is_eof() {
            match self.first() {
                '/' if self.second() == '/' => {
                    self.bump_twice();
                    self.eat_while(|c| c != '\n');
                }
                c if c.is_ascii_whitespace() => {
                    self.bump();
                }
                _ => break,
            }
        }
    }

    fn number(&mut self) -> Token {
        self.eat_while(|c| c.is_ascii_digit());

        if self.first() == '.' && self.second().is_ascii_digit() {
            self.bump_twice();
            self.eat_while(|c| c.is_ascii_digit());
            let s = &self.input[self.start..self.cur];
            self.make_token(TokenKind::Real(s.parse().unwrap()))
        } else {
            let s = &self.input[self.start..self.cur];
            self.make_token(TokenKind::Integer(s.parse().unwrap()))
        }
    }

    fn character(&mut self) -> LexResult<Token> {
        let c = self
            .bump()
            .ok_or_else(|| self.make_err(LexError::UnterminatedChar))?;

        let c = match c {
            '\\' => {
                let c = self
                    .bump()
                    .ok_or_else(|| self.make_err(LexError::UnterminatedString))?;
                Self::escape(c).ok_or_else(|| {
                    self.eat_while(|c| c != '"');
                    self.make_err(LexError::UnrecognizedEscape(c))
                })? as u8
            }
            '\'' => return Err(self.make_err(LexError::EmptyChar)),
            _ if c.is_ascii() => c as u8,
            _ => return Err(self.make_err(LexError::InvalidChar(c))),
        };

        if self.match_cur('\'') {
            Ok(self.make_token(TokenKind::Char(c)))
        } else {
            Err(self.make_err(LexError::UnterminatedChar))
        }
    }

    const fn escape(c: char) -> Option<char> {
        match c {
            'n' => Some('\n'),
            'r' => Some('\r'),
            '0' => Some('\0'),
            '\\' => Some('\\'),
            '\'' => Some('\''),
            '\"' => Some('\"'),
            _ => None,
        }
    }

    fn string(&mut self) -> LexResult<Token> {
        let mut s = String::new();

        while self.first() != '"' {
            let c = self.bump().unwrap();
            if c == '\\' {
                let c = self
                    .bump()
                    .ok_or_else(|| self.make_err(LexError::UnterminatedString))?;
                let c = Self::escape(c).ok_or_else(|| {
                    self.eat_while(|c| c != '"');
                    self.make_err(LexError::UnrecognizedEscape(c))
                })?;
                s.push(c);
            } else {
                s.push(c);
            }
        }

        if !self.match_cur('"') {
            return Err(self.make_err(LexError::UnterminatedString));
        }

        let kind = TokenKind::String(crate::global::intern_owned_symbol(s));

        Ok(self.make_token(kind))
    }

    fn identifier_or_keyword(&mut self) -> Token {
        self.eat_while(TokenKind::identifier_character);
        let s = &self.input[self.start..self.cur];
        let kind = TokenKind::keyword(s);
        self.make_token(kind)
    }

    fn operator(&mut self) -> Token {
        self.eat_while(TokenKind::operator_character);
        let s = &self.input[self.start..self.cur];
        let kind = TokenKind::operator(s);
        self.make_token(kind)
    }

    pub fn next_token(&mut self) -> Option<LexResult<Token>> {
        self.skip_whitespace();

        self.start = self.cur;
        let c = self.bump()?;

        macro_rules! token {
            ($tk:ident) => {{ Some(Ok(self.make_token(TokenKind::$tk))) }};
            ($tk:ident, $c2:expr => $tk2:ident) => {{
                if self.match_cur($c2) {
                    Some(Ok(self.make_token(TokenKind::$tk2)))
                } else {
                    Some(Ok(self.make_token(TokenKind::$tk)))
                }
            }};
        }

        match c {
            '@' => token!(At),
            '(' => token!(LParen),
            ')' => token!(RParen),
            '[' => token!(LBracket),
            ']' => token!(RBracket),
            '{' => token!(LBrace),
            '}' => token!(RBrace),
            ',' => token!(Comma),
            '\\' => token!(Backslash),
            ';' => token!(Semicolon),
            ':' => token!(Colon, ':' => ColonColon),
            '0'..='9' => Some(Ok(self.number())),
            '\'' => Some(self.character()),
            '"' => Some(self.string()),
            '_' | 'a'..='z' | 'A'..='Z' => Some(Ok(self.identifier_or_keyword())),
            c if TokenKind::operator_character(c) => Some(Ok(self.operator())),
            _ => Some(Err(self.make_err(LexError::InvalidChar(c)))),
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = LexResult<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
    }
}
