use std::str::Chars;

use super::error::LexError;
use super::token::{Token, TokenKind};
use crate::global::intern_span;
use crate::span::{SpanData, Spanned};

#[derive(Debug)]
pub struct Lexer<'a> {
    file_id: usize,
    input:   &'a str,
    chars:   Chars<'a>,
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

    fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    fn peek_next(&self) -> Option<char> {
        let mut iter = self.chars.clone();
        iter.next();
        iter.next()
    }

    fn bump(&mut self) -> Option<char> {
        self.cur += 1;
        self.chars.next()
    }

    fn bump_twice(&mut self) -> Option<(char, char)> {
        self.cur += 2;
        self.chars
            .next()
            .and_then(|c1| self.chars.next().map(|c2| (c1, c2)))
    }

    fn match_cur(&mut self, to_match: char) -> bool {
        match self.peek() {
            Some(c) if c == to_match => {
                self.bump();
                true
            }
            _ => false,
        }
    }

    fn eat_while<P>(&mut self, mut pred: P)
    where
        P: FnMut(char) -> bool,
    {
        while let Some(c) = self.peek() {
            if pred(c) {
                self.bump();
            } else {
                break;
            }
        }
    }

    fn make_token(&self, kind: TokenKind) -> Token {
        let span = SpanData::new(self.file_id, self.start, self.cur).unwrap();
        let span = intern_span(span);
        Token::new(kind, span)
    }

    fn make_err(&self, kind: LexError) -> Spanned<LexError> {
        let span = SpanData::new(self.file_id, self.start, self.cur).unwrap();
        let span = intern_span(span);
        Spanned::new(kind, span)
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            match c {
                '/' if self.peek_next().is_some_and(|c| c == '/') => {
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

        if self.peek().is_some_and(|c| c == '.')
            && self.peek_next().is_some_and(|c| c.is_ascii_digit())
        {
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
            '\\' => todo!(),
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

    fn identifier_or_keyword(&mut self) -> Token {
        const fn is_identifier_char(c: char) -> bool {
            c == '_' || c.is_ascii_alphanumeric()
        }

        self.eat_while(is_identifier_char);
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
            ($tk:ident, $c2:literal => $tk2:ident, $c3:literal => $tk3:ident) => {{
                match self.peek() {
                    Some($c2) => {
                        self.bump();
                        Some(Ok(self.make_token(TokenKind::$tk2)))
                    }
                    Some($c3) => {
                        self.bump();
                        Some(Ok(self.make_token(TokenKind::$tk3)))
                    }
                    _ => Some(Ok(self.make_token(TokenKind::$tk))),
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
