use std::str::Chars;

use super::error::LexError;
use super::token::{Token, TokenKind};
use crate::global::{self, intern_span};
use crate::span::{SpanData, Spanned};

#[derive(Debug)]
pub struct Lexer<'a> {
    input: &'a str,
    chars: Chars<'a>,
    start: usize,
    cur:   usize,
}

pub type LexResult<T> = Result<T, Spanned<LexError>>;

impl<'a> Lexer<'a> {
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        Self {
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

    fn check_next<P>(&self, pred: P) -> bool
    where
        P: FnOnce(char) -> bool,
    {
        self.peek_next().is_some_and(pred)
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
        let span = SpanData::new(self.start, self.cur).unwrap();
        let span = intern_span(span);
        Token::new(kind, span)
    }

    fn make_err(&self, kind: LexError) -> Spanned<LexError> {
        let span = SpanData::new(self.start, self.cur).unwrap();
        let span = intern_span(span);
        Spanned::new(kind, span)
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            match c {
                '/' if self.check_next(|c| c == '/') => {
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
        let s = &self.input[self.start..self.cur];
        self.make_token(TokenKind::Integer(s.parse().unwrap()))
    }

    fn identifier_or_keyword(&mut self) -> Token {
        self.eat_while(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'');
        let s = &self.input[self.start..self.cur];
        TokenKind::keyword(s).map_or_else(
            || self.make_token(TokenKind::Ident(global::intern_symbol(s))),
            |kw| self.make_token(kw),
        )
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
            '(' => token!(LParen),
            ')' => token!(RParen),
            ',' => token!(Comma),
            ';' => token!(Semicolon),
            ':' => token!(Colon),
            '*' => token!(Star),
            '/' => token!(Slash),
            '%' => token!(Percent),
            '+' => token!(Plus),
            '=' => token!(Eq),
            '|' => token!(Bar, '>' => Pipe),
            '-' => token!(Minus, '>' => Arrow),
            '!' => token!(Bang, '=' => BangEq),
            '<' => token!(Lt, '=' => Le),
            '>' => token!(Gt, '=' => Ge),
            '0'..='9' => Some(Ok(self.number())),
            '\'' | '_' | 'a'..='z' | 'A'..='Z' => Some(Ok(self.identifier_or_keyword())),
            '.' => match (self.peek(), self.peek_next()) {
                (Some('.'), Some('=')) => {
                    self.bump_twice();
                    Some(Ok(self.make_token(TokenKind::DotDotEq)))
                }
                (Some('.'), _) => {
                    self.bump();
                    Some(Ok(self.make_token(TokenKind::DotDot)))
                }
                _ => Some(Ok(self.make_token(TokenKind::Dot))),
            },
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
