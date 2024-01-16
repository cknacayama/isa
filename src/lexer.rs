use crate::{
    error::{Loc, ParseError, ParseErrorData, ParseResult, Span},
    token::*,
};

#[derive(Debug)]
pub struct Lexer<'a> {
    input: &'a [u8],
    cursor: usize,

    line: u32,
    line_start: usize,
}

impl<'i> Lexer<'i> {
    pub fn new(input: &'i [u8]) -> Self {
        Self {
            input,
            cursor: 0,

            line: 1,
            line_start: 0,
        }
    }

    #[inline(always)]
    fn loc(&self) -> Loc {
        Loc {
            line: self.line,
            col: (self.cursor - self.line_start + 1) as u32,
        }
    }

    #[inline(always)]
    fn peek(&self) -> Option<u8> {
        self.input.get(self.cursor).copied()
    }

    #[inline(always)]
    fn peek_next(&self) -> Option<u8> {
        self.input.get(self.cursor + 1).copied()
    }

    #[inline(always)]
    fn match_cur(&mut self, c: u8) -> bool {
        if self.peek() == Some(c) {
            self.advance();
            true
        } else {
            false
        }
    }

    #[inline(always)]
    fn advance(&mut self) {
        self.cursor += 1;
    }

    #[inline(always)]
    fn advance_while<P: Fn(u8) -> bool>(&mut self, predicate: P) {
        while let Some(c) = self.peek() {
            if predicate(c) {
                self.advance();
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    fn make_token(&self, start: Loc, data: TokenData<'i>) -> Token<'i> {
        Token {
            data,

            span: Span {
                start,
                end: self.loc(),
            },
        }
    }

    #[inline(always)]
    fn make_err(&self, data: ParseErrorData) -> ParseError {
        ParseError::new(data, self.loc())
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            match c {
                b' ' | b'\t' | b'\r' => self.advance(),
                b'\n' => {
                    self.advance();
                    self.line += 1;
                    self.line_start = self.cursor;
                }
                b'/' => {
                    if self.match_cur(b'/') {
                        self.advance_while(|c| c != b'\n');
                        self.line += 1;
                        self.line_start = self.cursor;
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
    }

    fn number(&mut self) -> ParseResult<Token<'i>> {
        let start = self.loc();
        let start_pos = self.cursor;

        self.advance_while(|c| c.is_ascii_digit());

        if self.peek() == Some(b'.') && self.peek_next().map_or(false, |c| c.is_ascii_digit()) {
            self.advance();
            self.advance_while(|c| c.is_ascii_digit());

            let slice = &self.input[start_pos..self.cursor];
            let float = unsafe { std::str::from_utf8_unchecked(slice) }
                .parse()
                .unwrap();

            Ok(self.make_token(start, TokenData::Float(float)))
        } else {
            let slice = &self.input[start_pos..self.cursor];
            let int = unsafe { std::str::from_utf8_unchecked(slice) }
                .parse()
                .unwrap();

            Ok(self.make_token(start, TokenData::Int(int)))
        }
    }

    fn character(&mut self) -> ParseResult<Token<'i>> {
        let start = self.loc();

        let c = match self.peek() {
            Some(c) => c,
            None => return Err(self.make_err(ParseErrorData::UnterminatedChar)),
        };

        let c = if c == b'\\' {
            self.advance();
            match self.peek() {
                Some(b'\\') => b'\\',
                Some(b'n') => b'\n',
                Some(b't') => b'\t',
                Some(b'r') => b'\r',
                Some(b'\'') => b'\'',
                Some(b'"') => b'"',
                Some(b'0') => b'\0',
                Some(c) => {
                    return Err(ParseError::new(
                        ParseErrorData::InvalidEscape(c as char),
                        start,
                    ))
                }
                None => return Err(self.make_err(ParseErrorData::UnterminatedChar)),
            }
        } else {
            c
        };

        self.advance();

        if !self.match_cur(b'\'') {
            return Err(self.make_err(ParseErrorData::UnterminatedChar));
        }

        Ok(self.make_token(start, TokenData::Char(c as char)))
    }

    fn string(&mut self) -> ParseResult<Token<'i>> {
        let start = self.loc();
        let start_pos = self.cursor;

        self.advance_while(|c| c != b'"');

        if !self.match_cur(b'"') {
            return Err(self.make_err(ParseErrorData::UnterminatedString));
        }

        let slice = &self.input[start_pos..self.cursor - 1];
        let string = unsafe { std::str::from_utf8_unchecked(slice) };

        Ok(self.make_token(start, TokenData::String(string)))
    }

    fn identifier(&mut self) -> ParseResult<Token<'i>> {
        let start = self.loc();
        let start_pos = self.cursor;

        self.advance_while(|c| c.is_ascii_alphanumeric() || c == b'_');

        let slice = &self.input[start_pos..self.cursor];
        let ident = unsafe { std::str::from_utf8_unchecked(slice) };

        let data = Token::get_keyword(ident).unwrap_or(TokenData::Ident(ident));

        Ok(self.make_token(start, data))
    }

    fn next_token(&mut self) -> Option<ParseResult<Token<'i>>> {
        self.skip_whitespace();

        let c = match self.peek() {
            Some(c) => c,
            None => return None,
        };

        if c.is_ascii_digit() {
            return Some(self.number());
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            return Some(self.identifier());
        }

        let start = self.loc();
        self.advance();

        macro_rules! tok_1 {
            ($kind:ident) => {
                Some(Ok(self.make_token(start, TokenData::$kind)))
            };
        }

        macro_rules! tok_2 {
            ($kind:ident, $next:literal => $next_kind:ident) => {
                if self.match_cur($next) {
                    Some(Ok(self.make_token(start, TokenData::$next_kind)))
                } else {
                    Some(Ok(self.make_token(start, TokenData::$kind)))
                }
            };
        }

        match c {
            b';' => tok_1!(Semicolon),
            b'(' => tok_1!(LParen),
            b')' => tok_1!(RParen),
            b'{' => tok_1!(LBrace),
            b'}' => tok_1!(RBrace),
            b'[' => tok_1!(LBracket),
            b']' => tok_1!(RBracket),
            b'.' => tok_1!(Dot),
            b':' => tok_1!(Colon),
            b',' => tok_1!(Comma),
            b'?' => tok_1!(Question),
            b'~' => tok_1!(Tilde),
            b'^' => tok_1!(Caret),

            b'+' => tok_1!(Plus),
            b'*' => tok_1!(Star),
            b'/' => tok_1!(Slash),
            b'%' => tok_1!(Percent),

            b'!' => tok_2!(Bang, b'=' => BangEqual),
            b'=' => tok_2!(Equal, b'=' => EqualEqual),
            b'-' => tok_2!(Minus, b'>' => Arrow),
            b'&' => tok_2!(Amp, b'&' => AmpAmp),
            b'|' => tok_2!(Pipe, b'|' => PipePipe),

            b'\'' => Some(self.character()),
            b'"' => Some(self.string()),

            b'<' => match self.peek() {
                Some(b'=') => {
                    self.advance();
                    Some(Ok(self.make_token(start, TokenData::LessEqual)))
                }
                Some(b'<') => {
                    self.advance();
                    Some(Ok(self.make_token(start, TokenData::LessLess)))
                }
                _ => Some(Ok(self.make_token(start, TokenData::Less))),
            },

            b'>' => match self.peek() {
                Some(b'=') => {
                    self.advance();
                    Some(Ok(self.make_token(start, TokenData::GreaterEqual)))
                }
                Some(b'>') => {
                    self.advance();
                    Some(Ok(self.make_token(start, TokenData::GreaterGreater)))
                }
                _ => Some(Ok(self.make_token(start, TokenData::Greater))),
            },

            _ => Some(Err(self.make_err(ParseErrorData::InvalidChar(c as char)))),
        }
    }

    pub fn lex(&mut self) -> ParseResult<Vec<Token<'i>>> {
        let mut tokens = vec![];

        for token in self {
            tokens.push(token?);
        }

        Ok(tokens)
    }
}

impl<'i> Iterator for Lexer<'i> {
    type Item = ParseResult<Token<'i>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
    }
}
