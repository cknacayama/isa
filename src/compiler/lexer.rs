use std::str::Chars;

use super::error::{LexError, LexErrorKind};
use super::token::{Token, TokenKind};
use crate::span::{Span, SpanData};

const EOF: char = '\0';

#[derive(Debug)]
pub struct Lexer<'a> {
    file_id: usize,
    chars:   Chars<'a>,
    input:   &'a str,
    start:   usize,
    cur:     usize,
}

pub type LexResult<T> = Result<T, LexError>;

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

    fn make_err(&self, kind: LexErrorKind) -> LexError {
        let span = SpanData::new(self.file_id, self.start, self.cur);
        let span = Span::intern(span);
        LexError::new(kind, span)
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
            .ok_or_else(|| self.make_err(LexErrorKind::UnterminatedChar))?;

        let c = match c {
            '\\' => {
                let c = self
                    .bump()
                    .ok_or_else(|| self.make_err(LexErrorKind::UnterminatedString))?;
                Self::escape(c).ok_or_else(|| {
                    self.eat_while(|c| c != '"');
                    self.make_err(LexErrorKind::UnrecognizedEscape(c))
                })? as u8
            }
            '\'' => return Err(self.make_err(LexErrorKind::EmptyChar)),
            _ if c.is_ascii() => c as u8,
            _ => return Err(self.make_err(LexErrorKind::InvalidChar(c))),
        };

        if self.match_cur('\'') {
            Ok(self.make_token(TokenKind::Char(c)))
        } else {
            Err(self.make_err(LexErrorKind::UnterminatedChar))
        }
    }

    const fn escape(c: char) -> Option<char> {
        match c {
            'n' => Some('\n'),
            'r' => Some('\r'),
            't' => Some('\t'),
            '0' => Some('\0'),
            '\\' => Some('\\'),
            '\'' => Some('\''),
            '\"' => Some('\"'),
            _ => None,
        }
    }

    fn string(&mut self) -> LexResult<Token> {
        let mut s = String::new();

        while !self.is_eof() && self.first() != '"' && self.first() != '\n' {
            let c = self.bump().unwrap();
            if c == '\\' {
                let c = self
                    .bump()
                    .ok_or_else(|| self.make_err(LexErrorKind::UnterminatedString))?;
                let c = Self::escape(c).ok_or_else(|| {
                    self.eat_while(|c| c != '"');
                    self.make_err(LexErrorKind::UnrecognizedEscape(c))
                })?;
                s.push(c);
            } else {
                s.push(c);
            }
        }

        if !self.match_cur('"') {
            return Err(self.make_err(LexErrorKind::UnterminatedString));
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
            _ => Some(Err(self.make_err(LexErrorKind::InvalidChar(c)))),
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = LexResult<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[track_caller]
    fn check_error(err: LexErrorKind, input: &str) {
        let got = Lexer::new(0, input).next().unwrap().unwrap_err();
        assert_eq!(err, got.data);
    }

    #[track_caller]
    fn check_kind(expected: TokenKind, input: &str) {
        let mut lexer = Lexer::new(0, input);
        let got = lexer.next().unwrap().unwrap();
        assert_eq!(expected, got.data);
        assert!(lexer.next().is_none());
    }

    #[track_caller]
    fn check_ident(input: &str) {
        let mut lexer = Lexer::new(0, input);
        let got = lexer.next().unwrap().unwrap();
        let input = input.trim();
        assert_eq!(input, got.data.as_ident().unwrap().get());
        assert!(lexer.next().is_none());
    }

    #[track_caller]
    fn check_operator(input: &str) {
        let mut lexer = Lexer::new(0, input);
        let got = lexer.next().unwrap().unwrap();
        let input = input.trim();
        assert_eq!(input, got.data.as_operator().unwrap().get());
        assert!(lexer.next().is_none());
    }

    #[track_caller]
    fn check_string(input: &str) {
        let mut lexer = Lexer::new(0, input);
        let got = lexer.next().unwrap().unwrap();
        let input = input.trim();
        assert_eq!(input, format!("{:?}", got.data.as_string().unwrap().get()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn numbers() {
        use TokenKind::{Integer, Real};
        check_kind(Integer(0), "0000");
        check_kind(Integer(120), "0120");
        check_kind(Integer(12), "12");
        check_kind(Real(4.0), "4.0");
        check_kind(Real(5.0), "5.0");
        check_kind(Real(1.2), "1.2");
        check_kind(Real(111.2), "111.2");
    }

    #[test]
    fn keyword() {
        use TokenKind::*;
        check_kind(Underscore, "_");
        check_kind(KwLet, "let");
        check_kind(KwVal, "val");
        check_kind(KwIf, "if");
        check_kind(KwThen, "then");
        check_kind(KwTrue, "true");
        check_kind(KwFalse, "false");
        check_kind(KwInt, "int");
        check_kind(KwBool, "bool");
        check_kind(KwChar, "char");
        check_kind(KwReal, "real");
        check_kind(KwType, "type");
        check_kind(KwAlias, "alias");
        check_kind(KwClass, "class");
        check_kind(KwInstance, "instance");
        check_kind(KwInfix, "infix");
        check_kind(KwInfixl, "infixl");
        check_kind(KwInfixr, "infixr");
        check_kind(KwPrefix, "prefix");
        check_kind(KwMatch, "match");
        check_kind(KwElse, "else");
        check_kind(KwIn, "in");
        check_kind(KwWith, "with");
        check_kind(KwModule, "module");
        check_kind(KwSelf, "Self");
    }

    #[test]
    fn ident() {
        check_ident("_i");
        check_ident("letf");
        check_ident("vals");
        check_ident("ifs");
        check_ident("thenz");
        check_ident("true10");
        check_ident("false18");
        check_ident("aint");
        check_ident("lbool");
        check_ident("_char");
        check_ident("real_");
        check_ident("Type");
        check_ident("aliass");
        check_ident("classes");
        check_ident("_8instance");
        check_ident("_01infix");
        check_ident("_01infixl");
        check_ident("_01infixr");
        check_ident("mengoprefix");
        check_ident("amatch");
        check_ident("belse");
        check_ident("cin");
        check_ident("dwith");
        check_ident("emodule");
        check_ident("self");
    }

    #[test]
    fn operator() {
        check_operator("+");
        check_operator("-");
        check_operator("/");
        check_operator("*");
        check_operator("^");
        check_operator("^^");
        check_operator("!");
        check_operator("==");
        check_operator("!=");
        check_operator(">");
        check_operator(">=");
        check_operator("<");
        check_operator("<=");
        check_operator("&&");
        check_operator("||");
        check_operator(">>");
        check_operator(">>=");
        check_operator("$");
        check_operator(".");
    }

    #[test]
    fn comment() {
        let input = "// mengo mengo mengo mengo 123 && à aa^`";
        let mut lexer = Lexer::new(0, input);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn comment_and_whitespace() {
        let input = "\n\n\n\n// mengo mengo mengo mengo 123 && a aa^`\t\t\t\t\n//foo bar baz";
        let mut lexer = Lexer::new(0, input);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn spaced_tokens() {
        let input =
            "\n\n12\n\n// mengo mengo mengo mengo 123 && a aa^`\t\t\t\t\n//foo bar baz\n\n   13";
        let mut lexer = Lexer::new(0, input);
        assert_eq!(TokenKind::Integer(12), lexer.next().unwrap().unwrap().data);
        assert_eq!(TokenKind::Integer(13), lexer.next().unwrap().unwrap().data);
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn chars() {
        use TokenKind::Char;
        check_kind(Char(b'a'), r"'a'");
        check_kind(Char(b'\n'), r"'\n'");
        check_kind(Char(b'\t'), r"'\t'");
        check_kind(Char(b'\r'), r"'\r'");
        check_kind(Char(b'\\'), r"'\\'");
        check_kind(Char(b'\''), r"'\''");
        check_kind(Char(b'\"'), r#"'\"'"#);
        check_kind(Char(b'\0'), r"'\0'");
        check_kind(Char(b'1'), r"'1'");
    }

    #[test]
    fn strings() {
        check_string(r#""foo""#);
        check_string(r#""foo\n""#);
        check_string(r#""bar\r""#);
        check_string(r#""ba5\t""#);
        check_string(r#""ba3\"""#);
        check_string(r#""ba2\0a""#);
    }

    #[test]
    fn delimiters() {
        use TokenKind::*;
        check_kind(LParen, "(");
        check_kind(RParen, ")");
        check_kind(LBrace, "{");
        check_kind(RBrace, "}");
        check_kind(LBracket, "[");
        check_kind(RBracket, "]");
        check_kind(Comma, ",");
        check_kind(Colon, ":");
        check_kind(ColonColon, "::");
        check_kind(Semicolon, ";");
        check_kind(At, "@");
        check_kind(Arrow, "->");
        check_kind(Rocket, "=>");
        check_kind(Backslash, "\\");
    }

    #[test]
    fn char_errors() {
        check_error(LexErrorKind::EmptyChar, "''");
        check_error(LexErrorKind::UnrecognizedEscape('z'), r"'\z'");
        check_error(LexErrorKind::InvalidChar('λ'), r"'λ'");
        check_error(LexErrorKind::UnterminatedChar, r"'aa'");
    }

    #[test]
    fn string_errors() {
        check_error(LexErrorKind::UnterminatedString, r#""foo"#);
        check_error(LexErrorKind::UnterminatedString, r#""foo\n"#);
        check_error(LexErrorKind::UnterminatedString, r#""bar\"#);
        check_error(
            LexErrorKind::UnterminatedString,
            r#""ba3\"
            ""#,
        );
        check_error(LexErrorKind::UnrecognizedEscape('c'), r#""ba5\c""#);
    }
}
