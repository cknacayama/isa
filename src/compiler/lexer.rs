use std::str::Chars;

use super::error::{LexError, LexErrorKind};
use super::token::{Token, TokenKind};
use crate::global::{Span, Symbol};
use crate::span::SpanData;

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
        self.chars.next().inspect(|c| self.cur += c.len_utf8())
    }

    fn bump_twice(&mut self) -> Option<(char, char)> {
        let c1 = self.chars.next()?;
        self.cur += c1.len_utf8();
        let c2 = self.chars.next()?;
        self.cur += c2.len_utf8();
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

        let kind = TokenKind::String(Symbol::intern_owned(s));

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

    macro_rules! assert_tk {
        ($input:literal) => {
            insta::assert_debug_snapshot!(Lexer::new(0, $input).next())
        };
    }

    macro_rules! assert_all {
        ($input:literal) => {
            insta::assert_debug_snapshot!(Lexer::new(0, $input).collect::<Vec<_>>())
        };
    }

    #[test]
    fn numbers() {
        assert_tk!("0000");
        assert_tk!("0120");
        assert_tk!("12");
        assert_tk!("4.0");
        assert_tk!("5.0");
        assert_tk!("1.2");
        assert_tk!("111.2");
    }

    #[test]
    fn keyword() {
        assert_tk!("_");
        assert_tk!("let");
        assert_tk!("val");
        assert_tk!("if");
        assert_tk!("then");
        assert_tk!("true");
        assert_tk!("false");
        assert_tk!("int");
        assert_tk!("bool");
        assert_tk!("char");
        assert_tk!("real");
        assert_tk!("type");
        assert_tk!("alias");
        assert_tk!("class");
        assert_tk!("instance");
        assert_tk!("infix");
        assert_tk!("infixl");
        assert_tk!("infixr");
        assert_tk!("prefix");
        assert_tk!("match");
        assert_tk!("else");
        assert_tk!("in");
        assert_tk!("with");
        assert_tk!("module");
        assert_tk!("Self");
    }

    #[test]
    fn ident() {
        assert_tk!("_i");
        assert_tk!("letf");
        assert_tk!("vals");
        assert_tk!("ifs");
        assert_tk!("thenz");
        assert_tk!("true10");
        assert_tk!("false18");
        assert_tk!("aint");
        assert_tk!("lbool");
        assert_tk!("_char");
        assert_tk!("real_");
        assert_tk!("Type");
        assert_tk!("aliass");
        assert_tk!("classes");
        assert_tk!("_8instance");
        assert_tk!("_01infix");
        assert_tk!("_01infixl");
        assert_tk!("_01infixr");
        assert_tk!("mengoprefix");
        assert_tk!("amatch");
        assert_tk!("belse");
        assert_tk!("cin");
        assert_tk!("dwith");
        assert_tk!("emodule");
        assert_tk!("self");
    }

    #[test]
    fn operator() {
        assert_tk!("+");
        assert_tk!("-");
        assert_tk!("/");
        assert_tk!("*");
        assert_tk!("^");
        assert_tk!("^^");
        assert_tk!("!");
        assert_tk!("==");
        assert_tk!("!=");
        assert_tk!(">");
        assert_tk!(">=");
        assert_tk!("<");
        assert_tk!("<=");
        assert_tk!("&&");
        assert_tk!("||");
        assert_tk!(">>");
        assert_tk!(">>=");
        assert_tk!("$");
        assert_tk!(".");
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
            "\n\n12 +\n\n// mengo mengo mengo mengo 123 && a aa^`\t\t\t\t\n//foo bar baz\n\n   13";
        let mut lexer = Lexer::new(0, input);
        insta::assert_debug_snapshot!(lexer.next());
        insta::assert_debug_snapshot!(lexer.next());
        insta::assert_debug_snapshot!(lexer.next());
        insta::assert_debug_snapshot!(lexer.next());
    }

    #[test]
    fn chars() {
        assert_tk!(r"'a'");
        assert_tk!(r"'\n'");
        assert_tk!(r"'\t'");
        assert_tk!(r"'\r'");
        assert_tk!(r"'\\'");
        assert_tk!(r"'\''");
        assert_tk!(r#"'\"'"#);
        assert_tk!(r"'\0'");
        assert_tk!(r"'1'");
    }

    #[test]
    fn strings() {
        assert_tk!(r#""foo""#);
        assert_tk!(r#""foo\n""#);
        assert_tk!(r#""bar\r""#);
        assert_tk!(r#""ba5\t""#);
        assert_tk!(r#""ba3\"""#);
        assert_tk!(r#""ba2\0a""#);
    }

    #[test]
    fn delimiters() {
        assert_tk!("(");
        assert_tk!(")");
        assert_tk!("{");
        assert_tk!("}");
        assert_tk!("[");
        assert_tk!("]");
        assert_tk!(":");
        assert_tk!("::");
        assert_tk!(";");
        assert_tk!("@");
        assert_tk!("->");
        assert_tk!("=>");
        assert_tk!("\\");
        assert_tk!(",");
    }

    #[test]
    fn invalid_errors() {
        assert_tk!(r"λ");
        assert_all!(r"λ λ λ");
        assert_all!(r"λ ba λ");
    }

    #[test]
    fn char_errors() {
        assert_tk!("''");
        assert_tk!(r"'\z'");
        assert_tk!(r"'λ'");
        assert_tk!(r"'aa'");
    }

    #[test]
    fn string_errors() {
        assert_tk!(r#""foo"#);
        assert_tk!(r#""foo\n"#);
        assert_tk!(r#""bar\"#);
        assert_tk!(
            r#""ba3\"
            ""#
        );
        assert_tk!(r#""ba5\c""#);
    }

    #[test]
    fn lists() {
        assert_all!("[]");
        assert_all!("[1,2,3]");
        assert_all!("[a,b,c,d]");
        assert_all!("[['a'],['b'],['c'],['d']]");
        assert_all!("[['a'],['b'],['c'],['d'],]");
    }

    #[test]
    fn tuples() {
        assert_all!("()");
        assert_all!("(1,2,3)");
        assert_all!("(a,b,c,d)");
        assert_all!("(('a'),('b'),('c'),('d'))");
        assert_all!("(('a'),('b'),('c'),('d'),)");
    }

    #[test]
    fn lets() {
        assert_all!("let a = 10 in 10");
        assert_all!("let a c = 10 in let b = a in b");
    }

    #[test]
    fn paths() {
        assert_all!("a::b");
        assert_all!("a::b::c");
        assert_all!("a::b::c a");
        assert_all!("a::b::c a::T");
        assert_all!("a::b::c C::a::T b");
    }

    #[test]
    fn prefix() {
        assert_all!("-1");
        assert_all!("(!false)");
        assert_all!("-a");
        assert_all!(r#"-"string""#);
        assert_all!(r#"-'c'"#);
        assert_all!(r#"- - - - - - - + - + 1"#);
    }

    #[test]
    fn infix() {
        assert_all!("1 + 1");
        assert_all!("a + 1 + 1");
        assert_all!(r#""string" + (1 * 1)"#);
        assert_all!("a + ((c ^^ []) >>= 'd')");
        assert_all!("1 * 2 * 3 + ((() & (1) ^^ []) >>= 'd')");
    }

    #[test]
    fn lambdas() {
        assert_all!(r"\x -> x");
        assert_all!(r"\(a,b) -> a + b");
        assert_all!(r"\_ -> 10 + (\x -> x) 10");
    }

    #[test]
    fn calls() {
        assert_all!("Some x");
        assert_all!(r"map (\x -> x + 1) [1,2,3]");
        assert_all!(r"(>>=) (None) \x -> return x");
    }

    #[test]
    fn matches() {
        assert_all!("match 10 with 0.. -> 10, ..0 -> -10");
        assert_all!("match (1,2) with (0.., ..0) -> 10, (..0, 0..) -> -10");
        assert_all!("match [10] with [] -> match [] with _ -> 10,, [a]b -> a+b");
    }

    #[test]
    fn ifs() {
        assert_all!("if true then true else false");
        assert_all!("if false then if true then false else true else false");
        assert_all!("if !false then !true else if false then true else false");
    }

    #[test]
    fn let_stmts() {
        assert_all!("let a = 10;");
        assert_all!("let fib n = match n with ..2 -> n, _ -> fib (n - 1) + fib (n - 2)");
        assert_all!("let foo (a,b,c) = a + b - c;");
        assert_all!("let bar _ _ _ = true;");
        assert_all!("let mengo _ _c _ = true;");
    }

    #[test]
    fn program() {
        assert_all!(
            r#"
module main

let a = 10;
let c = 1234;
let b = a + b * c;
// comment abc &&
(&&) && (&&);
match c with _ -> 10;
match c with ..10 -> 6.2, 10.. -> 3.14;
"#
        )
    }
}
