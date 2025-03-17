use std::iter::Peekable;

use crate::{
    compiler::{
        ast::{BinOp, Expr, ExprKind, UnOp},
        error::ParseError,
        lexer::Lexer,
        token::{Token, TokenKind},
    },
    span::{Span, Spanned},
};

pub type ParseResult<T> = Result<T, Spanned<ParseError>>;

#[derive(Debug)]
pub struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
}

impl<'a> Parser<'a> {
    pub fn from_input(input: &'a str) -> Self {
        Self::new(Lexer::new(input))
    }

    pub fn new(lexer: Lexer<'a>) -> Self {
        Self {
            lexer: lexer.peekable(),
        }
    }

    fn check(&mut self, t: TokenKind<'static>) -> bool {
        self.peek()
            .is_some_and(|tk| tk.map(|tk| tk.data == t).unwrap_or(false))
    }

    fn peek(&mut self) -> Option<ParseResult<&Token<'a>>> {
        self.lexer
            .peek()
            .map(|res| res.as_ref().map_err(|&err| Spanned::from(err)))
    }

    fn next(&mut self) -> Option<ParseResult<Token<'a>>> {
        self.lexer.next().map(|res| res.map_err(Spanned::from))
    }

    fn next_or_eof(&mut self) -> ParseResult<Token<'a>> {
        self.next()
            .ok_or_else(|| Spanned::new(ParseError::UnexpectedEof, Span::default()))?
    }

    fn next_if_match(&mut self, tk: TokenKind<'static>) -> Option<Token<'a>> {
        if self.check(tk) {
            Some(self.next().unwrap().unwrap())
        } else {
            None
        }
    }

    fn next_if_map<F, T>(&mut self, f: F) -> Option<T>
    where
        F: FnOnce(&Token<'a>) -> Option<T>,
    {
        let token = self.peek()?.ok()?;

        f(token).inspect(|_| {
            self.next().unwrap().unwrap();
        })
    }

    fn expect(&mut self, expected: TokenKind<'static>) -> ParseResult<Span> {
        self.next_or_eof().and_then(|t| {
            if t.data == expected {
                Ok(t.span)
            } else {
                Err(t.map(|_| ParseError::ExpectedToken(expected)))
            }
        })
    }

    fn expect_id(&mut self) -> ParseResult<Spanned<&'a str>> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Ident(id) => Ok(t.map(|_| id)),
            _ => Err(t.map(|_| ParseError::ExpectedId)),
        })
    }

    pub fn parse_all(&mut self) -> ParseResult<Vec<Expr<'a>>> {
        self.collect()
    }

    pub fn parse(&mut self) -> Option<ParseResult<Expr<'a>>> {
        if self.peek().is_some() {
            Some(self.parse_semi_expr())
        } else {
            None
        }
    }

    fn parse_semi_expr(&mut self) -> ParseResult<Expr<'a>> {
        let expr = self.parse_expr()?;

        if self.next_if_match(TokenKind::Semicolon).is_some() {
            let span = expr.span;
            let kind = ExprKind::Semi(Box::new(expr));
            Ok(Expr::new(kind, span))
        } else {
            Ok(expr)
        }
    }

    fn parse_expr(&mut self) -> ParseResult<Expr<'a>> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> ParseResult<Expr<'a>> {
        let mut lhs = self.parse_and()?;

        while self.next_if_match(TokenKind::KwOr).is_some() {
            let rhs = self.parse_and()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::bin_expr(BinOp::Or, lhs, rhs, span);
        }

        Ok(lhs)
    }

    fn parse_and(&mut self) -> ParseResult<Expr<'a>> {
        let mut lhs = self.parse_cmp()?;

        while self.next_if_match(TokenKind::KwAnd).is_some() {
            let rhs = self.parse_cmp()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::bin_expr(BinOp::And, lhs, rhs, span);
        }

        Ok(lhs)
    }

    fn parse_cmp(&mut self) -> ParseResult<Expr<'a>> {
        let mut lhs = self.parse_add()?;

        while let Some(op) = self.next_if_map(|tk| match tk.data {
            TokenKind::EqEq => Some(BinOp::Eq),
            TokenKind::BangEq => Some(BinOp::Ne),
            TokenKind::Lt => Some(BinOp::Lt),
            TokenKind::Le => Some(BinOp::Le),
            TokenKind::Gt => Some(BinOp::Gt),
            TokenKind::Ge => Some(BinOp::Ge),
            _ => None,
        }) {
            let rhs = self.parse_add()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::bin_expr(op, lhs, rhs, span);
        }

        Ok(lhs)
    }

    fn parse_add(&mut self) -> ParseResult<Expr<'a>> {
        let mut lhs = self.parse_mul()?;

        while let Some(op) = self.next_if_map(|tk| match tk.data {
            TokenKind::Plus => Some(BinOp::Add),
            TokenKind::Minus => Some(BinOp::Sub),
            _ => None,
        }) {
            let rhs = self.parse_mul()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::bin_expr(op, lhs, rhs, span);
        }

        Ok(lhs)
    }

    fn parse_mul(&mut self) -> ParseResult<Expr<'a>> {
        let mut lhs = self.parse_pow()?;

        while let Some(op) = self.next_if_map(|tk| match tk.data {
            TokenKind::Star => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            TokenKind::Percent => Some(BinOp::Rem),
            _ => None,
        }) {
            let rhs = self.parse_pow()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::bin_expr(op, lhs, rhs, span);
        }

        Ok(lhs)
    }

    fn parse_pow(&mut self) -> ParseResult<Expr<'a>> {
        let mut lhs = self.parse_call()?;

        while self.next_if_match(TokenKind::Caret).is_some() {
            let rhs = self.parse_call()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::bin_expr(BinOp::Pow, lhs, rhs, span);
        }

        Ok(lhs)
    }

    fn parse_call(&mut self) -> ParseResult<Expr<'a>> {
        let mut expr = self.parse_prim()?;

        while self
            .peek()
            .transpose()?
            .map(Spanned::data)
            .is_some_and(TokenKind::can_start_expr)
        {
            let arg = self.parse_prim()?;
            let span = expr.span.union(arg.span);
            expr = Expr::new(
                ExprKind::Call {
                    callee: Box::new(expr),
                    arg:    Box::new(arg),
                },
                span,
            );
        }
        Ok(expr)
    }

    fn parse_prim(&mut self) -> ParseResult<Expr<'a>> {
        let Token { data, span } = self.next_or_eof()?;

        if let Some(op) = UnOp::from_token(data) {
            return Ok(Expr::new(ExprKind::UnOp(op), span));
        }
        if let Some(op) = BinOp::from_token(data) {
            return Ok(Expr::new(ExprKind::BinOp(op), span));
        }

        match data {
            TokenKind::LParen => match self.next_if_match(TokenKind::RParen) {
                Some(rparen) => {
                    let span = span.union(rparen.span);
                    let kind = ExprKind::Unit;

                    Ok(Expr::new(kind, span))
                }
                _ => {
                    let mut expr = self.parse_expr()?;
                    expr.span = span.union(expr.span).union(self.expect(TokenKind::RParen)?);

                    Ok(expr)
                }
            },
            TokenKind::Integer(lit) => Ok(Expr::new(ExprKind::Int(lit.parse().unwrap()), span)),
            TokenKind::Ident(id) => Ok(Expr::new(ExprKind::Ident(id), span)),
            TokenKind::KwTrue => Ok(Expr::new(ExprKind::Bool(true), span)),
            TokenKind::KwFalse => Ok(Expr::new(ExprKind::Bool(false), span)),
            TokenKind::KwLet => self.parse_let(span),
            TokenKind::KwFn => self.parse_fn(span),
            TokenKind::KwIf => self.parse_if(span),

            _ => Err(Spanned::new(ParseError::ExpectedExpr, span)),
        }
    }

    fn parse_if(&mut self, span: Span) -> ParseResult<Expr<'a>> {
        let cond = self.parse_expr()?;

        self.expect(TokenKind::KwThen)?;
        let then = self.parse_expr()?;

        self.expect(TokenKind::KwElse)?;
        let otherwise = self.parse_expr()?;

        Ok(Expr::new(
            ExprKind::If {
                cond:      Box::new(cond),
                then:      Box::new(then),
                otherwise: Box::new(otherwise),
            },
            span,
        ))
    }

    fn parse_let(&mut self, mut span: Span) -> ParseResult<Expr<'a>> {
        let rec = self.next_if_match(TokenKind::KwRec).is_some();
        let Spanned { data: id, .. } = self.expect_id()?;
        self.expect(TokenKind::Eq)?;
        let expr = self.parse_expr()?;
        let body = if self.next_if_match(TokenKind::KwIn).is_some() {
            let body = self.parse_expr()?;
            span = span.union(body.span);
            Some(body)
        } else {
            None
        };

        Ok(Expr::new(
            ExprKind::Let {
                rec,
                id,
                expr: Box::new(expr),
                body: body.map(Box::new),
            },
            span,
        ))
    }

    fn parse_fn(&mut self, span: Span) -> ParseResult<Expr<'a>> {
        let Spanned { data: param, .. } = self.expect_id()?;

        self.expect(TokenKind::Arrow)?;

        let expr = self.parse_expr()?;

        let span = span.union(expr.span);

        Ok(Expr::new(
            ExprKind::Fn {
                param,
                expr: Box::new(expr),
            },
            span,
        ))
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = ParseResult<Expr<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.parse()
    }
}
