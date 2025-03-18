use std::{collections::HashSet, iter::Peekable, rc::Rc};

use crate::{
    compiler::{
        ast::{BinOp, Expr, ExprKind, UnOp},
        error::ParseError,
        lexer::Lexer,
        token::{Token, TokenKind},
    },
    span::{Span, Spanned},
};

use super::{
    ast::{Constructor, Pat, PatKind},
    env::TypeEnv,
    types::Type,
};

pub type ParseResult<T> = Result<T, Spanned<ParseError>>;

#[derive(Debug)]
pub struct Parser<'a> {
    lexer:   Peekable<Lexer<'a>>,
    strings: HashSet<Rc<str>>,
    types:   TypeEnv,
}

impl<'a> Parser<'a> {
    #[must_use]
    pub fn from_input(input: &'a str) -> Self {
        Self::new(Lexer::new(input))
    }

    #[must_use]
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self {
            lexer:   lexer.peekable(),
            strings: HashSet::default(),
            types:   TypeEnv::default(),
        }
    }

    fn get_string(&mut self, s: &str) -> Rc<str> {
        if let Some(s) = self.strings.get(s) {
            s.clone()
        } else {
            let s: Rc<str> = Rc::from(s);
            self.strings.insert(s.clone());
            s
        }
    }

    #[must_use]
    pub fn types(self) -> TypeEnv {
        self.types
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

    fn peek_and<P>(&mut self, p: P) -> ParseResult<bool>
    where
        P: FnOnce(&TokenKind<'a>) -> bool,
    {
        Ok(self.peek().transpose()?.map(Spanned::data).is_some_and(p))
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

    pub fn parse_all(&mut self) -> ParseResult<Vec<Expr>> {
        self.collect()
    }

    pub fn parse(&mut self) -> Option<ParseResult<Expr>> {
        if self.peek().is_some() {
            Some(self.parse_semi_expr())
        } else {
            None
        }
    }

    fn get_type(&mut self, ty: Type) -> Rc<Type> {
        self.types.get_type(ty)
    }

    fn parse_semi_expr(&mut self) -> ParseResult<Expr> {
        let expr = self.parse_expr()?;

        if self.next_if_match(TokenKind::Semicolon).is_some() {
            let span = expr.span;
            let kind = ExprKind::Semi(Box::new(expr));
            Ok(Expr::new(kind, span))
        } else {
            Ok(expr)
        }
    }

    fn parse_expr(&mut self) -> ParseResult<Expr> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> ParseResult<Expr> {
        let mut lhs = self.parse_and()?;

        while self.next_if_match(TokenKind::KwOr).is_some() {
            let rhs = self.parse_and()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::bin_expr(BinOp::Or, lhs, rhs, span);
        }

        Ok(lhs)
    }

    fn parse_and(&mut self) -> ParseResult<Expr> {
        let mut lhs = self.parse_cmp()?;

        while self.next_if_match(TokenKind::KwAnd).is_some() {
            let rhs = self.parse_cmp()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::bin_expr(BinOp::And, lhs, rhs, span);
        }

        Ok(lhs)
    }

    fn parse_cmp(&mut self) -> ParseResult<Expr> {
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

    fn parse_add(&mut self) -> ParseResult<Expr> {
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

    fn parse_mul(&mut self) -> ParseResult<Expr> {
        let mut lhs = self.parse_call()?;

        while let Some(op) = self.next_if_map(|tk| match tk.data {
            TokenKind::Star => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            TokenKind::Percent => Some(BinOp::Rem),
            _ => None,
        }) {
            let rhs = self.parse_call()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::bin_expr(op, lhs, rhs, span);
        }

        Ok(lhs)
    }

    fn parse_call(&mut self) -> ParseResult<Expr> {
        let mut expr = self.parse_prim()?;

        while self.peek_and(TokenKind::can_start_expr)? {
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

    fn parse_prim(&mut self) -> ParseResult<Expr> {
        let Token { data, span } = self.next_or_eof()?;

        if let Some(op) = UnOp::from_token(data) {
            return Ok(Expr::new(ExprKind::UnOp(op), span));
        }
        if let Some(op) = BinOp::from_token(data) {
            return Ok(Expr::new(ExprKind::BinOp(op), span));
        }

        match data {
            TokenKind::LParen => {
                if let Some(rparen) = self.next_if_match(TokenKind::RParen) {
                    let span = span.union(rparen.span);
                    let kind = ExprKind::Unit;

                    Ok(Expr::new(kind, span))
                } else {
                    let mut expr = self.parse_expr()?;
                    expr.span = span.union(expr.span).union(self.expect(TokenKind::RParen)?);

                    Ok(expr)
                }
            }
            TokenKind::Integer(lit) => Ok(Expr::new(ExprKind::Int(lit.parse().unwrap()), span)),
            TokenKind::Ident(id) => Ok(Expr::new(ExprKind::Ident(self.get_string(id)), span)),
            TokenKind::KwTrue => Ok(Expr::new(ExprKind::Bool(true), span)),
            TokenKind::KwFalse => Ok(Expr::new(ExprKind::Bool(false), span)),
            TokenKind::KwLet => self.parse_let(span),
            TokenKind::KwFn => self.parse_fn(span),
            TokenKind::KwIf => self.parse_if(span),
            TokenKind::KwType => self.parse_type_decl(span),
            TokenKind::KwMatch => self.parse_match(span),

            _ => Err(Spanned::new(ParseError::ExpectedExpr, span)),
        }
    }

    fn parse_simple_type(&mut self) -> ParseResult<Spanned<Type>> {
        let tk = self.next_or_eof()?;

        match tk.data {
            TokenKind::LParen => {
                if let Some(Spanned { span, .. }) = self.next_if_match(TokenKind::RParen) {
                    Ok(Spanned::new(Type::Unit, tk.span.union(span)))
                } else {
                    let t = self.parse_type()?;
                    let span = tk.span.union(self.expect(TokenKind::RParen)?);
                    Ok(Spanned::new(t.data, span))
                }
            }
            TokenKind::KwInt => Ok(Spanned::new(Type::Int, tk.span)),
            TokenKind::KwBool => Ok(Spanned::new(Type::Bool, tk.span)),
            TokenKind::Ident(id) => Ok(Spanned::new(
                Type::Named {
                    name: self.get_string(id),
                    args: Box::from([]),
                },
                tk.span,
            )),

            _ => Err(Spanned::new(ParseError::ExpectedType, tk.span)),
        }
    }

    fn parse_type(&mut self) -> ParseResult<Spanned<Type>> {
        let simple = self.parse_simple_type()?;

        if self.next_if_match(TokenKind::Arrow).is_some() {
            let ret = self.parse_type()?;
            let span = simple.span.union(ret.span);

            Ok(Spanned::new(
                Type::Fn {
                    param: self.get_type(simple.data),
                    ret:   self.get_type(ret.data),
                },
                span,
            ))
        } else if let Type::Named { name, .. } = simple.data {
            let mut span = simple.span;
            let mut params = Vec::new();

            while self.peek_and(TokenKind::can_start_type)? {
                let ty = self.parse_simple_type()?;
                span = span.union(ty.span);
                params.push(self.get_type(ty.data));
            }

            let args = params.into_boxed_slice();
            Ok(Spanned::new(Type::Named { name, args }, span))
        } else {
            Ok(simple)
        }
    }

    fn parse_constructor(&mut self) -> ParseResult<Spanned<Constructor>> {
        let Spanned { data: id, mut span } = self.expect_id()?;

        let mut params = Vec::new();

        while self.peek_and(TokenKind::can_start_type)? {
            let ty = self.parse_simple_type()?;
            span = span.union(ty.span);
            params.push(self.get_type(ty.data));
        }

        Ok(Spanned::new(
            Constructor {
                id:     self.get_string(id),
                params: params.into_boxed_slice(),
            },
            span,
        ))
    }

    fn parse_type_decl(&mut self, span: Span) -> ParseResult<Expr> {
        let Spanned { data: id, .. } = self.expect_id()?;

        let mut params = Vec::new();

        while !self.check(TokenKind::Eq) {
            let Spanned { data, .. } = self.expect_id()?;
            params.push(self.get_string(data));
        }

        self.expect(TokenKind::Eq)?;

        let mut constructors = Vec::new();
        let mut span = span;
        loop {
            let c = self.parse_constructor()?;
            constructors.push(c.data);
            span = span.union(c.span);
            if self.next_if_match(TokenKind::Pipe).is_none() {
                break;
            }
        }

        Ok(Expr::new(
            ExprKind::Type {
                id:           self.get_string(id),
                parameters:   params.into_boxed_slice(),
                constructors: constructors.into_boxed_slice(),
            },
            span,
        ))
    }

    fn parse_match_arm(&mut self) -> ParseResult<Spanned<(Pat, Expr)>> {
        let pat = self.parse_if_pat()?;
        self.expect(TokenKind::Arrow)?;
        let expr = self.parse_expr()?;
        let span = pat.span.union(expr.span);

        Ok(Spanned::new((pat, expr), span))
    }

    fn parse_match(&mut self, mut span: Span) -> ParseResult<Expr> {
        let expr = self.parse_expr()?;
        self.expect(TokenKind::KwIn)?;

        let mut arms = Vec::new();

        while self.peek_and(TokenKind::can_start_pat)? {
            let arm = self.parse_match_arm()?;
            arms.push(arm.data);
            span = span.union(arm.span);
            if let Some(tk) = self.next_if_match(TokenKind::Comma) {
                span = span.union(tk.span);
            } else {
                break;
            }
        }

        Ok(Expr::new(
            ExprKind::Match {
                expr: Box::new(expr),
                arms: arms.into_boxed_slice(),
            },
            span,
        ))
    }

    fn parse_if(&mut self, span: Span) -> ParseResult<Expr> {
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

    fn parse_simple_pat(&mut self) -> ParseResult<Pat> {
        let Token { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::Integer(int) => Ok(Pat::new(PatKind::Int(int.parse().unwrap()), span)),
            TokenKind::KwTrue => Ok(Pat::new(PatKind::Bool(true), span)),
            TokenKind::KwFalse => Ok(Pat::new(PatKind::Bool(false), span)),
            TokenKind::LParen => {
                if let Some(Spanned { span: rspan, .. }) = self.next_if_match(TokenKind::RParen) {
                    Ok(Pat::new(PatKind::Unit, span.union(rspan)))
                } else {
                    let t = self.parse_pat()?;
                    let span = span.union(self.expect(TokenKind::RParen)?);
                    Ok(Pat::new(t.data, span))
                }
            }
            TokenKind::Ident(id) => {
                let name = self.get_string(id);
                Ok(Pat::new(PatKind::Ident(name), span))
            }
            TokenKind::Underscore => Ok(Pat::new(PatKind::Wild, span)),
            _ => Err(Spanned::new(ParseError::ExpectedPattern, span)),
        }
    }

    fn parse_type_pat(&mut self) -> ParseResult<Pat> {
        let simple = self.parse_simple_pat()?;

        if let PatKind::Ident(name) = simple.data {
            let mut span = simple.span;
            let mut args = Vec::new();

            while self.peek_and(TokenKind::can_start_pat)? {
                let pat = self.parse_simple_pat()?;
                span = span.union(pat.span);
                args.push(pat);
            }

            let args = args.into_boxed_slice();
            Ok(Pat::new(PatKind::Type { name, args }, span))
        } else {
            Ok(simple)
        }
    }

    fn parse_pat(&mut self) -> ParseResult<Pat> {
        let mut pat = self.parse_type_pat()?;

        if self.next_if_match(TokenKind::Pipe).is_some() {
            let mut span = pat.span;
            let mut pats = vec![pat];

            loop {
                let pat = self.parse_type_pat()?;
                pats.push(pat);
                if self.next_if_match(TokenKind::Pipe).is_none() {
                    break;
                }
            }

            span = span.union(pats.last().unwrap().span);

            pat = Pat::new(PatKind::Or(pats.into_boxed_slice()), span);
        }

        Ok(pat)
    }

    fn parse_if_pat(&mut self) -> ParseResult<Pat> {
        let pat = self.parse_pat()?;

        if self.next_if_match(TokenKind::KwIf).is_some() {
            let guard = self.parse_expr()?;
            let span = pat.span.union(guard.span);

            Ok(Pat::new(
                PatKind::Guard {
                    pat: Box::new(pat),
                    guard,
                },
                span,
            ))
        } else {
            Ok(pat)
        }
    }

    fn parse_let(&mut self, mut span: Span) -> ParseResult<Expr> {
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
                id: self.get_string(id),
                expr: Box::new(expr),
                body: body.map(Box::new),
            },
            span,
        ))
    }

    fn parse_fn(&mut self, span: Span) -> ParseResult<Expr> {
        let Spanned { data: param, .. } = self.expect_id()?;

        self.expect(TokenKind::Arrow)?;

        let expr = self.parse_expr()?;

        let span = span.union(expr.span);

        Ok(Expr::new(
            ExprKind::Fn {
                param: self.get_string(param),
                expr:  Box::new(expr),
            },
            span,
        ))
    }
}

impl Iterator for Parser<'_> {
    type Item = ParseResult<Expr>;

    fn next(&mut self) -> Option<Self::Item> {
        self.parse()
    }
}
