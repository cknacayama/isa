use std::iter::Peekable;
use std::rc::Rc;

use super::ast::untyped::{
    UntypedExpr, UntypedExprKind, UntypedMatchArm, UntypedModule, UntypedParam, UntypedPat,
    UntypedPatKind,
};
use super::ast::{BinOp, Constructor, IntRangePat, ModuleIdent, PathIdent, UnOp};
use super::error::ParseError;
use super::lexer::Lexer;
use super::token::{Token, TokenKind};
use super::types::Ty;
use crate::global::Symbol;
use crate::span::{Span, Spanned};

pub type ParseResult<T> = Result<T, Spanned<ParseError>>;

#[derive(Debug)]
pub struct Parser<'a> {
    lexer:     Peekable<Lexer<'a>>,
    last_span: Span,
}

impl<'a> Parser<'a> {
    #[must_use]
    pub fn from_input(input: &'a str) -> Self {
        Self::new(Lexer::new(input))
    }

    #[must_use]
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self {
            lexer:     lexer.peekable(),
            last_span: Span::default(),
        }
    }

    fn check(&mut self, t: TokenKind) -> bool {
        self.peek()
            .is_some_and(|tk| tk.map(|tk| tk.data == t).unwrap_or(false))
    }

    fn peek(&mut self) -> Option<ParseResult<&Token>> {
        self.lexer.peek().map(|res| match res {
            Ok(t) => {
                self.last_span = t.span;
                Ok(t)
            }
            Err(e) => {
                self.last_span = e.span;
                Err(Spanned::from(*e))
            }
        })
    }

    fn peek_and<P>(&mut self, p: P) -> ParseResult<bool>
    where
        P: FnOnce(&TokenKind) -> bool,
    {
        Ok(self.peek().transpose()?.map(Spanned::data).is_some_and(p))
    }

    fn next(&mut self) -> Option<ParseResult<Token>> {
        self.lexer.next().map(|res| match res {
            Ok(t) => {
                self.last_span = t.span;
                Ok(t)
            }
            Err(e) => {
                self.last_span = e.span;
                Err(Spanned::from(e))
            }
        })
    }

    fn next_or_eof(&mut self) -> ParseResult<Token> {
        self.next()
            .ok_or_else(|| Spanned::new(ParseError::UnexpectedEof, self.last_span))?
    }

    fn next_if_match(&mut self, tk: TokenKind) -> Option<Span> {
        if self.check(tk) {
            Some(self.next().unwrap().unwrap().span)
        } else {
            None
        }
    }

    fn next_if_map<F, T>(&mut self, f: F) -> Option<T>
    where
        F: FnOnce(&Token) -> Option<T>,
    {
        let token = self.peek()?.ok()?;

        f(token).inspect(|_| {
            self.next().unwrap().unwrap();
        })
    }

    fn expect(&mut self, expected: TokenKind) -> ParseResult<Span> {
        self.next_or_eof().and_then(|t| {
            if t.data == expected {
                Ok(t.span)
            } else {
                Err(t.map(|got| ParseError::ExpectedToken { expected, got }))
            }
        })
    }

    fn expect_id(&mut self) -> ParseResult<Spanned<Symbol>> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Ident(id) => Ok(t.map(|_| id)),
            _ => Err(t.map(ParseError::ExpectedId)),
        })
    }

    fn expect_integer(&mut self) -> ParseResult<Spanned<i64>> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Integer(int) => Ok(t.map(|_| int)),
            _ => Err(t.map(ParseError::ExpectedInt)),
        })
    }

    pub fn try_parse_module(&mut self) -> Option<ParseResult<UntypedModule>> {
        if self.peek().is_some() {
            Some(self.parse_module())
        } else {
            None
        }
    }

    /// parses one module
    fn parse_module(&mut self) -> ParseResult<UntypedModule> {
        let mut span = self.expect(TokenKind::KwModule)?;
        let name = self.expect_id()?;

        let mut exprs = vec![self.parse_semi_expr()?];

        while !self.check(TokenKind::KwModule) {
            let Some(expr) = self.parse() else { break };
            exprs.push(expr?);
        }

        if let [.., expr] = exprs.as_slice() {
            span = span.union(expr.span);
        }

        Ok(UntypedModule::untyped(name.data, exprs, span))
    }

    pub fn parse_all(&mut self) -> ParseResult<Vec<UntypedModule>> {
        std::iter::from_fn(|| self.try_parse_module()).collect()
    }

    /// parses zero or one expression (can have semicolon)
    pub fn parse(&mut self) -> Option<ParseResult<UntypedExpr>> {
        if self.peek().is_some() {
            Some(self.parse_semi_expr())
        } else {
            None
        }
    }

    fn parse_semi_expr(&mut self) -> ParseResult<UntypedExpr> {
        let span = self.last_span;

        let expr = match self
            .peek()
            .ok_or_else(|| Spanned::new(ParseError::UnexpectedEof, span))??
            .data
        {
            TokenKind::KwType => self.parse_type_definition(),
            TokenKind::KwVal => self.parse_val(),
            _ => self.parse_expr(),
        }?;

        if self.next_if_match(TokenKind::Semicolon).is_some() {
            let span = expr.span;
            let kind = UntypedExprKind::Semi(Box::new(expr));
            Ok(UntypedExpr::untyped(kind, span))
        } else {
            Ok(expr)
        }
    }

    fn parse_val(&mut self) -> ParseResult<UntypedExpr> {
        let span = self.expect(TokenKind::KwVal)?;
        let Spanned { data: id, .. } = self.expect_id()?;
        let mut params = Vec::new();
        while !self.check(TokenKind::Colon) {
            let Spanned { data, .. } = self.expect_id()?;
            params.push(Ty::Named {
                name: PathIdent::Ident(data),
                args: Rc::from([]),
            });
        }
        self.expect(TokenKind::Colon)?;
        let parameters = params.into_boxed_slice();
        let Spanned {
            data: ty,
            span: ty_span,
        } = self.parse_type()?;
        let span = span.union(ty_span);

        Ok(UntypedExpr::untyped(
            UntypedExprKind::Val {
                name: id,
                parameters,
                ty,
                ty_span,
            },
            span,
        ))
    }

    fn parse_expr(&mut self) -> ParseResult<UntypedExpr> {
        let span = self.last_span;
        match self
            .peek()
            .ok_or_else(|| Spanned::new(ParseError::UnexpectedEof, span))??
            .data
        {
            TokenKind::KwLet => self.parse_let(),
            TokenKind::KwFn => self.parse_fn(),
            TokenKind::KwIf => self.parse_if(),
            TokenKind::KwMatch => self.parse_match(),
            _ => self.parse_pipe(),
        }
    }

    fn parse_pipe(&mut self) -> ParseResult<UntypedExpr> {
        let mut lhs = self.parse_or()?;

        while self.next_if_match(TokenKind::Pipe).is_some() {
            let rhs = self.parse_or()?;
            let span = lhs.span.union(rhs.span);
            lhs = UntypedExpr::untyped(
                UntypedExprKind::Bin {
                    op:  BinOp::Pipe,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }

        Ok(lhs)
    }

    fn parse_or(&mut self) -> ParseResult<UntypedExpr> {
        let mut lhs = self.parse_and()?;

        while self.next_if_match(TokenKind::KwOr).is_some() {
            let rhs = self.parse_and()?;
            let span = lhs.span.union(rhs.span);
            lhs = UntypedExpr::untyped(
                UntypedExprKind::Bin {
                    op:  BinOp::Or,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }

        Ok(lhs)
    }

    fn parse_and(&mut self) -> ParseResult<UntypedExpr> {
        let mut lhs = self.parse_cmp()?;

        while self.next_if_match(TokenKind::KwAnd).is_some() {
            let rhs = self.parse_cmp()?;
            let span = lhs.span.union(rhs.span);
            lhs = UntypedExpr::untyped(
                UntypedExprKind::Bin {
                    op:  BinOp::And,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }

        Ok(lhs)
    }

    fn parse_cmp(&mut self) -> ParseResult<UntypedExpr> {
        let mut lhs = self.parse_add()?;

        while let Some(op) = self.next_if_map(|tk| match tk.data {
            TokenKind::Eq => Some(BinOp::Eq),
            TokenKind::BangEq => Some(BinOp::Ne),
            TokenKind::Lt => Some(BinOp::Lt),
            TokenKind::Le => Some(BinOp::Le),
            TokenKind::Gt => Some(BinOp::Gt),
            TokenKind::Ge => Some(BinOp::Ge),
            _ => None,
        }) {
            let rhs = self.parse_add()?;
            let span = lhs.span.union(rhs.span);
            lhs = UntypedExpr::untyped(
                UntypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }

        Ok(lhs)
    }

    fn parse_add(&mut self) -> ParseResult<UntypedExpr> {
        let mut lhs = self.parse_mul()?;

        while let Some(op) = self.next_if_map(|tk| match tk.data {
            TokenKind::Plus => Some(BinOp::Add),
            TokenKind::Minus => Some(BinOp::Sub),
            _ => None,
        }) {
            let rhs = self.parse_mul()?;
            let span = lhs.span.union(rhs.span);
            lhs = UntypedExpr::untyped(
                UntypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }

        Ok(lhs)
    }

    fn parse_mul(&mut self) -> ParseResult<UntypedExpr> {
        let mut lhs = self.parse_unary()?;

        while let Some(op) = self.next_if_map(|tk| match tk.data {
            TokenKind::Star => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            TokenKind::Percent => Some(BinOp::Rem),
            _ => None,
        }) {
            let rhs = self.parse_unary()?;
            let span = lhs.span.union(rhs.span);
            lhs = UntypedExpr::untyped(
                UntypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }

        Ok(lhs)
    }

    fn parse_unary(&mut self) -> ParseResult<UntypedExpr> {
        if let Some(op) =
            self.next_if_map(|tk| UnOp::from_token(tk.data).map(|op| Spanned::new(op, tk.span)))
        {
            let expr = self.parse_unary()?;
            let span = op.span.union(expr.span);

            let kind = UntypedExprKind::Un {
                op:   op.data,
                expr: Box::new(expr),
            };

            Ok(UntypedExpr::untyped(kind, span))
        } else {
            self.parse_call()
        }
    }

    fn parse_call(&mut self) -> ParseResult<UntypedExpr> {
        let mut expr = self.parse_prim()?;

        while self.peek_and(TokenKind::can_start_expr)? {
            let arg = self.parse_prim()?;
            let span = expr.span.union(arg.span);
            expr = UntypedExpr::untyped(
                UntypedExprKind::Call {
                    callee: Box::new(expr),
                    arg:    Box::new(arg),
                },
                span,
            );
        }
        Ok(expr)
    }

    fn parse_prim(&mut self) -> ParseResult<UntypedExpr> {
        let Token { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::LParen => {
                if let Some(rparen) = self.next_if_match(TokenKind::RParen) {
                    let span = span.union(rparen);
                    let kind = UntypedExprKind::Unit;

                    Ok(UntypedExpr::untyped(kind, span))
                } else {
                    let mut expr = self.parse_expr()?;
                    expr.span = span.union(expr.span).union(self.expect(TokenKind::RParen)?);

                    Ok(expr)
                }
            }
            TokenKind::Integer(lit) => Ok(UntypedExpr::untyped(UntypedExprKind::Int(lit), span)),
            TokenKind::Ident(id) => {
                if self.next_if_match(TokenKind::Dot).is_some() {
                    let member = self.expect_id()?;
                    let span = span.union(member.span);
                    let kind = UntypedExprKind::ModuleIdent(ModuleIdent::new(id, member.data));
                    Ok(UntypedExpr::untyped(kind, span))
                } else {
                    Ok(UntypedExpr::untyped(UntypedExprKind::Ident(id), span))
                }
            }
            TokenKind::KwTrue => Ok(UntypedExpr::untyped(UntypedExprKind::Bool(true), span)),
            TokenKind::KwFalse => Ok(UntypedExpr::untyped(UntypedExprKind::Bool(false), span)),
            _ => Err(Spanned::new(ParseError::ExpectedExpr(data), span)),
        }
    }

    fn parse_path(&mut self, name: Symbol, span: Span) -> ParseResult<(PathIdent, Span)> {
        if self.next_if_match(TokenKind::Dot).is_some() {
            let member = self.expect_id()?;
            let span = span.union(member.span);

            Ok((PathIdent::Module(ModuleIdent::new(name, member.data)), span))
        } else {
            Ok((PathIdent::Ident(name), span))
        }
    }

    fn parse_simple_type(&mut self) -> ParseResult<Spanned<Ty>> {
        let Spanned { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::LParen => {
                if let Some(span) = self.next_if_match(TokenKind::RParen) {
                    Ok(Spanned::new(Ty::Unit, span.union(span)))
                } else {
                    let t = self.parse_type()?;
                    let span = span.union(self.expect(TokenKind::RParen)?);
                    Ok(Spanned::new(t.data, span))
                }
            }
            TokenKind::KwInt => Ok(Spanned::new(Ty::Int, span)),
            TokenKind::KwBool => Ok(Spanned::new(Ty::Bool, span)),
            TokenKind::Ident(name) => {
                let (path, span) = self.parse_path(name, span)?;
                Ok(Spanned::new(
                    Ty::Named {
                        name: path,
                        args: Rc::from([]),
                    },
                    span,
                ))
            }

            _ => Err(Spanned::new(ParseError::ExpectedType(data), span)),
        }
    }

    fn parse_polymorphic_type(&mut self) -> ParseResult<Spanned<Ty>> {
        let simple = self.parse_simple_type()?;

        if let Ty::Named { name, .. } = simple.data {
            let mut span = simple.span;
            let mut params = Vec::new();

            while self.peek_and(TokenKind::can_start_type)? {
                let ty = self.parse_simple_type()?;
                span = span.union(ty.span);
                params.push(ty.data);
            }

            let args = params.into();
            Ok(Spanned::new(Ty::Named { name, args }, span))
        } else {
            Ok(simple)
        }
    }

    fn parse_type(&mut self) -> ParseResult<Spanned<Ty>> {
        let simple = self.parse_polymorphic_type()?;

        if self.next_if_match(TokenKind::Arrow).is_some() {
            let ret = self.parse_type()?;
            let span = simple.span.union(ret.span);

            Ok(Spanned::new(
                Ty::Fn {
                    param: Rc::new(simple.data),
                    ret:   Rc::new(ret.data),
                },
                span,
            ))
        } else {
            Ok(simple)
        }
    }

    fn parse_constructor(&mut self) -> ParseResult<Constructor> {
        let Spanned {
            data: name,
            mut span,
        } = self.expect_id()?;

        let mut params = Vec::new();

        while self.peek_and(TokenKind::can_start_type)? {
            let ty = self.parse_simple_type()?;
            span = span.union(ty.span);
            params.push(ty.data);
        }

        Ok(Constructor {
            name,
            params: params.into_boxed_slice(),
            span,
        })
    }

    fn parse_type_definition(&mut self) -> ParseResult<UntypedExpr> {
        let span = self.expect(TokenKind::KwType)?;
        let Spanned { data: id, .. } = self.expect_id()?;

        let mut params = Vec::new();

        while !self.check(TokenKind::Eq) {
            let Spanned { data, .. } = self.expect_id()?;
            params.push(Ty::Named {
                name: PathIdent::Ident(data),
                args: Rc::from([]),
            });
        }

        self.expect(TokenKind::Eq)?;

        let mut constructors = Vec::new();
        let mut span = span;
        self.next_if_match(TokenKind::Bar);
        loop {
            let c = self.parse_constructor()?;
            span = span.union(c.span);
            constructors.push(c);
            if self.next_if_match(TokenKind::Bar).is_none() {
                break;
            }
        }

        Ok(UntypedExpr::untyped(
            UntypedExprKind::Type {
                name:         id,
                parameters:   params.into_boxed_slice(),
                constructors: constructors.into_boxed_slice(),
            },
            span,
        ))
    }

    fn parse_match_arm(&mut self) -> ParseResult<Spanned<UntypedMatchArm>> {
        let pat = self.parse_pat()?;
        self.expect(TokenKind::Arrow)?;
        let expr = self.parse_expr()?;
        let span = pat.span.union(expr.span);

        Ok(Spanned::new(UntypedMatchArm::new(pat, expr), span))
    }

    fn parse_match(&mut self) -> ParseResult<UntypedExpr> {
        let mut span = self.expect(TokenKind::KwMatch)?;
        let expr = self.parse_expr()?;
        self.expect(TokenKind::KwWith)?;

        let mut arms = Vec::new();

        while self.peek_and(TokenKind::can_start_pat)? {
            let arm = self.parse_match_arm()?;
            arms.push(arm.data);
            span = span.union(arm.span);
            if let Some(tk) = self.next_if_match(TokenKind::Comma) {
                span = span.union(tk);
            } else {
                break;
            }
        }

        Ok(UntypedExpr::untyped(
            UntypedExprKind::Match {
                expr: Box::new(expr),
                arms: arms.into_boxed_slice(),
            },
            span,
        ))
    }

    fn parse_if(&mut self) -> ParseResult<UntypedExpr> {
        let span = self.expect(TokenKind::KwIf)?;
        let cond = self.parse_expr()?;

        self.expect(TokenKind::KwThen)?;
        let then = self.parse_expr()?;

        self.expect(TokenKind::KwElse)?;
        let otherwise = self.parse_expr()?;
        let span = span.union(otherwise.span);

        Ok(UntypedExpr::untyped(
            UntypedExprKind::If {
                cond:      Box::new(cond),
                then:      Box::new(then),
                otherwise: Box::new(otherwise),
            },
            span,
        ))
    }

    fn try_parse_integer(&mut self) -> Option<ParseResult<Spanned<i64>>> {
        if let Some(span) = self.next_if_match(TokenKind::Minus) {
            let mut int = match self.expect_integer() {
                Ok(int) => int,
                Err(err) => return Some(Err(err)),
            };
            int.span = span.union(int.span);
            return Some(Ok(int.map(|int| -int)));
        }

        match self.peek()?.copied() {
            Ok(Token {
                data: TokenKind::Integer(int),
                span,
            }) => {
                self.next();
                Some(Ok(Spanned::new(int, span)))
            }
            Err(err) => Some(Err(err)),
            _ => None,
        }
    }

    fn parse_range_pat(&mut self, lhs: i64, lhs_span: Span) -> ParseResult<UntypedPat> {
        if let Some(span) = self.next_if_match(TokenKind::DotDot) {
            match self.try_parse_integer() {
                Some(rhs) => {
                    let rhs = rhs?;
                    let span = lhs_span.union(rhs.span);
                    Ok(UntypedPat::untyped(
                        UntypedPatKind::IntRange(IntRangePat::Exclusive(lhs, rhs.data)),
                        span,
                    ))
                }
                None => Ok(UntypedPat::untyped(
                    UntypedPatKind::IntRange(IntRangePat::From(lhs)),
                    lhs_span.union(span),
                )),
            }
        } else if let Some(span) = self.next_if_match(TokenKind::DotDotEq) {
            let rhs = self.try_parse_integer().ok_or_else(|| {
                Spanned::new(ParseError::ExpectedPattern(TokenKind::DotDotEq), span)
            })??;
            let span = lhs_span.union(rhs.span);
            Ok(UntypedPat::untyped(
                UntypedPatKind::IntRange(IntRangePat::Inclusive(lhs, rhs.data)),
                span,
            ))
        } else {
            Ok(UntypedPat::untyped(UntypedPatKind::Int(lhs), lhs_span))
        }
    }

    fn parse_simple_pat(&mut self) -> ParseResult<UntypedPat> {
        if let Some(int) = self.try_parse_integer() {
            let int = int?;
            return self.parse_range_pat(int.data, int.span);
        }

        let Token { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::DotDot => {
                let int = self.expect_integer()?;
                let span = span.union(int.span);
                Ok(UntypedPat::untyped(
                    UntypedPatKind::IntRange(IntRangePat::To(int.data)),
                    span,
                ))
            }
            TokenKind::DotDotEq => {
                let int = self.expect_integer()?;
                let span = span.union(int.span);
                Ok(UntypedPat::untyped(
                    UntypedPatKind::IntRange(IntRangePat::ToInclusive(int.data)),
                    span,
                ))
            }
            TokenKind::KwTrue => Ok(UntypedPat::untyped(UntypedPatKind::Bool(true), span)),
            TokenKind::KwFalse => Ok(UntypedPat::untyped(UntypedPatKind::Bool(false), span)),
            TokenKind::LParen => {
                if let Some(rspan) = self.next_if_match(TokenKind::RParen) {
                    Ok(UntypedPat::untyped(UntypedPatKind::Unit, span.union(rspan)))
                } else {
                    let t = self.parse_pat()?;
                    let span = span.union(self.expect(TokenKind::RParen)?);
                    Ok(UntypedPat::untyped(t.kind, span))
                }
            }
            TokenKind::Ident(name) => {
                if self.next_if_match(TokenKind::Dot).is_some() {
                    let member = self.expect_id()?;
                    let span = span.union(member.span);
                    let name = PathIdent::Module(ModuleIdent::new(name, member.data));
                    let kind = UntypedPatKind::Constructor {
                        name,
                        args: Box::from([]),
                    };
                    Ok(UntypedPat::untyped(kind, span))
                } else {
                    let name = PathIdent::Ident(name);
                    let kind = UntypedPatKind::Constructor {
                        name,
                        args: Box::from([]),
                    };
                    Ok(UntypedPat::untyped(kind, span))
                }
            }
            TokenKind::Underscore => Ok(UntypedPat::untyped(UntypedPatKind::Wild, span)),
            _ => Err(Spanned::new(ParseError::ExpectedPattern(data), span)),
        }
    }

    fn parse_type_pat(&mut self) -> ParseResult<UntypedPat> {
        let simple = self.parse_simple_pat()?;

        let UntypedPatKind::Constructor { name, .. } = simple.kind else {
            return Ok(simple);
        };

        let mut span = simple.span;
        let mut args = Vec::new();
        while self.peek_and(TokenKind::can_start_pat)? {
            let pat = self.parse_simple_pat()?;
            span = span.union(pat.span);
            args.push(pat);
        }
        let args = args.into_boxed_slice();
        Ok(UntypedPat::untyped(
            UntypedPatKind::Constructor { name, args },
            span,
        ))
    }

    fn parse_pat(&mut self) -> ParseResult<UntypedPat> {
        let mut pat = self.parse_type_pat()?;

        if self.next_if_match(TokenKind::Bar).is_some() {
            let mut span = pat.span;
            let mut pats = vec![pat];

            loop {
                let pat = self.parse_type_pat()?;
                pats.push(pat);
                if self.next_if_match(TokenKind::Bar).is_none() {
                    break;
                }
            }

            span = span.union(pats.last().unwrap().span);

            pat = UntypedPat::untyped(UntypedPatKind::Or(pats.into_boxed_slice()), span);
        }

        Ok(pat)
    }

    fn parse_let(&mut self) -> ParseResult<UntypedExpr> {
        let mut span = self.expect(TokenKind::KwLet)?;
        let Spanned {
            data: name,
            span: name_span,
        } = self.expect_id()?;

        let mut parametes = Vec::new();
        while !self.check(TokenKind::Eq) {
            let Spanned { data, span } = self.expect_id()?;
            let param = UntypedParam::untyped(data, span);
            parametes.push(param);
        }
        self.expect(TokenKind::Eq)?;
        let expr = self.parse_expr()?;
        let body = if self.next_if_match(TokenKind::KwIn).is_some() {
            let body = self.parse_expr()?;
            span = span.union(body.span);
            Some(body)
        } else {
            None
        };

        Ok(UntypedExpr::untyped(
            UntypedExprKind::Let {
                name,
                name_span,
                params: parametes.into_boxed_slice(),
                expr: Box::new(expr),
                body: body.map(Box::new),
            },
            span,
        ))
    }

    fn parse_fn(&mut self) -> ParseResult<UntypedExpr> {
        let span = self.expect(TokenKind::KwFn)?;
        let Spanned {
            data: name,
            span: name_span,
        } = self.expect_id()?;

        self.expect(TokenKind::Arrow)?;

        let expr = self.parse_expr()?;

        let span = span.union(expr.span);

        let param = UntypedParam::untyped(name, name_span);

        Ok(UntypedExpr::untyped(
            UntypedExprKind::Fn {
                param,
                expr: Box::new(expr),
            },
            span,
        ))
    }
}

impl Iterator for Parser<'_> {
    type Item = ParseResult<UntypedExpr>;

    fn next(&mut self) -> Option<Self::Item> {
        self.parse()
    }
}
