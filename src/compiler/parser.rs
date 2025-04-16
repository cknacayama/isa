use std::iter::Peekable;
use std::rc::Rc;

use smallvec::smallvec;

use super::ast::untyped::{
    UntypedConstructor, UntypedExpr, UntypedExprKind, UntypedLetBind, UntypedMatchArm,
    UntypedModule, UntypedParam, UntypedPat, UntypedPatKind,
};
use super::ast::{
    BinOp, Constructor, Import, ImportClause, ImportWildcard, Path, RangePat, UnOp, ValDeclaration,
};
use super::error::ParseError;
use super::infer::{ClassConstraint, ClassConstraintSet};
use super::lexer::Lexer;
use super::token::{Ident, Token, TokenKind};
use super::types::Ty;
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
            self.next();
        })
    }

    fn expect(&mut self, expected: TokenKind) -> ParseResult<Span> {
        self.next_or_eof().and_then(|t| {
            if t.data == expected {
                Ok(t.span)
            } else {
                Err(t.map(|got| ParseError::ExpectedToken {
                    expected,
                    got: Some(got),
                }))
            }
        })
    }

    fn expect_id(&mut self) -> ParseResult<Ident> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Ident(ident) => Ok(Ident {
                ident,
                span: t.span,
            }),
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

    fn parse_import_clause(&mut self) -> ParseResult<ImportClause> {
        self.expect(TokenKind::LBrace)?;

        let mut imports = Vec::new();

        while !self.check(TokenKind::RBrace) {
            let id = self.expect_id()?;
            let mut segments = smallvec![id];
            let mut wildcard = ImportWildcard::Nil;
            while self.next_if_match(TokenKind::ColonColon).is_some() {
                let Some(tk) = self.peek().transpose()? else {
                    return Err(Spanned::new(ParseError::UnexpectedEof, self.last_span));
                };
                match tk.data {
                    TokenKind::Ident(ident) => {
                        segments.push(Ident {
                            ident,
                            span: tk.span,
                        });
                    }
                    TokenKind::Star => {
                        self.next();
                        wildcard = ImportWildcard::Wildcard;
                        break;
                    }
                    TokenKind::LBrace => {
                        let clause = self.parse_import_clause()?;
                        wildcard = ImportWildcard::Clause(clause);
                        break;
                    }
                    kind => return Err(Spanned::new(ParseError::ExpectedId(kind), tk.span)),
                }
            }
            let path = Path { segments };
            imports.push(Import { path, wildcard });
            if self.next_if_match(TokenKind::Comma).is_none() {
                break;
            }
        }

        self.expect(TokenKind::RBrace)?;

        Ok(ImportClause(imports.into_boxed_slice()))
    }

    /// parses one module
    fn parse_module(&mut self) -> ParseResult<UntypedModule> {
        let mut span = self.expect(TokenKind::KwModule)?;
        let name = self.expect_id()?;

        let imports = if self.next_if_match(TokenKind::KwWith).is_some() {
            self.parse_import_clause()?
        } else {
            ImportClause::default()
        };

        let mut exprs = vec![self.parse_semi_expr()?];

        while !self.check(TokenKind::KwModule) {
            let Some(expr) = self.parse() else { break };
            exprs.push(expr?);
        }

        if let [.., expr] = exprs.as_slice() {
            span = span.union(expr.span);
        }

        Ok(UntypedModule::new(name, imports, exprs, span))
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
            TokenKind::KwVal => self.parse_val_expr(),
            TokenKind::KwAlias => self.parse_alias(),
            TokenKind::KwClass => self.parse_class(),
            TokenKind::KwInstance => self.parse_instance(),
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

    fn parse_class(&mut self) -> ParseResult<UntypedExpr> {
        let mut span = self.expect(TokenKind::KwClass)?;
        let (set, _) = self.parse_constraint_set()?;
        let name = self.expect_id()?;
        let instance = self.expect_id()?;
        let (signatures, defaults) = if self.next_if_match(TokenKind::Eq).is_some() {
            let mut signatures = Vec::new();
            let mut defaults = Vec::new();
            loop {
                match self.peek().transpose()?.map(Token::data) {
                    Some(TokenKind::KwVal) => {
                        let val = self.parse_val()?;
                        span = span.union(val.span);
                        signatures.push(val);
                    }
                    Some(TokenKind::KwLet) => {
                        let val = self.parse_let_bind()?;
                        span = span.union(val.span);
                        defaults.push(val.data);
                    }
                    _ => break,
                }
                if let Some(c_span) = self.next_if_match(TokenKind::Comma) {
                    span = span.union(c_span);
                }
            }
            if signatures.is_empty() {
                return Err(Spanned::new(
                    ParseError::ExpectedToken {
                        expected: TokenKind::KwVal,
                        got:      self.peek().transpose()?.map(|tk| tk.data),
                    },
                    span,
                ));
            }
            (signatures.into_boxed_slice(), defaults.into_boxed_slice())
        } else {
            Default::default()
        };

        Ok(UntypedExpr::untyped(
            UntypedExprKind::Class {
                set,
                name,
                instance,
                signatures,
                defaults,
            },
            span,
        ))
    }

    fn parse_instance(&mut self) -> ParseResult<UntypedExpr> {
        let mut span = self.expect(TokenKind::KwInstance)?;
        let (set, params) = self.parse_constraint_set()?;
        let (name, _) = self.parse_path()?;
        let Spanned { data: instance, .. } = self.parse_type()?;

        let impls = if self.next_if_match(TokenKind::Eq).is_some() {
            let mut impls = Vec::new();
            while self.check(TokenKind::KwLet) {
                let Spanned {
                    data: bind,
                    span: bind_span,
                } = self.parse_let_bind()?;
                impls.push(bind);
                span = span.union(bind_span);
                if let Some(c_span) = self.next_if_match(TokenKind::Comma) {
                    span = span.union(c_span);
                }
            }
            if impls.is_empty() {
                return Err(Spanned::new(
                    ParseError::ExpectedToken {
                        expected: TokenKind::KwLet,
                        got:      self.peek().transpose()?.map(|tk| tk.data),
                    },
                    span,
                ));
            }
            impls.into_boxed_slice()
        } else {
            Box::default()
        };

        Ok(UntypedExpr::untyped(
            UntypedExprKind::Instance {
                params,
                set,
                class: name,
                instance,
                impls,
            },
            span,
        ))
    }

    fn parse_alias(&mut self) -> ParseResult<UntypedExpr> {
        let span = self.expect(TokenKind::KwAlias)?;
        let name = self.expect_id()?;
        let mut params = Vec::new();
        while !self.check(TokenKind::Eq) {
            let ident = self.expect_id()?;
            params.push(Ty::Named {
                name: Path::from_ident(ident),
                args: Rc::from([]),
            });
        }
        self.expect(TokenKind::Eq)?;
        let parameters = params.into_boxed_slice();
        let Spanned {
            data: ty,
            span: ty_span,
        } = self.parse_type()?;
        let span = span.union(ty_span);

        Ok(UntypedExpr::untyped(
            UntypedExprKind::Alias {
                name,
                parameters,
                ty,
            },
            span,
        ))
    }

    fn parse_constraint_set(&mut self) -> ParseResult<(ClassConstraintSet, Box<[Ty]>)> {
        if self.next_if_match(TokenKind::LBrace).is_none() {
            return Ok(Default::default());
        }

        let mut constrs = Vec::new();
        let mut params = Vec::new();

        while !self.check(TokenKind::RBrace) {
            let (id, span) = self.parse_path()?;
            if let Some(Token {
                data: TokenKind::Ident(ident),
                span: ident_span,
            }) = self.peek().transpose()?.copied()
            {
                self.next();
                let name = Path::from_ident(Ident { ident, span });
                let span = span.union(ident_span);
                constrs.push(ClassConstraint::new(
                    id,
                    Ty::Named {
                        name,
                        args: Rc::from([]),
                    },
                    span,
                ));
            } else {
                if id.as_ident().is_none() {
                    return Err(Spanned::new(ParseError::UnexpectedEof, span));
                }
                params.push(Ty::Named {
                    name: id,
                    args: Rc::from([]),
                });
            }
            if self.next_if_match(TokenKind::Comma).is_none() {
                break;
            }
        }

        self.expect(TokenKind::RBrace)?;
        self.expect(TokenKind::Rocket)?;

        Ok((ClassConstraintSet { constrs }, params.into_boxed_slice()))
    }

    fn parse_val(&mut self) -> ParseResult<ValDeclaration> {
        let span = self.expect(TokenKind::KwVal)?;
        let (set, params) = self.parse_constraint_set()?;
        let name = self.expect_id()?;
        self.expect(TokenKind::Colon)?;
        let Spanned {
            data: ty,
            span: ty_span,
        } = self.parse_type()?;
        let span = span.union(ty_span);

        Ok(ValDeclaration {
            params,
            set,
            name,
            ty,
            span,
        })
    }

    fn parse_val_expr(&mut self) -> ParseResult<UntypedExpr> {
        let val = self.parse_val()?;
        let span = val.span;
        Ok(UntypedExpr::untyped(UntypedExprKind::Val(val), span))
    }

    fn parse_expr(&mut self) -> ParseResult<UntypedExpr> {
        self.parse_pipe()
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

        while self.next_if_match(TokenKind::BarBar).is_some() {
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

        while self.next_if_match(TokenKind::AmpAmp).is_some() {
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
        let last_span = self.last_span;
        let Token { data, span } = *self
            .peek()
            .ok_or_else(|| Spanned::new(ParseError::UnexpectedEof, last_span))??;

        match data {
            TokenKind::KwLet => self.parse_let(),
            TokenKind::KwFn => self.parse_fn(),
            TokenKind::KwIf => self.parse_if(),
            TokenKind::KwMatch => self.parse_match(),
            TokenKind::LParen => {
                self.next();
                let mut exprs = Vec::new();
                while !self.check(TokenKind::RParen) {
                    let expr = self.parse_expr()?;
                    exprs.push(expr);
                    if self.next_if_match(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                let span = span.union(self.expect(TokenKind::RParen)?);

                if exprs.len() == 1 {
                    let mut expr = exprs.pop().unwrap();
                    expr.span = span;
                    Ok(expr)
                } else {
                    Ok(UntypedExpr::untyped(
                        UntypedExprKind::Tuple(exprs.into_boxed_slice()),
                        span,
                    ))
                }
            }
            TokenKind::Integer(lit) => {
                self.next();
                Ok(UntypedExpr::untyped(UntypedExprKind::Int(lit), span))
            }
            TokenKind::Char(lit) => {
                self.next();
                Ok(UntypedExpr::untyped(UntypedExprKind::Char(lit), span))
            }
            TokenKind::Ident(_) => {
                let (path, span) = self.parse_path()?;
                Ok(UntypedExpr::untyped(UntypedExprKind::Path(path), span))
            }
            TokenKind::KwTrue => {
                self.next();
                Ok(UntypedExpr::untyped(UntypedExprKind::Bool(true), span))
            }
            TokenKind::KwFalse => {
                self.next();
                Ok(UntypedExpr::untyped(UntypedExprKind::Bool(false), span))
            }
            kind => Err(Spanned::new(ParseError::ExpectedExpr(kind), span)),
        }
    }

    fn parse_path(&mut self) -> ParseResult<(Path, Span)> {
        let first = self.expect_id()?;
        let mut span = first.span;
        let mut segments = smallvec![first];

        while self.next_if_match(TokenKind::ColonColon).is_some() {
            let id = self.expect_id()?;
            span = span.union(id.span);
            segments.push(id);
        }

        Ok((Path { segments }, span))
    }

    fn parse_simple_type(&mut self) -> ParseResult<Spanned<Ty>> {
        let Spanned { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::LParen => {
                let mut types = Vec::new();
                while !self.check(TokenKind::RParen) {
                    let ty = self.parse_type()?;
                    types.push(ty.data);
                    if self.next_if_match(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                let span = span.union(self.expect(TokenKind::RParen)?);

                if types.is_empty() {
                    Ok(Spanned::new(Ty::Unit, span))
                } else if types.len() == 1 {
                    let ty = types.pop().unwrap();
                    Ok(Spanned::new(ty, span))
                } else {
                    Ok(Spanned::new(Ty::Tuple(types.into()), span))
                }
            }
            TokenKind::KwInt => Ok(Spanned::new(Ty::Int, span)),
            TokenKind::KwBool => Ok(Spanned::new(Ty::Bool, span)),
            TokenKind::KwChar => Ok(Spanned::new(Ty::Char, span)),
            TokenKind::Ident(ident) => {
                let mut span = span;
                let mut segments = smallvec![Ident { ident, span }];

                while self.next_if_match(TokenKind::ColonColon).is_some() {
                    let id = self.expect_id()?;
                    span = span.union(id.span);
                    segments.push(id);
                }

                Ok(Spanned::new(
                    Ty::Named {
                        name: Path { segments },
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

        match simple.data {
            Ty::Named { name, args } if args.is_empty() => {
                let mut span = simple.span;
                let mut params = Vec::new();
                while self.peek_and(TokenKind::can_start_type)? {
                    let ty = self.parse_simple_type()?;
                    span = span.union(ty.span);
                    params.push(ty.data);
                }
                let args = params.into();
                Ok(Spanned::new(Ty::Named { name, args }, span))
            }
            _ => Ok(simple),
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

    fn parse_constructor(&mut self) -> ParseResult<UntypedConstructor> {
        let name = self.expect_id()?;
        let mut span = name.span;

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
            ty: (),
        })
    }

    fn parse_type_definition(&mut self) -> ParseResult<UntypedExpr> {
        let span = self.expect(TokenKind::KwType)?;
        let name = self.expect_id()?;

        let mut params = Vec::new();

        while !self.check(TokenKind::Eq) {
            let name = self.expect_id()?;
            let span = name.span;
            params.push(Ty::Named {
                name: Path::from_ident(Ident {
                    ident: name.ident,
                    span,
                }),
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
                name,
                parameters: params.into_boxed_slice(),
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

    fn try_parse_char(&mut self) -> Option<ParseResult<Spanned<u8>>> {
        match self.peek()?.copied() {
            Ok(Token {
                data: TokenKind::Char(c),
                span,
            }) => {
                self.next();
                Some(Ok(Spanned::new(c, span)))
            }
            Err(err) => Some(Err(err)),
            _ => None,
        }
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

    fn parse_int_range_pat(&mut self, lhs: i64, lhs_span: Span) -> ParseResult<UntypedPat> {
        if let Some(span) = self.next_if_match(TokenKind::DotDot) {
            match self.try_parse_integer() {
                Some(rhs) => {
                    let rhs = rhs?;
                    let span = lhs_span.union(rhs.span);
                    Ok(UntypedPat::untyped(
                        UntypedPatKind::IntRange(RangePat::Exclusive(lhs, rhs.data)),
                        span,
                    ))
                }
                None => Ok(UntypedPat::untyped(
                    UntypedPatKind::IntRange(RangePat::From(lhs)),
                    lhs_span.union(span),
                )),
            }
        } else if let Some(span) = self.next_if_match(TokenKind::DotDotEq) {
            let rhs = self.try_parse_integer().ok_or_else(|| {
                Spanned::new(ParseError::ExpectedPattern(TokenKind::DotDotEq), span)
            })??;
            let span = lhs_span.union(rhs.span);
            Ok(UntypedPat::untyped(
                UntypedPatKind::IntRange(RangePat::Inclusive(lhs, rhs.data)),
                span,
            ))
        } else {
            Ok(UntypedPat::untyped(UntypedPatKind::Int(lhs), lhs_span))
        }
    }

    fn parse_char_range_pat(&mut self, lhs: u8, lhs_span: Span) -> ParseResult<UntypedPat> {
        if let Some(span) = self.next_if_match(TokenKind::DotDot) {
            match self.try_parse_char() {
                Some(rhs) => {
                    let rhs = rhs?;
                    let span = lhs_span.union(rhs.span);
                    Ok(UntypedPat::untyped(
                        UntypedPatKind::CharRange(RangePat::Exclusive(lhs, rhs.data)),
                        span,
                    ))
                }
                None => Ok(UntypedPat::untyped(
                    UntypedPatKind::CharRange(RangePat::From(lhs)),
                    lhs_span.union(span),
                )),
            }
        } else if let Some(span) = self.next_if_match(TokenKind::DotDotEq) {
            let rhs = self.try_parse_char().ok_or_else(|| {
                Spanned::new(ParseError::ExpectedPattern(TokenKind::DotDotEq), span)
            })??;
            let span = lhs_span.union(rhs.span);
            Ok(UntypedPat::untyped(
                UntypedPatKind::CharRange(RangePat::Inclusive(lhs, rhs.data)),
                span,
            ))
        } else {
            Ok(UntypedPat::untyped(UntypedPatKind::Char(lhs), lhs_span))
        }
    }

    fn parse_simple_pat(&mut self) -> ParseResult<UntypedPat> {
        if let Some(int) = self.try_parse_integer() {
            let int = int?;
            return self.parse_int_range_pat(int.data, int.span);
        }
        if let Some(c) = self.try_parse_char() {
            let c = c?;
            return self.parse_char_range_pat(c.data, c.span);
        }

        let Token { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::DotDot => {
                if let Some(char) = self.try_parse_char() {
                    let char = char?;
                    let span = span.union(char.span);
                    Ok(UntypedPat::untyped(
                        UntypedPatKind::CharRange(RangePat::To(char.data)),
                        span,
                    ))
                } else {
                    let int = self.expect_integer()?;
                    let span = span.union(int.span);
                    Ok(UntypedPat::untyped(
                        UntypedPatKind::IntRange(RangePat::To(int.data)),
                        span,
                    ))
                }
            }
            TokenKind::DotDotEq => {
                if let Some(char) = self.try_parse_char() {
                    let char = char?;
                    let span = span.union(char.span);
                    Ok(UntypedPat::untyped(
                        UntypedPatKind::CharRange(RangePat::ToInclusive(char.data)),
                        span,
                    ))
                } else {
                    let int = self.expect_integer()?;
                    let span = span.union(int.span);
                    Ok(UntypedPat::untyped(
                        UntypedPatKind::IntRange(RangePat::ToInclusive(int.data)),
                        span,
                    ))
                }
            }
            TokenKind::KwTrue => Ok(UntypedPat::untyped(UntypedPatKind::Bool(true), span)),
            TokenKind::KwFalse => Ok(UntypedPat::untyped(UntypedPatKind::Bool(false), span)),
            TokenKind::LParen => {
                let mut pats = Vec::new();
                while !self.check(TokenKind::RParen) {
                    let pat = self.parse_pat()?;
                    pats.push(pat);
                    if self.next_if_match(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                let span = span.union(self.expect(TokenKind::RParen)?);

                if pats.len() == 1 {
                    let mut pat = pats.pop().unwrap();
                    pat.span = span;
                    Ok(pat)
                } else {
                    Ok(UntypedPat::untyped(
                        UntypedPatKind::Tuple(pats.into_boxed_slice()),
                        span,
                    ))
                }
            }
            TokenKind::Ident(ident) => {
                let mut span = span;
                let mut segments = smallvec![Ident { ident, span }];

                while self.next_if_match(TokenKind::ColonColon).is_some() {
                    let id = self.expect_id()?;
                    span = span.union(id.span);
                    segments.push(id);
                }

                Ok(UntypedPat::untyped(
                    UntypedPatKind::Constructor {
                        name: Path { segments },
                        args: Box::from([]),
                    },
                    span,
                ))
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

    fn parse_let_bind(&mut self) -> ParseResult<Spanned<UntypedLetBind>> {
        let mut span = self.expect(TokenKind::KwLet)?;
        let name = self.expect_id()?;

        let mut parametes = Vec::new();
        while !self.check(TokenKind::Eq) {
            let param = self.expect_id()?;
            let param = UntypedParam::untyped(param);
            parametes.push(param);
        }
        self.expect(TokenKind::Eq)?;
        let expr = self.parse_expr()?;
        span = span.union(expr.span);

        Ok(Spanned::new(
            UntypedLetBind::new(name, parametes.into_boxed_slice(), Box::new(expr)),
            span,
        ))
    }

    fn parse_let(&mut self) -> ParseResult<UntypedExpr> {
        let Spanned {
            data: bind,
            mut span,
        } = self.parse_let_bind()?;
        let body = if self.next_if_match(TokenKind::KwIn).is_some() {
            let body = self.parse_expr()?;
            span = span.union(body.span);
            Some(body)
        } else {
            None
        };

        Ok(UntypedExpr::untyped(
            UntypedExprKind::Let {
                bind,
                body: body.map(Box::new),
            },
            span,
        ))
    }

    fn parse_fn(&mut self) -> ParseResult<UntypedExpr> {
        let span = self.expect(TokenKind::KwFn)?;
        let name = self.expect_id()?;

        self.expect(TokenKind::Arrow)?;

        let expr = self.parse_expr()?;

        let span = span.union(expr.span);

        let param = UntypedParam::untyped(name);

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
