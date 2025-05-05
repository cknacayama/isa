use std::rc::Rc;

use super::ast::{
    Constructor, Expr, ExprKind, Fixity, Import, ImportClause, ImportWildcard, LetBind, ListPat,
    MatchArm, Module, Operator, Param, Pat, PatKind, Path, RangePat, Stmt, StmtKind, Val,
};
use super::error::ParseError;
use super::infer::{ClassConstraint, ClassConstraintSet};
use super::token::{Ident, Token, TokenKind};
use super::types::Ty;
use crate::global::Symbol;
use crate::span::{Span, Spanned};

pub type ParseResult<T> = Result<T, Spanned<ParseError>>;

#[derive(Debug)]
pub struct Parser {
    tokens:    Vec<Token>,
    cur:       usize,
    last_span: Span,
}

impl Parser {
    #[must_use]
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            cur: 0,
            last_span: Span::default(),
        }
    }

    fn check(&mut self, t: TokenKind) -> bool {
        self.peek().is_some_and(|tk| tk.data == t)
    }

    fn peek(&mut self) -> Option<Token> {
        self.tokens
            .get(self.cur)
            .inspect(|tk| self.last_span = tk.span)
            .copied()
    }

    fn peek_and<P>(&mut self, p: P) -> bool
    where
        P: FnOnce(TokenKind) -> bool,
    {
        self.peek_kind().is_some_and(p)
    }

    fn peek_kind(&mut self) -> Option<TokenKind> {
        self.peek().map(|tk| tk.data)
    }

    const fn eat(&mut self) {
        self.cur += 1;
    }

    #[must_use]
    fn next(&mut self) -> Option<Token> {
        let tk = self.peek()?;
        self.cur += 1;
        Some(tk)
    }

    fn next_or_eof(&mut self) -> ParseResult<Token> {
        self.next()
            .ok_or_else(|| Spanned::new(ParseError::UnexpectedEof, self.last_span))
    }

    fn next_if_match(&mut self, tk: TokenKind) -> Option<Span> {
        if self.check(tk) {
            Some(self.next().unwrap().span)
        } else {
            None
        }
    }

    fn next_if_map<F, T>(&mut self, f: F) -> Option<T>
    where
        F: FnOnce(Token) -> Option<T>,
    {
        let token = self.peek()?;

        f(token).inspect(|_| {
            self.eat();
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

    fn expect_op(&mut self) -> ParseResult<Ident> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Operator(ident) => Ok(Ident::new(ident, t.span)),
            _ => Err(t.map(ParseError::ExpectedId)),
        })
    }

    fn expect_id(&mut self) -> ParseResult<Ident> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Ident(ident) => Ok(Ident::new(ident, t.span)),
            _ => Err(t.map(ParseError::ExpectedId)),
        })
    }

    fn expect_integer(&mut self) -> ParseResult<Spanned<i64>> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Integer(int) => Ok(t.map(|_| int)),
            _ => Err(t.map(ParseError::ExpectedInt)),
        })
    }

    fn try_parse_module(&mut self) -> Option<ParseResult<Module<()>>> {
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
            let mut path = Path::from_one(id);
            let mut wildcard = ImportWildcard::Nil;
            while self.next_if_match(TokenKind::ColonColon).is_some() {
                let Some(tk) = self.peek() else {
                    return Err(Spanned::new(ParseError::UnexpectedEof, self.last_span));
                };
                match tk.data {
                    TokenKind::Ident(ident) => {
                        self.eat();
                        if !path.push(Ident::new(ident, tk.span)) {
                            return Err(Spanned::new(ParseError::PathToLong, self.last_span));
                        }
                    }
                    TokenKind::Underscore => {
                        self.eat();
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
            imports.push(Import { path, wildcard });
            if self.next_if_match(TokenKind::Comma).is_none() {
                break;
            }
        }

        self.expect(TokenKind::RBrace)?;

        Ok(ImportClause(imports.into_boxed_slice()))
    }

    /// parses one module
    fn parse_module(&mut self) -> ParseResult<Module<()>> {
        let span = self.expect(TokenKind::KwModule)?;
        let no_prelude = self.next_if_match(TokenKind::At).is_some();
        let name = self.expect_id()?;

        let imports = if self.next_if_match(TokenKind::KwWith).is_some() {
            self.parse_import_clause()?
        } else {
            ImportClause::default()
        };

        let mut stmts = vec![self.parse_stmt()?];

        while !self.check(TokenKind::KwModule) {
            let Some(expr) = self.parse() else { break };
            stmts.push(expr?);
        }

        let [.., stmt] = stmts.as_slice() else {
            unreachable!()
        };
        let span = span.union(stmt.span);

        Ok(Module::new(no_prelude, name, imports, stmts, span))
    }

    pub fn parse_all(&mut self) -> ParseResult<Vec<Module<()>>> {
        std::iter::from_fn(|| self.try_parse_module()).collect()
    }

    pub fn parse(&mut self) -> Option<ParseResult<Stmt<()>>> {
        if self.peek().is_some() {
            Some(self.parse_stmt())
        } else {
            None
        }
    }

    fn parse_stmt(&mut self) -> ParseResult<Stmt<()>> {
        let span = self.last_span;

        let stmt = match self
            .peek()
            .ok_or_else(|| Spanned::new(ParseError::UnexpectedEof, span))?
            .data
        {
            TokenKind::KwType => self.parse_type_definition(),
            TokenKind::KwVal => self.parse_val_expr(),
            TokenKind::KwAlias => self.parse_alias(),
            TokenKind::KwClass => self.parse_class(),
            TokenKind::KwLet => self.parse_let_stmt(),
            TokenKind::KwInstance => self.parse_instance(),
            tk => {
                if let Some(fixity) = Fixity::from_tk(tk) {
                    let op = self.parse_operator(fixity)?;
                    let span = op.span;
                    Ok(Stmt::new(StmtKind::Operator(op), span))
                } else {
                    self.parse_expr_stmt()
                }
            }
        }?;

        self.expect(TokenKind::Semicolon)?;

        Ok(stmt)
    }

    fn parse_let_stmt(&mut self) -> ParseResult<Stmt<()>> {
        let Spanned { data: bind, span } = self.parse_let_bind(true)?;
        if self.next_if_match(TokenKind::KwIn).is_some() {
            let body = self.parse_expr()?;
            let span = span.union(body.span);
            let kind = StmtKind::Semi(Expr::untyped(
                ExprKind::Let {
                    bind: Box::new(bind),
                    body: Box::new(body),
                },
                span,
            ));
            Ok(Stmt::new(kind, span))
        } else {
            let kind = StmtKind::Let(bind);
            Ok(Stmt::new(kind, span))
        }
    }

    fn parse_expr_stmt(&mut self) -> ParseResult<Stmt<()>> {
        let expr = self.parse_expr()?;
        let span = expr.span;

        Ok(Stmt::new(StmtKind::Semi(expr), span))
    }

    fn parse_operator(&mut self, fixity: Fixity) -> ParseResult<Operator> {
        let span = self.next().unwrap().span;
        let Spanned {
            data: prec,
            span: prec_span,
        } = self.expect_integer()?;
        let prec = u8::try_from(prec)
            .map_err(|_| Spanned::new(ParseError::PrecendenceLimit(prec), prec_span))?;
        let (set, params) = self.parse_constraint_set()?;
        self.expect(TokenKind::LParen)?;
        let op = self.expect_op()?;
        self.expect(TokenKind::RParen)?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        let span = span.union(ty.span);

        Ok(Operator {
            fixity,
            prec,
            params,
            set,
            op,
            ty: ty.data,
            span,
        })
    }

    fn parse_class(&mut self) -> ParseResult<Stmt<()>> {
        let mut span = self.expect(TokenKind::KwClass)?;
        let (set, _) = self.parse_constraint_set()?;
        let name = self.expect_id()?;
        let instance = self.expect_id()?;
        let instance = Ty::Named {
            name: Path::from_one(instance),
            args: Rc::from([]),
        };
        let (signatures, defaults, ops) = if self.next_if_match(TokenKind::Eq).is_some() {
            let mut signatures = Vec::new();
            let mut ops = Vec::new();
            let mut defaults = Vec::new();
            loop {
                match self.peek_kind() {
                    Some(TokenKind::KwVal) => {
                        let val = self.parse_val()?;
                        span = span.union(val.span);
                        signatures.push(val);
                    }
                    Some(TokenKind::KwLet) => {
                        let val = self.parse_let_bind(true)?;
                        span = span.union(val.span);
                        defaults.push(val.data);
                    }
                    Some(tk) => {
                        if let Some(fixity) = Fixity::from_tk(tk) {
                            let op = self.parse_operator(fixity)?;
                            span = span.union(op.span);
                            ops.push(op);
                        } else {
                            break;
                        }
                    }
                    _ => break,
                }
                if let Some(c_span) = self.next_if_match(TokenKind::Comma) {
                    span = span.union(c_span);
                }
            }
            if signatures.is_empty() && ops.is_empty() {
                return Err(Spanned::new(
                    ParseError::ExpectedToken {
                        expected: TokenKind::KwVal,
                        got:      self.peek().map(|tk| tk.data),
                    },
                    span,
                ));
            }
            (
                signatures.into_boxed_slice(),
                defaults.into_boxed_slice(),
                ops.into_boxed_slice(),
            )
        } else {
            Default::default()
        };

        Ok(Stmt::new(
            StmtKind::Class {
                set,
                name,
                instance,
                signatures,
                ops,
                defaults,
            },
            span,
        ))
    }

    fn parse_instance(&mut self) -> ParseResult<Stmt<()>> {
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
                } = self.parse_let_bind(true)?;
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
                        got:      self.peek().map(|tk| tk.data),
                    },
                    span,
                ));
            }
            impls.into_boxed_slice()
        } else {
            Box::default()
        };

        Ok(Stmt::new(
            StmtKind::Instance {
                params,
                set,
                class: name,
                instance,
                impls,
            },
            span,
        ))
    }

    fn parse_alias(&mut self) -> ParseResult<Stmt<()>> {
        let span = self.expect(TokenKind::KwAlias)?;
        let name = self.expect_id()?;
        let mut params = Vec::new();
        while !self.check(TokenKind::Eq) {
            let ident = self.expect_id()?;
            params.push(Ty::Named {
                name: Path::from_one(ident),
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

        Ok(Stmt::new(
            StmtKind::Alias {
                name,
                parameters,
                ty,
            },
            span,
        ))
    }

    fn parse_constraint_set(&mut self) -> ParseResult<(ClassConstraintSet, Box<[Ty]>)> {
        if self.next_if_match(TokenKind::LBrace).is_none() {
            return Ok((ClassConstraintSet::new(), Box::new([])));
        }

        let mut constrs = Vec::new();
        let mut params = Vec::new();

        while !self.check(TokenKind::RBrace) {
            let (id, span) = self.parse_path()?;
            if let Some(Token {
                data: TokenKind::Ident(ident),
                span: ident_span,
            }) = self.peek()
            {
                self.eat();
                let name = Path::from_one(Ident { ident, span });
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

        Ok((ClassConstraintSet { constrs }, params.into_boxed_slice()))
    }

    fn parse_val(&mut self) -> ParseResult<Val> {
        let span = self.expect(TokenKind::KwVal)?;
        let (set, params) = self.parse_constraint_set()?;
        let name = self.expect_id()?;
        self.expect(TokenKind::Colon)?;
        let Spanned {
            data: ty,
            span: ty_span,
        } = self.parse_type()?;
        let span = span.union(ty_span);

        Ok(Val {
            params,
            set,
            name,
            ty,
            span,
        })
    }

    fn parse_val_expr(&mut self) -> ParseResult<Stmt<()>> {
        let val = self.parse_val()?;
        let span = val.span;
        Ok(Stmt::new(StmtKind::Val(val), span))
    }

    fn parse_expr(&mut self) -> ParseResult<Expr<()>> {
        let mut lhs = self.parse_prefix()?;

        // We assume all infix operators to be left associative
        // this will be resolved right before type checking
        while let Some(op) =
            self.next_if_map(|tk| tk.data.as_operator().map(|op| Ident::new(op, tk.span)))
        {
            let rhs = self.parse_prefix()?;
            let span = lhs.span.union(rhs.span);
            lhs = Expr::untyped(
                ExprKind::Infix {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> ParseResult<Expr<()>> {
        match self.peek() {
            Some(Token {
                data: TokenKind::Operator(op),
                span,
            }) => {
                self.eat();
                let expr = self.parse_prefix()?;
                let op = Ident::new(op, span);
                let span = span.union(expr.span);
                let kind = ExprKind::Prefix {
                    op,
                    expr: Box::new(expr),
                };

                Ok(Expr::untyped(kind, span))
            }

            _ => self.parse_call(),
        }
    }

    fn parse_call(&mut self) -> ParseResult<Expr<()>> {
        let mut expr = self.parse_prim()?;

        while self.peek_and(|tk| tk.can_start_expr()) {
            let arg = self.parse_prim()?;
            let span = expr.span.union(arg.span);
            expr = Expr::untyped(
                ExprKind::Call {
                    callee: Box::new(expr),
                    arg:    Box::new(arg),
                },
                span,
            );
        }

        Ok(expr)
    }

    fn parse_prim(&mut self) -> ParseResult<Expr<()>> {
        let last_span = self.last_span;
        let Token { data, span } = self
            .peek()
            .ok_or_else(|| Spanned::new(ParseError::UnexpectedEof, last_span))?;

        match data {
            TokenKind::KwLet => self.parse_let(),
            TokenKind::Backslash => self.parse_fn(),
            TokenKind::KwIf => self.parse_if(),
            TokenKind::KwMatch => self.parse_match(),
            TokenKind::LBracket => self.parse_list(),
            TokenKind::LParen => self.parse_tuple_or_operator(),
            TokenKind::Integer(lit) => {
                self.eat();
                Ok(Expr::untyped(ExprKind::Int(lit), span))
            }
            TokenKind::Real(lit) => {
                self.eat();
                Ok(Expr::untyped(ExprKind::Real(lit), span))
            }
            TokenKind::Char(lit) => {
                self.eat();
                Ok(Expr::untyped(ExprKind::Char(lit), span))
            }
            TokenKind::String(s) => {
                self.eat();
                Ok(Expr::untyped(ExprKind::String(s), span))
            }
            TokenKind::Ident(_) => {
                let (path, span) = self.parse_path()?;
                Ok(Expr::untyped(ExprKind::Path(path), span))
            }
            TokenKind::KwTrue => {
                self.eat();
                Ok(Expr::untyped(ExprKind::Bool(true), span))
            }
            TokenKind::KwFalse => {
                self.eat();
                Ok(Expr::untyped(ExprKind::Bool(false), span))
            }
            kind => Err(Spanned::new(ParseError::ExpectedExpr(kind), span)),
        }
    }

    fn parse_tuple_or_operator(&mut self) -> ParseResult<Expr<()>> {
        let span = self.expect(TokenKind::LParen)?;

        let mut exprs = Vec::new();

        if let Some((op, op_span)) = self.next_if_map(|tk| match tk.data {
            TokenKind::Operator(op) => Some((op, span)),
            _ => None,
        }) {
            if let Some(rspan) = self.next_if_match(TokenKind::RParen) {
                let kind = ExprKind::Operator(Ident::new(op, op_span));
                return Ok(Expr::untyped(kind, span.union(rspan)));
            }
            let expr = self.parse_prefix()?;
            let op = Ident::new(op, span);
            let span = span.union(expr.span);
            let kind = ExprKind::Prefix {
                op,
                expr: Box::new(expr),
            };
            exprs.push(Expr::untyped(kind, span));
            self.next_if_match(TokenKind::Comma);
        }

        while !self.check(TokenKind::RParen) {
            let expr = self.parse_expr()?;
            exprs.push(expr);
            if self.next_if_match(TokenKind::Comma).is_none() {
                break;
            }
        }

        let span = span.union(self.expect(TokenKind::RParen)?);

        if exprs.len() == 1 {
            let kind = ExprKind::Paren(Box::new(exprs.pop().unwrap()));
            Ok(Expr::untyped(kind, span))
        } else {
            Ok(Expr::untyped(
                ExprKind::Tuple(exprs.into_boxed_slice()),
                span,
            ))
        }
    }

    fn parse_list(&mut self) -> ParseResult<Expr<()>> {
        let span = self.expect(TokenKind::LBracket)?;

        let mut exprs = Vec::new();
        while !self.check(TokenKind::RBracket) {
            let expr = self.parse_expr()?;
            exprs.push(expr);
            if self.next_if_match(TokenKind::Comma).is_none() {
                break;
            }
        }

        let span = span.union(self.expect(TokenKind::RBracket)?);

        let kind = ExprKind::List(exprs.into_boxed_slice());

        Ok(Expr::untyped(kind, span))
    }

    fn parse_path(&mut self) -> ParseResult<(Path, Span)> {
        let first = self.expect_id()?;
        self.parse_path_from(first)
    }

    fn parse_path_from(&mut self, first: Ident) -> ParseResult<(Path, Span)> {
        let mut span = first.span;
        let mut path = Path::from_one(first);

        while self.next_if_match(TokenKind::ColonColon).is_some() {
            let id = self.expect_id()?;
            span = span.union(id.span);
            if !path.push(id) {
                return Err(Spanned::new(ParseError::PathToLong, span));
            }
        }

        Ok((path, span))
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

                if types.len() == 1 {
                    let ty = types.pop().unwrap();
                    Ok(Spanned::new(ty, span))
                } else {
                    Ok(Spanned::new(Ty::Tuple(types.into()), span))
                }
            }
            TokenKind::KwInt => Ok(Spanned::new(Ty::Int, span)),
            TokenKind::KwBool => Ok(Spanned::new(Ty::Bool, span)),
            TokenKind::KwReal => Ok(Spanned::new(Ty::Real, span)),
            TokenKind::KwChar => Ok(Spanned::new(Ty::Char, span)),
            TokenKind::Ident(ident) => {
                let (path, span) = self.parse_path_from(Ident { ident, span })?;

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

        match simple.data {
            Ty::Named { name, args } if args.is_empty() => {
                let mut span = simple.span;
                let mut params = Vec::new();
                while self.peek_and(|tk| tk.can_start_type()) {
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

    fn parse_constructor(&mut self) -> ParseResult<Constructor<()>> {
        let name = self.expect_id()?;
        let mut span = name.span;

        let mut params = Vec::new();

        while self.peek_and(|tk| tk.can_start_type()) {
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

    fn parse_type_definition(&mut self) -> ParseResult<Stmt<()>> {
        let span = self.expect(TokenKind::KwType)?;
        let name = self.expect_id()?;

        let params = std::iter::from_fn(|| {
            self.next_if_map(|tk| {
                tk.data.as_ident().map(|ident| Ty::Named {
                    name: Path::from_one(Ident::new(ident, tk.span)),
                    args: Rc::from([]),
                })
            })
        })
        .collect::<Vec<_>>();

        let mut constructors = Vec::new();
        let mut span = span;
        self.expect(TokenKind::Eq)?;
        self.next_if_match(TokenKind::Bar);
        loop {
            let c = self.parse_constructor()?;
            span = span.union(c.span);
            constructors.push(c);
            if self.next_if_match(TokenKind::Bar).is_none() {
                break;
            }
        }

        Ok(Stmt::new(
            StmtKind::Type {
                name,
                parameters: params.into_boxed_slice(),
                constructors: constructors.into_boxed_slice(),
            },
            span,
        ))
    }

    fn parse_match_arm(&mut self) -> ParseResult<Spanned<MatchArm<()>>> {
        let pat = self.parse_pat()?;
        self.expect(TokenKind::Arrow)?;
        let expr = self.parse_expr()?;
        let span = pat.span.union(expr.span);

        Ok(Spanned::new(MatchArm::new(pat, expr), span))
    }

    fn parse_match(&mut self) -> ParseResult<Expr<()>> {
        let mut span = self.expect(TokenKind::KwMatch)?;
        let expr = self.parse_expr()?;
        self.expect(TokenKind::KwWith)?;

        let mut arms = Vec::new();

        while self.peek_and(|tk| tk.can_start_pat()) {
            let arm = self.parse_match_arm()?;
            arms.push(arm.data);
            span = span.union(arm.span);
            if let Some(tk) = self.next_if_match(TokenKind::Comma) {
                span = span.union(tk);
            } else {
                break;
            }
        }

        Ok(Expr::untyped(
            ExprKind::Match {
                expr: Box::new(expr),
                arms: arms.into_boxed_slice(),
            },
            span,
        ))
    }

    fn parse_if(&mut self) -> ParseResult<Expr<()>> {
        let span = self.expect(TokenKind::KwIf)?;
        let cond = self.parse_expr()?;

        self.expect(TokenKind::KwThen)?;
        let then = self.parse_expr()?;

        self.expect(TokenKind::KwElse)?;
        let otherwise = self.parse_expr()?;
        let span = span.union(otherwise.span);

        Ok(Expr::untyped(
            ExprKind::If {
                cond:      Box::new(cond),
                then:      Box::new(then),
                otherwise: Box::new(otherwise),
            },
            span,
        ))
    }

    fn try_parse_char(&mut self) -> Option<Spanned<u8>> {
        let Token {
            data: TokenKind::Char(c),
            span,
        } = self.peek()?
        else {
            return None;
        };
        Some(Spanned::new(c, span))
    }

    fn try_parse_number<T, Parse>(&mut self, parse: Parse) -> Option<ParseResult<Spanned<T>>>
    where
        T: std::ops::Neg<Output = T>,
        Parse: FnOnce(Token) -> Option<Spanned<T>>,
    {
        let Some(span) = self.next_if_map(|tk| match tk.data {
            TokenKind::Operator(op) if op == Symbol::intern("-") => Some(tk.span),
            _ => None,
        }) else {
            return self.next_if_map(parse).map(Result::Ok);
        };

        let Some(int) = self.next_if_map(parse) else {
            return Some(Err(Spanned::new(
                ParseError::ExpectedPattern(TokenKind::Operator(Symbol::intern("-"))),
                span,
            )));
        };

        Some(Ok(Spanned::new(-int.data, span.union(int.span))))
    }

    fn try_parse_real(&mut self) -> Option<ParseResult<Spanned<f64>>> {
        self.try_parse_number(|tk| {
            if let TokenKind::Real(real) = tk.data {
                Some(Spanned::new(real, tk.span))
            } else {
                None
            }
        })
    }

    fn try_parse_integer(&mut self) -> Option<ParseResult<Spanned<i64>>> {
        self.try_parse_number(|tk| {
            if let TokenKind::Integer(int) = tk.data {
                Some(Spanned::new(int, tk.span))
            } else {
                None
            }
        })
    }

    fn parse_range_pat<T, Kind, RangeKind, Expect>(
        &mut self,
        lhs: T,
        lhs_span: Span,
        kind: Kind,
        range_kind: RangeKind,
        mut expect: Expect,
    ) -> ParseResult<Pat<()>>
    where
        RangeKind: FnOnce(RangePat<T>) -> PatKind<()>,
        Kind: FnOnce(T) -> PatKind<()>,
        Expect: FnMut(&mut Self) -> Option<ParseResult<Spanned<T>>>,
    {
        if let Some(span) = self.next_if_match(TokenKind::DotDot) {
            match expect(self) {
                Some(rhs) => {
                    let rhs = rhs?;
                    let span = lhs_span.union(rhs.span);
                    Ok(Pat::untyped(
                        range_kind(RangePat::Exclusive(lhs, rhs.data)),
                        span,
                    ))
                }
                None => Ok(Pat::untyped(
                    range_kind(RangePat::From(lhs)),
                    lhs_span.union(span),
                )),
            }
        } else if let Some(span) = self.next_if_match(TokenKind::DotDotEq) {
            let rhs = expect(self).ok_or_else(|| {
                Spanned::new(ParseError::ExpectedPattern(TokenKind::DotDotEq), span)
            })??;
            let span = lhs_span.union(rhs.span);
            Ok(Pat::untyped(
                range_kind(RangePat::Inclusive(lhs, rhs.data)),
                span,
            ))
        } else {
            Ok(Pat::untyped(kind(lhs), lhs_span))
        }
    }

    fn parse_int_range_pat(&mut self, lhs: i64, lhs_span: Span) -> ParseResult<Pat<()>> {
        self.parse_range_pat(
            lhs,
            lhs_span,
            PatKind::Int,
            PatKind::IntRange,
            Self::try_parse_integer,
        )
    }

    fn parse_real_range_pat(&mut self, lhs: f64, lhs_span: Span) -> ParseResult<Pat<()>> {
        self.parse_range_pat(
            lhs,
            lhs_span,
            PatKind::Real,
            PatKind::RealRange,
            Self::try_parse_real,
        )
    }

    fn parse_char_range_pat(&mut self, lhs: u8, lhs_span: Span) -> ParseResult<Pat<()>> {
        self.parse_range_pat(lhs, lhs_span, PatKind::Char, PatKind::CharRange, |this| {
            this.try_parse_char().map(Result::Ok)
        })
    }

    fn parse_to_range_pat(&mut self, span: Span) -> ParseResult<Pat<()>> {
        if let Some(char) = self.try_parse_char() {
            let span = span.union(char.span);
            return Ok(Pat::untyped(
                PatKind::CharRange(RangePat::To(char.data)),
                span,
            ));
        }

        let minus = self
            .next_if_map(|tk| match tk.data {
                TokenKind::Operator(op) if op == Symbol::intern("-") => Some(tk.span),
                _ => None,
            })
            .is_some();

        if let Some(real) = self.try_parse_real() {
            let mut real = real?;
            if minus {
                real.data = -real.data;
            }
            let span = span.union(real.span);
            Ok(Pat::untyped(
                PatKind::RealRange(RangePat::To(real.data)),
                span,
            ))
        } else {
            let mut int = self.expect_integer()?;
            if minus {
                int.data = -int.data;
            }
            let span = span.union(int.span);
            Ok(Pat::untyped(
                PatKind::IntRange(RangePat::To(int.data)),
                span,
            ))
        }
    }

    fn parse_to_inclusive_range_pat(&mut self, span: Span) -> ParseResult<Pat<()>> {
        if let Some(char) = self.try_parse_char() {
            let span = span.union(char.span);
            return Ok(Pat::untyped(
                PatKind::CharRange(RangePat::ToInclusive(char.data)),
                span,
            ));
        }

        let minus = self
            .next_if_map(|tk| match tk.data {
                TokenKind::Operator(op) if op == Symbol::intern("-") => Some(tk.span),
                _ => None,
            })
            .is_some();

        if let Some(real) = self.try_parse_real() {
            let mut real = real?;
            if minus {
                real.data = -real.data;
            }
            let span = span.union(real.span);
            Ok(Pat::untyped(
                PatKind::RealRange(RangePat::ToInclusive(real.data)),
                span,
            ))
        } else {
            let mut int = self.expect_integer()?;
            if minus {
                int.data = -int.data;
            }
            let span = span.union(int.span);
            Ok(Pat::untyped(
                PatKind::IntRange(RangePat::ToInclusive(int.data)),
                span,
            ))
        }
    }

    fn parse_simple_pat(&mut self) -> ParseResult<Pat<()>> {
        if let Some(c) = self.try_parse_char() {
            return self.parse_char_range_pat(c.data, c.span);
        }
        let minus = self.next_if_map(|tk| match tk.data {
            TokenKind::Operator(op) if op == Symbol::intern("-") => Some(tk.span),
            _ => None,
        });
        if let Some(int) = self.try_parse_integer() {
            let int = int?;
            if let Some(span) = minus {
                return self.parse_int_range_pat(-int.data, span.union(int.span));
            }
            return self.parse_int_range_pat(int.data, int.span);
        }
        if let Some(real) = self.try_parse_real() {
            let real = real?;
            if let Some(span) = minus {
                return self.parse_real_range_pat(-real.data, span.union(real.span));
            }
            return self.parse_real_range_pat(real.data, real.span);
        }
        if let Some(span) = minus {
            return Err(Spanned::new(
                ParseError::ExpectedPattern(TokenKind::Operator(Symbol::intern("-"))),
                span,
            ));
        }

        let Token { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::DotDot => self.parse_to_range_pat(span),
            TokenKind::DotDotEq => self.parse_to_inclusive_range_pat(span),
            TokenKind::KwTrue => Ok(Pat::untyped(PatKind::Bool(true), span)),
            TokenKind::KwFalse => Ok(Pat::untyped(PatKind::Bool(false), span)),
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
                    Ok(Pat {
                        span,
                        ..pats.pop().unwrap()
                    })
                } else {
                    Ok(Pat::untyped(PatKind::Tuple(pats.into_boxed_slice()), span))
                }
            }
            TokenKind::LBracket => self.parse_list_pat(span),
            TokenKind::Ident(ident) => {
                let (name, span) = self.parse_path_from(Ident { ident, span })?;
                Ok(Pat::untyped(
                    PatKind::Constructor {
                        name,
                        args: Box::from([]),
                    },
                    span,
                ))
            }
            TokenKind::Underscore => Ok(Pat::untyped(PatKind::Wild, span)),
            _ => Err(Spanned::new(ParseError::ExpectedPattern(data), span)),
        }
    }

    fn parse_list_pat(&mut self, span: Span) -> ParseResult<Pat<()>> {
        if let Some(close) = self.next_if_match(TokenKind::RBracket) {
            return Ok(Pat::untyped(PatKind::List(ListPat::Nil), span.union(close)));
        }

        let head = self.parse_pat()?;
        let span = span.union(self.expect(TokenKind::RBracket)?);

        let (kind, span) = if self.peek_and(|tk| tk.can_start_pat()) {
            let rest = self.parse_pat()?;
            let span = span.union(rest.span);
            (ListPat::Cons(Box::new(head), Box::new(rest)), span)
        } else {
            (ListPat::Single(Box::new(head)), span)
        };

        Ok(Pat::untyped(PatKind::List(kind), span))
    }

    fn parse_type_pat(&mut self) -> ParseResult<Pat<()>> {
        let simple = self.parse_simple_pat()?;

        let PatKind::Constructor { name, .. } = simple.kind else {
            return Ok(simple);
        };

        let mut span = simple.span;
        let mut args = Vec::new();
        while self.peek_and(|tk| tk.can_start_pat()) {
            let pat = self.parse_simple_pat()?;
            span = span.union(pat.span);
            args.push(pat);
        }
        let args = args.into_boxed_slice();
        Ok(Pat::untyped(PatKind::Constructor { name, args }, span))
    }

    fn parse_pat(&mut self) -> ParseResult<Pat<()>> {
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

            pat = Pat::untyped(PatKind::Or(pats.into_boxed_slice()), span);
        }

        Ok(pat)
    }

    fn parse_let_bind(&mut self, allow_operator: bool) -> ParseResult<Spanned<LetBind<()>>> {
        let span = self.expect(TokenKind::KwLet)?;
        let (name, operator) = if allow_operator && self.next_if_match(TokenKind::LParen).is_some()
        {
            let op = self.expect_op()?;
            self.expect(TokenKind::RParen)?;
            (op, true)
        } else {
            (self.expect_id()?, false)
        };

        let mut parametes = Vec::new();
        while !self.check(TokenKind::Eq) {
            let param = self.parse_simple_pat()?;
            let param = Param::new(param);
            parametes.push(param);
        }
        self.expect(TokenKind::Eq)?;
        let expr = self.parse_expr()?;
        let span = span.union(expr.span);

        Ok(Spanned::new(
            LetBind::new(operator, name, parametes.into_boxed_slice(), expr),
            span,
        ))
    }

    fn parse_let(&mut self) -> ParseResult<Expr<()>> {
        let Spanned { data: bind, span } = self.parse_let_bind(false)?;
        self.expect(TokenKind::KwIn)?;
        let body = self.parse_expr()?;
        let span = span.union(body.span);

        Ok(Expr::untyped(
            ExprKind::Let {
                bind: Box::new(bind),
                body: Box::new(body),
            },
            span,
        ))
    }

    fn parse_fn(&mut self) -> ParseResult<Expr<()>> {
        let span = self.expect(TokenKind::Backslash)?;
        let pat = self.parse_type_pat()?;

        self.expect(TokenKind::Arrow)?;

        let expr = self.parse_expr()?;

        let span = span.union(expr.span);

        let param = Param::new(pat);

        Ok(Expr::untyped(
            ExprKind::Fn {
                param,
                expr: Box::new(expr),
            },
            span,
        ))
    }
}
