use super::ast::{
    Expr, ExprKind, Fixity, HiConstraint, HiCtor, HiTy, HiTyKind, Ident, Import, ImportClause,
    ImportWildcard, LetBind, ListPat, MatchArm, Module, Operator, Param, Pat, PatKind, Path,
    RangePat, Stmt, StmtKind, Val,
};
use super::error::{ParseError, ParseErrorKind};
use super::token::{Token, TokenKind};
use crate::global::{Span, Symbol};
use crate::span::Spand;

pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug)]
pub struct Parser {
    tokens: Vec<Token>,
    cur:    usize,
}

impl Parser {
    #[must_use]
    pub const fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, cur: 0 }
    }

    fn last_span(&self) -> Span {
        self.tokens.last().map(|tk| tk.span).unwrap_or_default()
    }

    fn check(&self, t: TokenKind) -> bool {
        self.peek().is_some_and(|tk| tk.data == t)
    }

    fn peek(&self) -> Option<Token> {
        self.tokens.get(self.cur).copied()
    }

    fn peek_and<P>(&self, p: P) -> bool
    where
        P: FnOnce(TokenKind) -> bool,
    {
        self.peek().map(|tk| tk.data).is_some_and(p)
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
            .ok_or_else(|| ParseError::new(ParseErrorKind::UnexpectedEof, self.last_span()))
    }

    fn next_if_match(&mut self, tk: TokenKind) -> Option<Span> {
        match self.peek() {
            Some(t) if t.data == tk => {
                self.eat();
                Some(t.span)
            }
            _ => None,
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
        let t = self.next_or_eof()?;

        if t.data == expected {
            Ok(t.span)
        } else {
            Err(ParseError::new(
                ParseErrorKind::ExpectedToken {
                    expected,
                    got: Some(t.data),
                },
                t.span,
            ))
        }
    }

    fn expect_op(&mut self) -> ParseResult<Ident> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Operator(ident) => Ok(Ident::new(ident, t.span)),
            tk => Err(ParseError::new(ParseErrorKind::ExpectedId(tk), t.span)),
        })
    }

    fn expect_id(&mut self) -> ParseResult<Ident> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Ident(ident) => Ok(Ident::new(ident, t.span)),
            tk => Err(ParseError::new(ParseErrorKind::ExpectedId(tk), t.span)),
        })
    }

    fn expect_integer(&mut self) -> ParseResult<Spand<i64>> {
        self.next_or_eof().and_then(|t| match t.data {
            TokenKind::Integer(int) => Ok(t.map(|_| int)),
            tk => Err(ParseError::new(ParseErrorKind::ExpectedInt(tk), t.span)),
        })
    }

    fn parse_delimited_from<T>(
        &mut self,
        span: Span,
        delim: Delim,
        mut parse: impl FnMut(&mut Self) -> ParseResult<T>,
    ) -> ParseResult<(Vec<T>, Span)> {
        let mut data = Vec::new();

        while !self.check(delim.closing()) {
            let res = parse(self)?;
            data.push(res);
            if self.next_if_match(Delim::separator()).is_none() {
                break;
            }
        }

        let span = span.join(self.expect(delim.closing())?);

        Ok((data, span))
    }

    fn parse_delimited<T>(
        &mut self,
        delim: Delim,
        parse: impl FnMut(&mut Self) -> ParseResult<T>,
    ) -> ParseResult<(Vec<T>, Span)> {
        let span = self.expect(delim.opening())?;
        self.parse_delimited_from(span, delim, parse)
    }

    fn parse_import_clause(&mut self) -> ParseResult<(ImportClause, Span)> {
        let (imports, span) = self.parse_delimited(Delim::Brace, |parser| {
            let id = parser.expect_id()?;
            let mut path = Path::from_one(id);
            let mut wildcard = ImportWildcard::Nil;
            while parser.next_if_match(TokenKind::ColonColon).is_some() {
                let Some(tk) = parser.peek() else {
                    return Err(ParseError::new(
                        ParseErrorKind::UnexpectedEof,
                        parser.last_span(),
                    ));
                };
                match tk.data {
                    TokenKind::Ident(ident) => {
                        parser.eat();
                        path.push(Ident::new(ident, tk.span));
                    }
                    TokenKind::Underscore => {
                        parser.eat();
                        wildcard = ImportWildcard::Wildcard;
                        break;
                    }
                    TokenKind::LBrace => {
                        let (clause, _) = parser.parse_import_clause()?;
                        wildcard = ImportWildcard::Clause(clause);
                        break;
                    }
                    kind => return Err(ParseError::new(ParseErrorKind::ExpectedId(kind), tk.span)),
                }
            }
            Ok(Import { path, wildcard })
        })?;

        Ok((ImportClause(imports.into_boxed_slice()), span))
    }

    fn error_recover(&mut self) {
        while self.peek_and(|tk| !tk.recover_start_point()) {
            self.eat();
        }
    }

    /// parses one module
    fn parse_module(&mut self) -> Result<Module<()>, Vec<ParseError>> {
        let span = self.expect(TokenKind::KwModule)?;
        let no_prelude = self.next_if_match(TokenKind::At).is_some();
        let name = self.expect_id()?;
        let mut span = span.join(name.span);

        let imports = if self.next_if_match(TokenKind::KwWith).is_some() {
            let (imports, clause_span) = self.parse_import_clause()?;
            span = span.join(clause_span);
            imports
        } else {
            ImportClause::default()
        };

        let mut errors = Vec::new();
        let mut stmts = Vec::new();

        while !self.check(TokenKind::KwModule)
            && let Some(stmt) = self.parse()
        {
            match stmt {
                Ok(stmt) => stmts.push(stmt),
                Err(err) => {
                    errors.push(err);
                    self.error_recover();
                }
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        if let [.., stmt] = stmts.as_slice() {
            span = span.join(stmt.span);
        }

        Ok(Module::new(no_prelude, name, imports, stmts, span))
    }

    pub fn parse_all(self) -> Result<Vec<Module<()>>, Vec<ParseError>> {
        let mut folded = Vec::new();
        let mut errs = Vec::new();

        for item in self {
            match item {
                Ok(ok) => folded.push(ok),
                Err(err) => errs.extend(err),
            }
        }

        if errs.is_empty() {
            Ok(folded)
        } else {
            Err(errs)
        }
    }

    fn parse(&mut self) -> Option<ParseResult<Stmt<()>>> {
        if self.peek().is_some() {
            Some(self.parse_stmt())
        } else {
            None
        }
    }

    fn parse_stmt(&mut self) -> ParseResult<Stmt<()>> {
        let stmt = match self
            .peek()
            .ok_or_else(|| ParseError::new(ParseErrorKind::UnexpectedEof, self.last_span()))?
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
        let span = self.next().unwrap().span;
        let Spand { data: bind, span } = self.parse_let_bind::<true>(span)?;
        if self.next_if_match(TokenKind::KwIn).is_some() {
            let body = self.parse_expr()?;
            let span = span.join(body.span);
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
        let Spand {
            data: prec,
            span: prec_span,
        } = self.expect_integer()?;
        let prec = u8::try_from(prec)
            .map_err(|_| ParseError::new(ParseErrorKind::PrecendenceLimit(prec), prec_span))?;
        let (set, params) = self.parse_constraint_set()?;
        self.expect(TokenKind::LParen)?;
        let op = self.expect_op()?;
        self.expect(TokenKind::RParen)?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        let span = span.join(ty.span);

        Ok(Operator {
            fixity,
            prec,
            params,
            set,
            op,
            ty,
            span,
        })
    }

    fn parse_class(&mut self) -> ParseResult<Stmt<()>> {
        let span = self.expect(TokenKind::KwClass)?;
        let (set, _) = self.parse_constraint_set()?;
        let name = self.expect_id()?;
        let mut span = span.join(name.span);
        let parents = if self.next_if_match(TokenKind::Colon).is_some() {
            self.parse_class_constraint()?
                .into_iter()
                .map(|(class, _)| class)
                .collect()
        } else {
            Box::default()
        };

        let (signatures, defaults, ops) = if self.next_if_match(TokenKind::Eq).is_some() {
            let mut signatures = Vec::new();
            let mut ops = Vec::new();
            let mut defaults = Vec::new();
            loop {
                match self.peek() {
                    Some(Token {
                        data: TokenKind::KwVal,
                        ..
                    }) => {
                        let val = self.parse_val()?;
                        span = span.join(val.span);
                        signatures.push(val);
                    }
                    Some(Token {
                        data: TokenKind::KwLet,
                        span: let_span,
                    }) => {
                        self.eat();
                        let val = self.parse_let_bind::<true>(let_span)?;
                        span = span.join(val.span);
                        defaults.push(val.data);
                    }
                    Some(tk) => {
                        if let Some(fixity) = Fixity::from_tk(tk.data) {
                            let op = self.parse_operator(fixity)?;
                            span = span.join(op.span);
                            ops.push(op);
                        } else {
                            break;
                        }
                    }
                    _ => break,
                }
                if let Some(c_span) = self.next_if_match(TokenKind::Comma) {
                    span = span.join(c_span);
                }
            }
            if signatures.is_empty() && ops.is_empty() {
                return Err(ParseError::new(
                    ParseErrorKind::ExpectedToken {
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
                parents,
                signatures,
                ops,
                defaults,
            },
            span,
        ))
    }

    fn parse_instance(&mut self) -> ParseResult<Stmt<()>> {
        let span = self.expect(TokenKind::KwInstance)?;
        let (set, params) = self.parse_constraint_set()?;
        let instance = self.parse_type()?;
        self.expect(TokenKind::Colon)?;
        let (class, name_span) = self.parse_path()?;
        let mut span = span.join(name_span);

        let impls = if self.next_if_match(TokenKind::Eq).is_some() {
            let mut impls = Vec::new();
            while let Some(let_span) = self.next_if_match(TokenKind::KwLet) {
                let Spand {
                    data: bind,
                    span: bind_span,
                } = self.parse_let_bind::<true>(let_span)?;
                impls.push(bind);
                span = span.join(bind_span);
                if let Some(c_span) = self.next_if_match(TokenKind::Comma) {
                    span = span.join(c_span);
                }
            }
            if impls.is_empty() {
                return Err(ParseError::new(
                    ParseErrorKind::ExpectedToken {
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
                class,
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
            params.push(HiTy::new(
                HiTyKind::Named(Path::from_one(ident)),
                ident.span,
            ));
        }
        self.expect(TokenKind::Eq)?;
        let ty = self.parse_type()?;
        let span = span.join(ty.span);
        let params = params.into_boxed_slice();

        Ok(Stmt::new(StmtKind::Alias { name, params, ty }, span))
    }

    fn parse_constraint_set(&mut self) -> ParseResult<(Box<[HiConstraint]>, Box<[HiTy]>)> {
        if !self.check(TokenKind::LBrace) {
            return Ok(Default::default());
        }

        let mut constrs = Vec::new();
        let (params, _) = self.parse_delimited(Delim::Brace, |parser| {
            let name = parser.expect_id()?;
            let ty = HiTy::new(HiTyKind::Named(Path::from_one(name)), name.span);
            if parser.next_if_match(TokenKind::Colon).is_some() {
                let classes = parser.parse_class_constraint()?;
                for (class, span) in classes {
                    constrs.push(HiConstraint::new(class, ty.clone(), span));
                }
            }
            Ok(ty)
        })?;

        Ok((constrs.into_boxed_slice(), params.into_boxed_slice()))
    }

    fn parse_class_constraint(&mut self) -> ParseResult<Vec<(Path, Span)>> {
        if self.check(TokenKind::LBrace) {
            let (classes, _) = self.parse_delimited(Delim::Brace, Self::parse_path)?;
            Ok(classes)
        } else {
            Ok(vec![self.parse_path()?])
        }
    }

    fn parse_val(&mut self) -> ParseResult<Val> {
        let span = self.expect(TokenKind::KwVal)?;
        let (set, params) = self.parse_constraint_set()?;
        let name = self.expect_id()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        let span = span.join(ty.span);

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
            let span = lhs.span.join(rhs.span);
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
                let span = span.join(expr.span);
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
            let span = expr.span.join(arg.span);
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
        let Token { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::KwLet => self.parse_let(span),
            TokenKind::Backslash => self.parse_fn(span),
            TokenKind::KwIf => self.parse_if(span),
            TokenKind::KwMatch => self.parse_match(span),
            TokenKind::LBracket => self.parse_list(span),
            TokenKind::LParen => self.parse_tuple_or_operator(span),
            TokenKind::Integer(lit) => Ok(Expr::untyped(ExprKind::Int(lit), span)),
            TokenKind::Real(lit) => Ok(Expr::untyped(ExprKind::Real(lit), span)),
            TokenKind::Char(lit) => Ok(Expr::untyped(ExprKind::Char(lit), span)),
            TokenKind::String(s) => Ok(Expr::untyped(ExprKind::String(s), span)),
            TokenKind::Ident(ident) => {
                let (path, span) = self.parse_path_from(Ident { ident, span })?;
                Ok(Expr::untyped(ExprKind::Path(path), span))
            }
            TokenKind::KwTrue => Ok(Expr::untyped(ExprKind::Bool(true), span)),
            TokenKind::KwFalse => Ok(Expr::untyped(ExprKind::Bool(false), span)),
            kind => Err(ParseError::new(ParseErrorKind::ExpectedExpr(kind), span)),
        }
    }

    fn parse_tuple_or_operator(&mut self, span: Span) -> ParseResult<Expr<()>> {
        let mut exprs = Vec::new();

        if let Some((op, op_span)) = self.next_if_map(|tk| match tk.data {
            TokenKind::Operator(op) => Some((op, tk.span)),
            _ => None,
        }) {
            if let Some(rspan) = self.next_if_match(TokenKind::RParen) {
                let kind = ExprKind::Operator(Ident::new(op, op_span));
                return Ok(Expr::untyped(kind, span.join(rspan)));
            }
            let expr = self.parse_prefix()?;
            let op = Ident::new(op, span);
            let span = span.join(expr.span);
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

        let span = span.join(self.expect(TokenKind::RParen)?);

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

    fn parse_list(&mut self, span: Span) -> ParseResult<Expr<()>> {
        let (exprs, span) = self.parse_delimited_from(span, Delim::Bracket, Self::parse_expr)?;

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
            span = span.join(id.span);
            path.push(id);
        }

        Ok((path, span))
    }

    fn parse_simple_type(&mut self) -> ParseResult<HiTy> {
        let Spand { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::LParen => {
                let (mut types, span) =
                    self.parse_delimited_from(span, Delim::Paren, Self::parse_type)?;

                if types.len() == 1 {
                    let ty = types.pop().unwrap();
                    Ok(ty)
                } else {
                    Ok(HiTy::new(HiTyKind::Tuple(types.into_boxed_slice()), span))
                }
            }
            TokenKind::KwInt => Ok(HiTy::new(HiTyKind::Int, span)),
            TokenKind::KwBool => Ok(HiTy::new(HiTyKind::Bool, span)),
            TokenKind::KwReal => Ok(HiTy::new(HiTyKind::Real, span)),
            TokenKind::KwChar => Ok(HiTy::new(HiTyKind::Char, span)),
            TokenKind::Ident(ident) => {
                let (path, span) = self.parse_path_from(Ident { ident, span })?;

                Ok(HiTy::new(HiTyKind::Named(path), span))
            }
            TokenKind::KwSelf => Ok(HiTy::new(HiTyKind::This, span)),
            _ => Err(ParseError::new(ParseErrorKind::ExpectedType(data), span)),
        }
    }

    fn parse_polymorphic_type(&mut self) -> ParseResult<HiTy> {
        let simple = self.parse_simple_type()?;

        match simple.kind() {
            HiTyKind::Named(_) if self.peek_and(|tk| tk.can_start_type()) => {
                let mut span = simple.span;
                let mut params = Vec::new();
                while self.peek_and(|tk| tk.can_start_type()) {
                    let ty = self.parse_simple_type()?;
                    span = span.join(ty.span);
                    params.push(ty);
                }
                let args = params.into_boxed_slice();
                Ok(HiTy::new(
                    HiTyKind::Parametric {
                        ty: Box::new(simple),
                        args,
                    },
                    span,
                ))
            }
            HiTyKind::This if self.peek_and(|tk| tk.can_start_type()) => {
                let mut span = simple.span;
                let mut params = Vec::new();
                while self.peek_and(|tk| tk.can_start_type()) {
                    let ty = self.parse_simple_type()?;
                    span = span.join(ty.span);
                    params.push(ty);
                }
                let args = params.into_boxed_slice();
                Ok(HiTy::new(
                    HiTyKind::Parametric {
                        ty: Box::new(simple),
                        args,
                    },
                    span,
                ))
            }
            _ => Ok(simple),
        }
    }

    fn parse_type(&mut self) -> ParseResult<HiTy> {
        let simple = self.parse_polymorphic_type()?;

        if self.next_if_match(TokenKind::Arrow).is_some() {
            let ret = self.parse_type()?;
            let span = simple.span.join(ret.span);

            Ok(HiTy::new(
                HiTyKind::Fn {
                    param: Box::new(simple),
                    ret:   Box::new(ret),
                },
                span,
            ))
        } else {
            Ok(simple)
        }
    }

    fn parse_constructor(&mut self) -> ParseResult<HiCtor> {
        let name = self.expect_id()?;
        let mut span = name.span;

        let mut params = Vec::new();

        while self.peek_and(|tk| tk.can_start_type()) {
            let ty = self.parse_simple_type()?;
            span = span.join(ty.span);
            params.push(ty);
        }

        let params = params.into_boxed_slice();

        Ok(HiCtor { name, params, span })
    }

    fn parse_type_definition(&mut self) -> ParseResult<Stmt<()>> {
        let span = self.expect(TokenKind::KwType)?;
        let name = self.expect_id()?;

        let params = std::iter::from_fn(|| {
            self.next_if_map(|tk| {
                tk.data.as_ident().map(|ident| {
                    HiTy::new(
                        HiTyKind::Named(Path::from_one(Ident::new(ident, tk.span))),
                        tk.span,
                    )
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
            span = span.join(c.span);
            constructors.push(c);
            if self.next_if_match(TokenKind::Bar).is_none() {
                break;
            }
        }

        let params = params.into_boxed_slice();
        let constructors = constructors.into_boxed_slice();

        Ok(Stmt::new(
            StmtKind::Type {
                name,
                params,
                constructors,
            },
            span,
        ))
    }

    fn parse_match_arm(&mut self) -> ParseResult<Spand<MatchArm<()>>> {
        let pat = self.parse_pat()?;
        self.expect(TokenKind::Arrow)?;
        let expr = self.parse_expr()?;
        let span = pat.span.join(expr.span);

        Ok(Spand::new(MatchArm::new(pat, expr), span))
    }

    fn parse_match(&mut self, mut span: Span) -> ParseResult<Expr<()>> {
        let expr = self.parse_expr()?;
        self.expect(TokenKind::KwWith)?;

        let mut arms = Vec::new();

        while self.peek_and(|tk| tk.can_start_pat()) {
            let arm = self.parse_match_arm()?;
            arms.push(arm.data);
            span = span.join(arm.span);
            if let Some(tk) = self.next_if_match(TokenKind::Comma) {
                span = span.join(tk);
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

    fn parse_if(&mut self, span: Span) -> ParseResult<Expr<()>> {
        let cond = self.parse_expr()?;

        self.expect(TokenKind::KwThen)?;
        let then = self.parse_expr()?;

        self.expect(TokenKind::KwElse)?;
        let otherwise = self.parse_expr()?;
        let span = span.join(otherwise.span);

        Ok(Expr::untyped(
            ExprKind::If {
                cond:      Box::new(cond),
                then:      Box::new(then),
                otherwise: Box::new(otherwise),
            },
            span,
        ))
    }

    fn try_parse_char(&mut self) -> Option<Spand<u8>> {
        let Token {
            data: TokenKind::Char(c),
            span,
        } = self.peek()?
        else {
            return None;
        };
        self.eat();
        Some(Spand::new(c, span))
    }

    fn try_parse_number<T, Parse>(&mut self, parse: Parse) -> Option<ParseResult<Spand<T>>>
    where
        T: std::ops::Neg<Output = T>,
        Parse: FnOnce(Token) -> Option<Spand<T>>,
    {
        let Some(span) = self.next_if_map(|tk| match tk.data {
            TokenKind::Operator(op) if op == Symbol::intern("-") => Some(tk.span),
            _ => None,
        }) else {
            return self.next_if_map(parse).map(Result::Ok);
        };

        let Some(int) = self.next_if_map(parse) else {
            return Some(Err(ParseError::new(
                ParseErrorKind::ExpectedPattern(TokenKind::Operator(Symbol::intern("-"))),
                span,
            )));
        };

        Some(Ok(Spand::new(-int.data, span.join(int.span))))
    }

    fn try_parse_real(&mut self) -> Option<ParseResult<Spand<f64>>> {
        self.try_parse_number(|tk| {
            if let TokenKind::Real(real) = tk.data {
                Some(Spand::new(real, tk.span))
            } else {
                None
            }
        })
    }

    fn try_parse_integer(&mut self) -> Option<ParseResult<Spand<i64>>> {
        self.try_parse_number(|tk| {
            if let TokenKind::Integer(int) = tk.data {
                Some(Spand::new(int, tk.span))
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
        Expect: FnMut(&mut Self) -> Option<ParseResult<Spand<T>>>,
    {
        match self.peek() {
            Some(Token {
                data: TokenKind::DotDot,
                span,
            }) => {
                self.eat();
                match expect(self) {
                    Some(rhs) => {
                        let rhs = rhs?;
                        let span = lhs_span.join(rhs.span);
                        Ok(Pat::untyped(
                            range_kind(RangePat::Exclusive(lhs, rhs.data)),
                            span,
                        ))
                    }
                    None => Ok(Pat::untyped(
                        range_kind(RangePat::From(lhs)),
                        lhs_span.join(span),
                    )),
                }
            }
            Some(Token {
                data: TokenKind::DotDotEq,
                span,
            }) => {
                self.eat();
                let rhs = expect(self).ok_or_else(|| {
                    ParseError::new(ParseErrorKind::ExpectedPattern(TokenKind::DotDotEq), span)
                })??;
                let span = lhs_span.join(rhs.span);
                Ok(Pat::untyped(
                    range_kind(RangePat::Inclusive(lhs, rhs.data)),
                    span,
                ))
            }
            _ => Ok(Pat::untyped(kind(lhs), lhs_span)),
        }
    }

    fn parse_int_pat(&mut self, lhs: i64, lhs_span: Span) -> ParseResult<Pat<()>> {
        self.parse_range_pat(
            lhs,
            lhs_span,
            PatKind::Int,
            PatKind::IntRange,
            Self::try_parse_integer,
        )
    }

    fn parse_real_pat(&mut self, lhs: f64, lhs_span: Span) -> ParseResult<Pat<()>> {
        self.parse_range_pat(
            lhs,
            lhs_span,
            PatKind::Real,
            PatKind::RealRange,
            Self::try_parse_real,
        )
    }

    fn parse_char_pat(&mut self, lhs: u8, lhs_span: Span) -> ParseResult<Pat<()>> {
        self.parse_range_pat(lhs, lhs_span, PatKind::Char, PatKind::CharRange, |this| {
            this.try_parse_char().map(Result::Ok)
        })
    }

    fn parse_to_pat(&mut self, span: Span) -> ParseResult<Pat<()>> {
        if let Some(char) = self.try_parse_char() {
            let span = span.join(char.span);
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
            let span = span.join(real.span);
            Ok(Pat::untyped(
                PatKind::RealRange(RangePat::To(real.data)),
                span,
            ))
        } else {
            let mut int = self.expect_integer()?;
            if minus {
                int.data = -int.data;
            }
            let span = span.join(int.span);
            Ok(Pat::untyped(
                PatKind::IntRange(RangePat::To(int.data)),
                span,
            ))
        }
    }

    fn parse_to_inclusive_pat(&mut self, span: Span) -> ParseResult<Pat<()>> {
        if let Some(char) = self.try_parse_char() {
            let span = span.join(char.span);
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
            let span = span.join(real.span);
            Ok(Pat::untyped(
                PatKind::RealRange(RangePat::ToInclusive(real.data)),
                span,
            ))
        } else {
            let mut int = self.expect_integer()?;
            if minus {
                int.data = -int.data;
            }
            let span = span.join(int.span);
            Ok(Pat::untyped(
                PatKind::IntRange(RangePat::ToInclusive(int.data)),
                span,
            ))
        }
    }

    fn parse_simple_pat(&mut self) -> ParseResult<Pat<()>> {
        let Token { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::Char(c) => self.parse_char_pat(c, span),
            TokenKind::Integer(int) => self.parse_int_pat(int, span),
            TokenKind::Real(real) => self.parse_real_pat(real, span),
            TokenKind::Operator(op) if op == Symbol::intern("-") => {
                let next = self.next_or_eof()?;
                match next.data {
                    TokenKind::Integer(int) => self.parse_int_pat(-int, span),
                    TokenKind::Real(real) => self.parse_real_pat(-real, span),
                    tk => Err(ParseError::new(
                        ParseErrorKind::ExpectedPattern(tk),
                        next.span,
                    )),
                }
            }
            TokenKind::DotDot => self.parse_to_pat(span),
            TokenKind::DotDotEq => self.parse_to_inclusive_pat(span),
            TokenKind::KwTrue => Ok(Pat::untyped(PatKind::Bool(true), span)),
            TokenKind::KwFalse => Ok(Pat::untyped(PatKind::Bool(false), span)),
            TokenKind::LParen => {
                let (mut pats, span) =
                    self.parse_delimited_from(span, Delim::Paren, Self::parse_pat)?;

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
            _ => Err(ParseError::new(ParseErrorKind::ExpectedPattern(data), span)),
        }
    }

    fn parse_list_pat(&mut self, span: Span) -> ParseResult<Pat<()>> {
        if let Some(close) = self.next_if_match(TokenKind::RBracket) {
            return Ok(Pat::untyped(PatKind::List(ListPat::Nil), span.join(close)));
        }

        let head = self.parse_pat()?;
        let span = span.join(self.expect(TokenKind::RBracket)?);

        let (kind, span) = if self.peek_and(|tk| tk.can_start_pat()) {
            let rest = self.parse_pat()?;
            let span = span.join(rest.span);
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
            span = span.join(pat.span);
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

            span = span.join(pats.last().unwrap().span);

            pat = Pat::untyped(PatKind::Or(pats.into_boxed_slice()), span);
        }

        Ok(pat)
    }

    fn parse_let_bind<const OPERATOR: bool>(
        &mut self,
        span: Span,
    ) -> ParseResult<Spand<LetBind<()>>> {
        let (name, operator) = if OPERATOR && self.next_if_match(TokenKind::LParen).is_some() {
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
        let span = span.join(expr.span);

        Ok(Spand::new(
            LetBind::new(operator, name, parametes.into_boxed_slice(), expr),
            span,
        ))
    }

    fn parse_let(&mut self, span: Span) -> ParseResult<Expr<()>> {
        let Spand { data: bind, span } = self.parse_let_bind::<false>(span)?;
        self.expect(TokenKind::KwIn)?;
        let body = self.parse_expr()?;
        let span = span.join(body.span);

        Ok(Expr::untyped(
            ExprKind::Let {
                bind: Box::new(bind),
                body: Box::new(body),
            },
            span,
        ))
    }

    fn parse_fn(&mut self, span: Span) -> ParseResult<Expr<()>> {
        let pat = self.parse_type_pat()?;

        self.expect(TokenKind::Arrow)?;

        let expr = self.parse_expr()?;

        let span = span.join(expr.span);

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

#[derive(Clone, Copy)]
enum Delim {
    Paren,
    Brace,
    Bracket,
}

impl Delim {
    const fn opening(self) -> TokenKind {
        match self {
            Self::Paren => TokenKind::LParen,
            Self::Brace => TokenKind::LBrace,
            Self::Bracket => TokenKind::LBracket,
        }
    }

    const fn closing(self) -> TokenKind {
        match self {
            Self::Paren => TokenKind::RParen,
            Self::Brace => TokenKind::RBrace,
            Self::Bracket => TokenKind::RBracket,
        }
    }

    const fn separator() -> TokenKind {
        TokenKind::Comma
    }
}

impl Iterator for Parser {
    type Item = Result<Module<()>, Vec<ParseError>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.peek().is_some() {
            Some(self.parse_module())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::lexer::{LexResult, Lexer};

    macro_rules! assert_all {
        ($input:literal) => {
            insta::assert_debug_snapshot!(create_parser($input).parse_expr())
        };
        (stmt $input:literal) => {
            insta::assert_debug_snapshot!(create_parser($input).parse_stmt())
        };
    }

    #[track_caller]
    fn create_parser(input: &str) -> Parser {
        let tokens = Lexer::new(0, input).collect::<LexResult<_>>().unwrap();
        Parser::new(tokens)
    }

    #[test]
    fn numbers() {
        assert_all!("0000");
        assert_all!("0120");
        assert_all!("12");
        assert_all!("4.0");
        assert_all!("5.0");
        assert_all!("1.2");
        assert_all!("111.2");
    }

    #[test]
    fn idents() {
        assert_all!("_i");
        assert_all!("letf");
        assert_all!("vals");
        assert_all!("ifs");
        assert_all!("thenz");
        assert_all!("true10");
        assert_all!("false18");
        assert_all!("aint");
        assert_all!("lbool");
        assert_all!("_char");
        assert_all!("real_");
        assert_all!("Type");
        assert_all!("aliass");
        assert_all!("classes");
        assert_all!("_8instance");
        assert_all!("_01infix");
        assert_all!("_01infixl");
        assert_all!("_01infixr");
        assert_all!("mengoprefix");
        assert_all!("amatch");
        assert_all!("belse");
        assert_all!("cin");
        assert_all!("dwith");
        assert_all!("emodule");
        assert_all!("self");
    }

    #[test]
    fn chars() {
        assert_all!(r"'a'");
        assert_all!(r"'\n'");
        assert_all!(r"'\t'");
        assert_all!(r"'\r'");
        assert_all!(r"'\\'");
        assert_all!(r"'\''");
        assert_all!(r#"'\"'"#);
        assert_all!(r"'\0'");
        assert_all!(r"'1'");
    }

    #[test]
    fn strings() {
        assert_all!(r#""foo""#);
        assert_all!(r#""foo\n""#);
        assert_all!(r#""bar\r""#);
        assert_all!(r#""ba5\t""#);
        assert_all!(r#""ba3\"""#);
        assert_all!(r#""ba2\0a""#);
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
        assert_all!(stmt "let a = 10;");
        assert_all!(stmt "let fib n = match n with ..2 -> n, _ -> fib (n - 1) + fib (n - 2);");
        assert_all!(stmt "let foo (a,b,c) = a + b - c;");
        assert_all!(stmt "let bar _ _ _ = true;");
        assert_all!(stmt "let mengo _ _c _ = true;");
    }

    #[test]
    fn spaced_tokens() {
        assert_all!(
            "\n\n12 +\n\n// mengo mengo mengo mengo 123 && a aa^`\t\t\t\t\n//foo bar baz\n\n   13"
        );
    }
}
