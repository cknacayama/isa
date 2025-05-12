use std::rc::Rc;

use super::ast::{
    Constructor, Expr, ExprKind, Fixity, Import, ImportClause, ImportWildcard, LetBind, ListPat,
    MatchArm, Module, Operator, Param, Pat, PatKind, Path, RangePat, Stmt, StmtKind, Val,
};
use super::error::{ParseError, ParseErrorKind};
use super::infer::{ClassConstraint, ClassConstraintSet};
use super::token::{Ident, Token, TokenKind};
use super::types::Ty;
use crate::global::Symbol;
use crate::span::{Span, Spand};

pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug)]
pub struct Parser {
    tokens: Vec<Token>,
    cur:    usize,
    empty:  Rc<[Ty]>,
}

impl Parser {
    #[must_use]
    pub fn new() -> Self {
        Self {
            tokens: Vec::new(),
            cur:    0,
            empty:  Rc::new([]),
        }
    }

    fn last_span(&self) -> Span {
        self.tokens.last().map(|tk| tk.span).unwrap_or_default()
    }

    pub fn restart(&mut self, tokens: Vec<Token>) {
        self.tokens = tokens;
        self.cur = 0;
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
        self.peek_kind().is_some_and(p)
    }

    fn peek_kind(&self) -> Option<TokenKind> {
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
            .ok_or_else(|| ParseError::new(ParseErrorKind::UnexpectedEof, self.last_span()))
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
                        if !path.push(Ident::new(ident, tk.span)) {
                            return Err(ParseError::new(
                                ParseErrorKind::PathToLong,
                                parser.last_span(),
                            ));
                        }
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

    pub fn parse_all(&mut self) -> Result<Vec<Module<()>>, Vec<ParseError>> {
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
        let Spand { data: bind, span } = self.parse_let_bind(true)?;
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
        let Spand {
            data: ty,
            span: ty_span,
        } = self.parse_type()?;
        let span = span.join(ty_span);

        Ok(Operator {
            fixity,
            prec,
            params,
            set,
            op,
            ty,
            ty_span,
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
                match self.peek_kind() {
                    Some(TokenKind::KwVal) => {
                        let val = self.parse_val()?;
                        span = span.join(val.span);
                        signatures.push(val);
                    }
                    Some(TokenKind::KwLet) => {
                        let val = self.parse_let_bind(true)?;
                        span = span.join(val.span);
                        defaults.push(val.data);
                    }
                    Some(tk) => {
                        if let Some(fixity) = Fixity::from_tk(tk) {
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
        let Spand { data: instance, .. } = self.parse_type()?;
        self.expect(TokenKind::Colon)?;
        let (class, name_span) = self.parse_path()?;
        let mut span = span.join(name_span);

        let impls = if self.next_if_match(TokenKind::Eq).is_some() {
            let mut impls = Vec::new();
            while self.check(TokenKind::KwLet) {
                let Spand {
                    data: bind,
                    span: bind_span,
                } = self.parse_let_bind(true)?;
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
            params.push(Ty::Named {
                name: Path::from_one(ident),
                args: self.empty.clone(),
            });
        }
        self.expect(TokenKind::Eq)?;
        let params = params.into_boxed_slice();
        let Spand {
            data: ty,
            span: ty_span,
        } = self.parse_type()?;
        let span = span.join(ty_span);

        Ok(Stmt::new(StmtKind::Alias { name, params, ty }, span))
    }

    fn parse_constraint_set(&mut self) -> ParseResult<(ClassConstraintSet, Box<[Ty]>)> {
        let mut constrs = ClassConstraintSet::new();
        if !self.check(TokenKind::LBrace) {
            return Ok((constrs, Box::new([])));
        }

        let (params, _) = self.parse_delimited(Delim::Brace, |parser| {
            let name = parser.expect_id()?;
            let ty = Ty::Named {
                name: Path::from_one(name),
                args: parser.empty.clone(),
            };
            if parser.next_if_match(TokenKind::Colon).is_some() {
                let classes = parser.parse_class_constraint()?;
                for (class, span) in classes {
                    constrs.push(ClassConstraint::new(class, ty.clone(), span));
                }
            }
            Ok(ty)
        })?;

        Ok((constrs, params.into_boxed_slice()))
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
        let Spand {
            data: ty,
            span: ty_span,
        } = self.parse_type()?;
        let span = span.join(ty_span);

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
        let Token { data, span } = self
            .peek()
            .ok_or_else(|| ParseError::new(ParseErrorKind::UnexpectedEof, self.last_span()))?;

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
            kind => Err(ParseError::new(ParseErrorKind::ExpectedExpr(kind), span)),
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

    fn parse_list(&mut self) -> ParseResult<Expr<()>> {
        let (exprs, span) = self.parse_delimited(Delim::Bracket, Self::parse_expr)?;

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
            if !path.push(id) {
                return Err(ParseError::new(ParseErrorKind::PathToLong, span));
            }
        }

        Ok((path, span))
    }

    fn parse_simple_type(&mut self) -> ParseResult<Spand<Ty>> {
        let Spand { data, span } = self.next_or_eof()?;

        match data {
            TokenKind::LParen => {
                let (mut types, span) =
                    self.parse_delimited_from(span, Delim::Paren, |parser| {
                        parser.parse_type().map(|ty| ty.data)
                    })?;

                if types.len() == 1 {
                    let ty = types.pop().unwrap();
                    Ok(Spand::new(ty, span))
                } else {
                    Ok(Spand::new(Ty::Tuple(types.into()), span))
                }
            }
            TokenKind::KwInt => Ok(Spand::new(Ty::Int, span)),
            TokenKind::KwBool => Ok(Spand::new(Ty::Bool, span)),
            TokenKind::KwReal => Ok(Spand::new(Ty::Real, span)),
            TokenKind::KwChar => Ok(Spand::new(Ty::Char, span)),
            TokenKind::Ident(ident) => {
                let (path, span) = self.parse_path_from(Ident { ident, span })?;

                Ok(Spand::new(
                    Ty::Named {
                        name: path,
                        args: self.empty.clone(),
                    },
                    span,
                ))
            }
            TokenKind::KwSelf => Ok(Spand::new(Ty::This(self.empty.clone()), span)),
            _ => Err(ParseError::new(ParseErrorKind::ExpectedType(data), span)),
        }
    }

    fn parse_polymorphic_type(&mut self) -> ParseResult<Spand<Ty>> {
        let simple = self.parse_simple_type()?;

        match simple.data {
            Ty::Named { name, args } if args.is_empty() => {
                let mut span = simple.span;
                let mut params = Vec::new();
                while self.peek_and(|tk| tk.can_start_type()) {
                    let ty = self.parse_simple_type()?;
                    span = span.join(ty.span);
                    params.push(ty.data);
                }
                let args = params.into();
                Ok(Spand::new(Ty::Named { name, args }, span))
            }
            Ty::This(args) if args.is_empty() => {
                let mut span = simple.span;
                let mut params = Vec::new();
                while self.peek_and(|tk| tk.can_start_type()) {
                    let ty = self.parse_simple_type()?;
                    span = span.join(ty.span);
                    params.push(ty.data);
                }
                let args = params.into();
                Ok(Spand::new(Ty::This(args), span))
            }
            _ => Ok(simple),
        }
    }

    fn parse_type(&mut self) -> ParseResult<Spand<Ty>> {
        let simple = self.parse_polymorphic_type()?;

        if self.next_if_match(TokenKind::Arrow).is_some() {
            let ret = self.parse_type()?;
            let span = simple.span.join(ret.span);

            Ok(Spand::new(
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
            span = span.join(ty.span);
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
            let args = self.empty.clone();
            self.next_if_map(|tk| {
                tk.data.as_ident().map(|ident| Ty::Named {
                    name: Path::from_one(Ident::new(ident, tk.span)),
                    args,
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

        Ok(Stmt::new(
            StmtKind::Type {
                name,
                params: params.into_boxed_slice(),
                constructors: constructors.into_boxed_slice(),
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

    fn parse_match(&mut self) -> ParseResult<Expr<()>> {
        let mut span = self.expect(TokenKind::KwMatch)?;
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

    fn parse_if(&mut self) -> ParseResult<Expr<()>> {
        let span = self.expect(TokenKind::KwIf)?;
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
        if let Some(span) = self.next_if_match(TokenKind::DotDot) {
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
        } else if let Some(span) = self.next_if_match(TokenKind::DotDotEq) {
            let rhs = expect(self).ok_or_else(|| {
                ParseError::new(ParseErrorKind::ExpectedPattern(TokenKind::DotDotEq), span)
            })??;
            let span = lhs_span.join(rhs.span);
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

    fn parse_to_inclusive_range_pat(&mut self, span: Span) -> ParseResult<Pat<()>> {
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
                return self.parse_int_range_pat(-int.data, span.join(int.span));
            }
            return self.parse_int_range_pat(int.data, int.span);
        }
        if let Some(real) = self.try_parse_real() {
            let real = real?;
            if let Some(span) = minus {
                return self.parse_real_range_pat(-real.data, span.join(real.span));
            }
            return self.parse_real_range_pat(real.data, real.span);
        }
        if let Some(span) = minus {
            return Err(ParseError::new(
                ParseErrorKind::ExpectedPattern(TokenKind::Operator(Symbol::intern("-"))),
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

    fn parse_let_bind(&mut self, allow_operator: bool) -> ParseResult<Spand<LetBind<()>>> {
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
        let span = span.join(expr.span);

        Ok(Spand::new(
            LetBind::new(operator, name, parametes.into_boxed_slice(), expr),
            span,
        ))
    }

    fn parse_let(&mut self) -> ParseResult<Expr<()>> {
        let Spand { data: bind, span } = self.parse_let_bind(false)?;
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

    fn parse_fn(&mut self) -> ParseResult<Expr<()>> {
        let span = self.expect(TokenKind::Backslash)?;
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
