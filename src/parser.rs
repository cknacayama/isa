use crate::{
    ast::*,
    ctx::{Ctx, ProcSig},
    error::{Loc, ParseError, ParseErrorData, ParseResult, Span},
    token::{Token, TokenData},
    types::{BinOp, Type, TypeError, UnOp},
};

#[derive(Debug)]
pub struct Parser<'p, 'i> {
    tokens: &'p [Token<'i>],
    cursor: usize,

    ctxs: Vec<Ctx<'i>>,

    cur_proc: Option<Type>,
}

impl<'p, 'i> Parser<'p, 'i> {
    pub fn new(tokens: &'p [Token<'i>]) -> Self {
        Self {
            tokens,
            cursor: 0,
            ctxs: vec![Ctx::new()],
            cur_proc: None,
        }
    }

    #[inline]
    fn begin_scope(&mut self) {
        self.ctxs.push(Ctx::new());
    }

    #[inline]
    fn end_scope(&mut self) -> Option<Ctx<'i>> {
        self.ctxs.pop()
    }

    #[inline]
    fn add_local(&mut self, name: &'i str, ty: Type) -> Option<Type> {
        self.ctxs.last_mut().unwrap().add_local(name, ty)
    }

    #[inline]
    fn add_proc(&mut self, name: &'i str, sig: ProcSig) -> Option<ProcSig> {
        self.ctxs.first_mut().unwrap().add_proc(name, sig)
    }

    #[inline]
    fn get_local(&self, name: &'i str) -> Option<&Type> {
        for ctx in self.ctxs.iter().rev() {
            if let Some(ty) = ctx.get_local(name) {
                return Some(ty);
            }
        }

        None
    }

    #[inline]
    fn get_proc(&self, name: &'i str) -> Option<&ProcSig> {
        self.ctxs.first().unwrap().get_proc(name)
    }

    #[inline]
    fn peek(&self) -> Option<&Token<'i>> {
        self.tokens.get(self.cursor)
    }

    #[inline]
    fn peek_or_eof(&self) -> ParseResult<&Token<'i>> {
        self.peek()
            .ok_or(self.make_err(ParseErrorData::UnexpectedEof))
    }

    #[inline]
    fn peek_next(&self) -> Option<&Token<'i>> {
        self.tokens.get(self.cursor + 1)
    }

    #[inline]
    fn peek_binop(&self) -> Option<BinOp> {
        match self.peek()?.data {
            TokenData::Plus => Some(BinOp::Add),
            TokenData::Minus => Some(BinOp::Sub),
            TokenData::Star => Some(BinOp::Mul),
            TokenData::Slash => Some(BinOp::Div),
            TokenData::Percent => Some(BinOp::Mod),

            TokenData::EqualEqual => Some(BinOp::Eq),
            TokenData::BangEqual => Some(BinOp::Neq),
            TokenData::Less => Some(BinOp::Lt),
            TokenData::LessEqual => Some(BinOp::Leq),
            TokenData::Greater => Some(BinOp::Gt),
            TokenData::GreaterEqual => Some(BinOp::Geq),

            TokenData::Amp => Some(BinOp::BitAnd),
            TokenData::Pipe => Some(BinOp::BitOr),
            TokenData::Caret => Some(BinOp::BitXor),
            TokenData::LessLess => Some(BinOp::BitShl),
            TokenData::GreaterGreater => Some(BinOp::BitShr),

            TokenData::AmpAmp => Some(BinOp::BoolAnd),
            TokenData::PipePipe => Some(BinOp::BoolOr),

            TokenData::Equal => Some(BinOp::Assign),

            _ => None,
        }
    }

    #[inline]
    fn peek_unop(&self) -> Option<UnOp> {
        match self.peek()?.data {
            TokenData::Minus => Some(UnOp::Neg),
            TokenData::Tilde => Some(UnOp::BitNot),
            TokenData::Bang => Some(UnOp::BoolNot),
            TokenData::KwUnit => Some(UnOp::Cast(Type::Unit)),
            TokenData::KwInt => Some(UnOp::Cast(Type::Int)),
            TokenData::KwFloat => Some(UnOp::Cast(Type::Float)),
            TokenData::KwChar => Some(UnOp::Cast(Type::Char)),
            TokenData::KwBool => Some(UnOp::Cast(Type::Bool)),
            TokenData::KwString => Some(UnOp::Cast(Type::String)),
            _ => None,
        }
    }

    #[inline]
    fn check_cur(&self, token: TokenData<'static>) -> bool {
        self.peek().map(|t| t.data) == Some(token)
    }

    #[inline]
    fn match_cur(&mut self, token: TokenData<'static>) -> bool {
        if self.peek().map(|t| t.data) == Some(token) {
            self.cursor += 1;
            true
        } else {
            false
        }
    }

    #[inline]
    fn next(&mut self) -> Option<&Token<'i>> {
        self.cursor += 1;
        self.tokens.get(self.cursor - 1)
    }

    #[inline]
    fn advance(&mut self) -> Option<Span> {
        let span = self.peek()?.span;

        self.cursor += 1;

        Some(span)
    }

    #[inline]
    fn make_err(&self, data: ParseErrorData) -> ParseError {
        let loc = if let Some(token) = self.peek() {
            token.span.start
        } else {
            Loc { line: 0, col: 0 }
        };

        ParseError::new(data, loc)
    }

    #[inline]
    fn expect(&mut self, token: TokenData<'static>) -> ParseResult<Span> {
        if self.peek_or_eof()?.data == token {
            Ok(self.advance().unwrap())
        } else {
            Err(self.make_err(ParseErrorData::ExpectedToken(token)))
        }
    }

    #[inline]
    fn expect_ident(&mut self) -> ParseResult<(&'i str, Span)> {
        match self.peek_or_eof()?.data {
            TokenData::Ident(ident) => Ok((ident, self.advance().unwrap())),
            _ => Err(self.make_err(ParseErrorData::ExpectedIdent)),
        }
    }

    #[inline]
    fn expect_type(&mut self) -> ParseResult<(Type, Span)> {
        match self.peek_or_eof()?.data {
            TokenData::KwInt => Ok((Type::Int, self.advance().unwrap())),
            TokenData::KwFloat => Ok((Type::Float, self.advance().unwrap())),
            TokenData::KwChar => Ok((Type::Char, self.advance().unwrap())),
            TokenData::KwBool => Ok((Type::Bool, self.advance().unwrap())),
            TokenData::KwString => Ok((Type::String, self.advance().unwrap())),
            TokenData::KwUnit => Ok((Type::Unit, self.advance().unwrap())),
            _ => Err(self.make_err(ParseErrorData::ExpectedType)),
        }
    }

    #[inline]
    fn type_check_binop(&self, op: BinOp, lhs: Type, rhs: Type) -> ParseResult<Type> {
        match op.type_of(lhs, rhs) {
            Ok(ty) => Ok(ty),
            Err(err) => Err(self.make_err(ParseErrorData::TypeError(err))),
        }
    }

    #[inline]
    fn type_check_unop(&self, op: UnOp, ty: Type) -> ParseResult<Type> {
        match op.type_of(ty) {
            Ok(ty) => Ok(ty),
            Err(err) => Err(self.make_err(ParseErrorData::TypeError(err))),
        }
    }

    #[inline]
    fn decl(&mut self) -> ParseResult<Ast<'i>> {
        match self.peek_or_eof()?.data {
            TokenData::KwProc => self.proc_decl(),
            _ => Err(self.make_err(ParseErrorData::ExpectedDecl)),
        }
    }

    #[inline]
    fn stmt(&mut self) -> ParseResult<Ast<'i>> {
        match self.peek_or_eof()?.data {
            TokenData::KwLet => self.let_decl(),
            TokenData::KwIf => self.if_stmt(),
            TokenData::KwWhile => self.while_stmt(),
            TokenData::KwReturn => self.return_stmt(),
            TokenData::LBrace => self.block_stmt(),
            _ => self.expr_stmt(),
        }
    }

    #[inline]
    fn expr(&mut self) -> ParseResult<Ast<'i>> {
        self.assign_expr()
    }

    #[inline]
    fn block(&mut self) -> ParseResult<(Vec<Ast<'i>>, Span)> {
        let mut span = self.expect(TokenData::LBrace)?;

        let mut stmts = vec![];

        while !self.check_cur(TokenData::RBrace) {
            stmts.push(self.stmt()?);
        }

        span = span.join(&self.expect(TokenData::RBrace)?);

        Ok((stmts, span))
    }

    fn proc_decl(&mut self) -> ParseResult<Ast<'i>> {
        let mut span = self.advance().unwrap();

        let (name, _) = self.expect_ident()?;
        self.expect(TokenData::LParen)?;

        let mut params = vec![];

        if !self.check_cur(TokenData::RParen) {
            loop {
                let (param_name, _) = self.expect_ident()?;
                self.expect(TokenData::Colon)?;
                let (param_ty, _) = self.expect_type()?;

                params.push(Param {
                    name: param_name,
                    ty: param_ty,
                });

                if !self.match_cur(TokenData::Comma) {
                    break;
                }
            }
        }

        self.expect(TokenData::RParen)?;

        let ret = if self.check_cur(TokenData::LBrace) {
            Type::Unit
        } else {
            self.expect_type()?.0
        };

        self.cur_proc = Some(ret);

        self.begin_scope();
        params.iter().for_each(|param| {
            self.add_local(param.name, param.ty);
        });

        let (body, body_span) = self.block()?;

        self.end_scope();

        self.cur_proc = None;

        span = span.join(&body_span);

        let params_sig = params.iter().map(|param| param.ty).collect();

        let proc_sig = ProcSig {
            params: params_sig,
            ret,
        };

        if self.add_proc(name, proc_sig).is_some() {
            return Err(self.make_err(ParseErrorData::AlreadyDefinedProc(name.to_owned())));
        }

        Ok(Ast::new(
            AstData::ProcDecl {
                name,
                ret,
                params,
                body,
            },
            Type::Unit,
            span,
        ))
    }

    fn let_decl(&mut self) -> ParseResult<Ast<'i>> {
        let mut span = self.advance().unwrap();

        let is_mut = self.match_cur(TokenData::KwMut);

        let (name, _) = self.expect_ident()?;
        self.expect(TokenData::Colon)?;
        let (ty, _) = self.expect_type()?;

        let value = if self.match_cur(TokenData::Equal) {
            let value = self.expr()?;
            self.type_check_binop(BinOp::Assign, ty, value.ty)?;
            Some(Box::new(value))
        } else {
            None
        };

        span = span.join(&self.expect(TokenData::Semicolon)?);

        if self.add_local(name, ty).is_some() {
            return Err(self.make_err(ParseErrorData::AlreadyDefinedLocal(name.to_owned())));
        }

        Ok(Ast::new(
            AstData::LetDecl {
                name,
                ty,
                is_mut,
                value,
            },
            Type::Unit,
            span,
        ))
    }

    fn block_stmt(&mut self) -> ParseResult<Ast<'i>> {
        self.begin_scope();

        let (stmts, span) = self.block()?;

        self.end_scope();

        Ok(Ast::new(AstData::BlockStmt(stmts), Type::Unit, span))
    }

    fn if_stmt(&mut self) -> ParseResult<Ast<'i>> {
        let mut span = self.advance().unwrap();

        let cond = self.expr()?;

        if cond.ty != Type::Bool {
            return Err(self.make_err(ParseErrorData::TypeError(TypeError::Expected(
                Type::Bool,
                cond.ty,
            ))));
        }

        let then = self.block_stmt()?;

        let else_ = if self.match_cur(TokenData::KwElse) {
            if !self.check_cur(TokenData::KwIf) {
                let else_ = self.block_stmt()?;
                span = span.join(&else_.span);
                Some(Box::new(else_))
            } else {
                let else_if = self.if_stmt()?;
                span = span.join(&else_if.span);
                Some(Box::new(else_if))
            }
        } else {
            span = span.join(&then.span);
            None
        };

        Ok(Ast::new(
            AstData::IfStmt {
                cond: Box::new(cond),
                then: Box::new(then),
                else_,
            },
            Type::Unit,
            span,
        ))
    }

    fn while_stmt(&mut self) -> ParseResult<Ast<'i>> {
        let mut span = self.advance().unwrap();

        let cond = self.expr()?;
        if cond.ty != Type::Bool {
            return Err(self.make_err(ParseErrorData::TypeError(TypeError::Expected(
                Type::Bool,
                cond.ty,
            ))));
        }
        let body = self.block_stmt()?;

        span = span.join(&body.span);

        Ok(Ast::new(
            AstData::WhileStmt {
                cond: Box::new(cond),
                body: Box::new(body),
            },
            Type::Unit,
            span,
        ))
    }

    fn return_stmt(&mut self) -> ParseResult<Ast<'i>> {
        let Some(cur_ret) = self.cur_proc else {
            return Err(self.make_err(ParseErrorData::ReturnOutsideProc));
        };

        let mut span = self.advance().unwrap();

        let value = if !self.check_cur(TokenData::Semicolon) {
            let value = self.expr()?;
            if value.ty != cur_ret {
                return Err(self.make_err(ParseErrorData::TypeError(TypeError::Mismatch(
                    cur_ret, value.ty,
                ))));
            }
            Some(Box::new(value))
        } else {
            if cur_ret != Type::Unit {
                return Err(self.make_err(ParseErrorData::TypeError(TypeError::Mismatch(
                    Type::Unit,
                    cur_ret,
                ))));
            }
            None
        };

        span = span.join(&self.expect(TokenData::Semicolon)?);

        Ok(Ast::new(AstData::ReturnStmt(value), Type::Unit, span))
    }

    fn expr_stmt(&mut self) -> ParseResult<Ast<'i>> {
        let mut span = self.peek_or_eof()?.span;

        let expr = self.expr()?;

        span = span.join(&self.expect(TokenData::Semicolon)?);

        Ok(Ast::new(expr.data, Type::Unit, span))
    }

    fn assign_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.bool_or_expr()?;

        if self.match_cur(TokenData::Equal) {
            let rhs = self.assign_expr()?;
            let span = expr.span.join(&rhs.span);

            let ty = self.type_check_binop(BinOp::Assign, expr.ty, rhs.ty)?;

            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::Assign,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                ty,
                span,
            );
        }

        Ok(expr)
    }

    fn bool_or_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.bool_and_expr()?;

        while self.match_cur(TokenData::PipePipe) {
            let rhs = self.bool_and_expr()?;
            let span = expr.span.join(&rhs.span);

            let ty = self.type_check_binop(BinOp::BoolOr, expr.ty, rhs.ty)?;
            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BoolOr,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                ty,
                span,
            );
        }

        Ok(expr)
    }

    fn bool_and_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.bit_or_expr()?;

        while self.match_cur(TokenData::AmpAmp) {
            let rhs = self.bit_or_expr()?;
            let span = expr.span.join(&rhs.span);

            let ty = self.type_check_binop(BinOp::BoolAnd, expr.ty, rhs.ty)?;
            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BoolAnd,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                ty,
                span,
            );
        }

        Ok(expr)
    }

    fn bit_or_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.bit_xor_expr()?;

        while self.match_cur(TokenData::Pipe) {
            let rhs = self.bit_xor_expr()?;
            let span = expr.span.join(&rhs.span);

            let ty = self.type_check_binop(BinOp::BitOr, expr.ty, rhs.ty)?;
            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BitOr,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                ty,
                span,
            );
        }

        Ok(expr)
    }

    fn bit_xor_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.bit_and_expr()?;

        while self.match_cur(TokenData::Caret) {
            let rhs = self.bit_and_expr()?;
            let span = expr.span.join(&rhs.span);

            let ty = self.type_check_binop(BinOp::BitXor, expr.ty, rhs.ty)?;
            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BitXor,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                ty,
                span,
            );
        }

        Ok(expr)
    }

    fn bit_and_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.eq_expr()?;

        while self.match_cur(TokenData::Amp) {
            let rhs = self.eq_expr()?;
            let span = expr.span.join(&rhs.span);

            let ty = self.type_check_binop(BinOp::BitAnd, expr.ty, rhs.ty)?;
            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BitAnd,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                ty,
                span,
            );
        }

        Ok(expr)
    }

    fn eq_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.rel_expr()?;

        while let Some(op) = self.peek_binop() {
            match op {
                BinOp::Eq | BinOp::Neq => {
                    self.advance();
                    let rhs = self.rel_expr()?;
                    let span = expr.span.join(&rhs.span);

                    let ty = self.type_check_binop(op, expr.ty, rhs.ty)?;
                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        ty,
                        span,
                    );
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn rel_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.shift_expr()?;

        while let Some(op) = self.peek_binop() {
            match op {
                BinOp::Lt | BinOp::Leq | BinOp::Gt | BinOp::Geq | BinOp::BitShl | BinOp::BitShr => {
                    self.advance();
                    let rhs = self.shift_expr()?;
                    let span = expr.span.join(&rhs.span);

                    let ty = self.type_check_binop(op, expr.ty, rhs.ty)?;
                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        ty,
                        span,
                    );
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn shift_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.add_expr()?;

        while let Some(op) = self.peek_binop() {
            match op {
                BinOp::BitShl | BinOp::BitShr => {
                    self.advance();
                    let rhs = self.add_expr()?;
                    let span = expr.span.join(&rhs.span);

                    let ty = self.type_check_binop(op, expr.ty, rhs.ty)?;
                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        ty,
                        span,
                    );
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn add_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.mul_expr()?;

        while let Some(op) = self.peek_binop() {
            match op {
                BinOp::Add | BinOp::Sub => {
                    self.advance();
                    let rhs = self.mul_expr()?;
                    let span = expr.span.join(&rhs.span);

                    let ty = self.type_check_binop(op, expr.ty, rhs.ty)?;
                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        ty,
                        span,
                    );
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn mul_expr(&mut self) -> ParseResult<Ast<'i>> {
        let mut expr = self.un_expr()?;

        while let Some(op) = self.peek_binop() {
            match op {
                BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    self.advance();
                    let rhs = self.un_expr()?;
                    let span = expr.span.join(&rhs.span);

                    let ty = self.type_check_binop(op, expr.ty, rhs.ty)?;
                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        ty,
                        span,
                    );
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn un_expr(&mut self) -> ParseResult<Ast<'i>> {
        if let Some(op) = self.peek_unop() {
            let mut span = self.advance().unwrap();

            let expr = self.un_expr()?;
            span = span.join(&expr.span);

            let ty = self.type_check_unop(op, expr.ty)?;
            Ok(Ast::new(
                AstData::UnExpr {
                    op,
                    expr: Box::new(expr),
                },
                ty,
                span,
            ))
        } else {
            self.postfix_expr()
        }
    }

    fn postfix_expr(&mut self) -> ParseResult<Ast<'i>> {
        match self.peek_or_eof()?.data {
            TokenData::Ident(_) if self.peek_next().map(|t| t.data) == Some(TokenData::LParen) => {
                self.call_expr()
            }
            _ => self.primary_expr(),
        }
    }

    fn call_expr(&mut self) -> ParseResult<Ast<'i>> {
        let (name, mut span) = self.expect_ident()?;

        let mut args = vec![];

        self.expect(TokenData::LParen)?;

        if !self.check_cur(TokenData::RParen) {
            loop {
                args.push(self.expr()?);

                if !self.match_cur(TokenData::Comma) {
                    break;
                }
            }
        }

        span = span.join(&self.expect(TokenData::RParen)?);

        let sig = self
            .get_proc(name)
            .ok_or(self.make_err(ParseErrorData::UndefinedProc(name.to_owned())))?;

        if sig.params.len() != args.len() {
            return Err(self.make_err(ParseErrorData::WrongArgCount(sig.params.len(), args.len())));
        }
        for (param, arg) in sig.params.iter().zip(args.iter()) {
            if *param != arg.ty {
                return Err(self.make_err(ParseErrorData::TypeError(TypeError::Mismatch(
                    *param, arg.ty,
                ))));
            }
        }

        Ok(Ast::new(
            AstData::CallExpr { callee: name, args },
            sig.ret,
            span,
        ))
    }

    fn primary_expr(&mut self) -> ParseResult<Ast<'i>> {
        let Some(token) = self.next() else {
            return Err(self.make_err(ParseErrorData::ExpectedExpr));
        };

        let mut span = token.span;

        let (data, ty) = match token.data {
            TokenData::LParen => {
                if self.check_cur(TokenData::RParen) {
                    span = span.join(&self.advance().unwrap());
                    (AstData::UnitExpr, Type::Unit)
                } else {
                    let expr = self.expr()?;
                    span = span.join(&self.expect(TokenData::RParen)?);
                    (expr.data, expr.ty)
                }
            }
            TokenData::Ident(ident) => {
                let ty = self
                    .get_local(ident)
                    .ok_or(self.make_err(ParseErrorData::UndefinedLocal(ident.to_owned())))?;

                (AstData::IdentExpr(ident), *ty)
            }
            TokenData::Int(int) => (AstData::IntExpr(int), Type::Int),
            TokenData::Float(float) => (AstData::FloatExpr(float), Type::Float),
            TokenData::Char(char) => (AstData::CharExpr(char), Type::Char),
            TokenData::String(string) => (AstData::StringExpr(string), Type::String),
            TokenData::KwTrue => (AstData::BoolExpr(true), Type::Bool),
            TokenData::KwFalse => (AstData::BoolExpr(false), Type::Bool),
            _ => return Err(self.make_err(ParseErrorData::ExpectedExpr)),
        };

        Ok(Ast::new(data, ty, span))
    }

    pub fn parse(&mut self) -> ParseResult<Vec<Ast<'i>>> {
        let mut ast = vec![];

        while self.cursor < self.tokens.len() {
            ast.push(self.decl()?);
        }

        Ok(ast)
    }
}

impl<'p, 'i> Iterator for Parser<'p, 'i> {
    type Item = ParseResult<Ast<'i>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= self.tokens.len() {
            None
        } else {
            Some(self.decl())
        }
    }
}
