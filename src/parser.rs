use std::{collections::HashSet, rc::Rc};

use crate::{
    ast::*,
    error::{ParseError, ParseErrorData, ParseResult},
    span::*,
    token::{Token, TokenData},
    types::*,
};

#[derive(Debug)]
pub struct Parser<'p, 'i> {
    tokens: &'p [Token<'i>],
    cursor: usize,
    proc_sigs: HashSet<Rc<ProcSig>>,
}

impl<'p, 'i> Parser<'p, 'i> {
    pub fn new(tokens: &'p [Token<'i>]) -> Self {
        Self {
            tokens,
            cursor: 0,
            proc_sigs: HashSet::new(),
        }
    }

    #[inline]
    fn add_proc_sig(&mut self, sig: Rc<ProcSig>) -> bool {
        self.proc_sigs.insert(sig)
    }

    #[inline]
    fn get_proc_sig(&self, sig: &ProcSig) -> Option<&Rc<ProcSig>> {
        self.proc_sigs.get(sig)
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
            TokenData::KwProc => self.proc_decl(),
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

        let mut params = vec![];
        let mut param_types = vec![];

        self.expect(TokenData::LParen)?;

        if !self.check_cur(TokenData::RParen) {
            loop {
                let (param_name, _) = self.expect_ident()?;
                self.expect(TokenData::Colon)?;
                let (param_ty, _) = self.expect_type()?;

                params.push(param_name);
                param_types.push(param_ty);

                if !self.match_cur(TokenData::Comma) {
                    break;
                }
            }
        }

        span = span.join(&self.expect(TokenData::RParen)?);

        let ret_ty = if !self.check_cur(TokenData::LBrace) {
            self.expect_type()?.0
        } else {
            Type::Unit
        };

        let sig = ProcSig {
            params: param_types,
            ret: ret_ty,
        };

        let sig = if let Some(sig) = self.get_proc_sig(&sig) {
            sig.clone()
        } else {
            let sig = Rc::new(sig);
            self.add_proc_sig(sig.clone());
            sig
        };

        let (body, body_span) = self.block()?;

        span = span.join(&body_span);

        Ok(Ast::new(
            AstData::ProcDecl {
                sig,
                name,
                params,
                body,
            },
            Type::Unit,
            span,
        ))
    }

    fn let_decl(&mut self) -> ParseResult<Ast<'i>> {
        let mut span = self.advance().unwrap();

        let (name, _) = self.expect_ident()?;
        let (ty, _) = if self.match_cur(TokenData::Colon) {
            self.expect_type()?
        } else {
            (Type::Unknown, Span::default())
        };

        let value = if self.match_cur(TokenData::Equal) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        span = span.join(&self.expect(TokenData::Semicolon)?);

        Ok(Ast::new(
            AstData::LetDecl { name, ty, value },
            Type::Unit,
            span,
        ))
    }

    fn block_stmt(&mut self) -> ParseResult<Ast<'i>> {
        let (stmts, span) = self.block()?;

        Ok(Ast::new(AstData::BlockStmt(stmts), Type::Unit, span))
    }

    fn if_stmt(&mut self) -> ParseResult<Ast<'i>> {
        let mut span = self.advance().unwrap();

        let cond = self.expr()?;

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
        let mut span = self.advance().unwrap();

        let mut value = if !self.check_cur(TokenData::Semicolon) {
            self.expr()?
        } else {
            Ast::new(AstData::UnitExpr, Type::Unit, Span::default())
        };

        let semicolon = self.expect(TokenData::Semicolon)?;
        if value.ty == Type::Unit {
            value.span = semicolon;
        }
        span = span.join(&semicolon);

        Ok(Ast::new(
            AstData::ReturnStmt(Box::new(value)),
            Type::Unit,
            span,
        ))
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

            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::Assign,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                Type::Unknown,
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

            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BoolOr,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                Type::Unknown,
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

            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BoolAnd,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                Type::Unknown,
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

            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BitOr,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                Type::Unknown,
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

            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BitXor,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                Type::Unknown,
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

            expr = Ast::new(
                AstData::BinExpr {
                    op: BinOp::BitAnd,
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                },
                Type::Unknown,
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

                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        Type::Unknown,
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

                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        Type::Unknown,
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

                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        Type::Unknown,
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

                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        Type::Unknown,
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

                    expr = Ast::new(
                        AstData::BinExpr {
                            op,
                            lhs: Box::new(expr),
                            rhs: Box::new(rhs),
                        },
                        Type::Unknown,
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

            Ok(Ast::new(
                AstData::UnExpr {
                    op,
                    expr: Box::new(expr),
                },
                Type::Unknown,
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
        let (callee, mut span) = self.expect_ident()?;

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

        Ok(Ast::new(
            AstData::CallExpr { callee, args },
            Type::Unknown,
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
            TokenData::Ident(ident) => (AstData::IdentExpr(ident), Type::Unknown),
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
