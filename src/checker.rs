use std::rc::Rc;

use crate::{
    ast::*,
    ctx::Ctx,
    error::{CheckError, CheckErrorData, CheckResult, TypeError},
    span::Span,
    types::*,
};

#[derive(Debug)]
pub struct Checker<'a> {
    ctx_stack: Vec<Ctx<'a>>,
    ret_stack: Vec<Type>,
}

impl<'i> Checker<'i> {
    pub fn new() -> Self {
        Self {
            ctx_stack: vec![Ctx::new()],
            ret_stack: vec![],
        }
    }

    fn add_local(&mut self, name: &'i str, ty: Type) -> Option<Type> {
        self.ctx_stack.last_mut().unwrap().add_local(name, ty)
    }

    fn add_proc(&mut self, name: &'i str, sig: Rc<ProcSig>) -> Option<Rc<ProcSig>> {
        self.ctx_stack.last_mut().unwrap().add_proc(name, sig)
    }

    fn get_local(&self, name: &'i str) -> Option<&Type> {
        self.ctx_stack
            .iter()
            .rev()
            .find_map(|ctx| ctx.get_local(name))
    }

    fn get_proc(&self, name: &'i str) -> Option<&Rc<ProcSig>> {
        self.ctx_stack
            .iter()
            .rev()
            .find_map(|ctx| ctx.get_proc(name))
    }

    fn begin_scope(&mut self) {
        self.ctx_stack.push(Ctx::new());
    }

    fn end_scope(&mut self) {
        self.ctx_stack.pop();
    }

    fn begin_proc_scope(&mut self, ret_ty: Type) {
        self.ctx_stack.push(Ctx::new());
        self.ret_stack.push(ret_ty);
    }

    fn end_proc_scope(&mut self) {
        self.ctx_stack.pop();
        self.ret_stack.pop();
    }

    fn binary_expr(
        &mut self,
        op: BinOp,
        lhs: Ast<'i>,
        rhs: Ast<'i>,
        span: Span,
    ) -> CheckResult<Ast<'i>> {
        let lhs = self.ast(lhs)?;
        let rhs = self.ast(rhs)?;

        let ty = op
            .type_of(lhs.ty.clone(), rhs.ty.clone())
            .map_err(|err| err.into_check_error(span))?;

        Ok(Ast {
            data: AstData::BinExpr {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            ty,
            span,
        })
    }

    fn unary_expr(&mut self, op: UnOp, expr: Ast<'i>, span: Span) -> CheckResult<Ast<'i>> {
        let expr = self.ast(expr)?;

        let ty = op
            .type_of(expr.ty.clone())
            .map_err(|err| err.into_check_error(span))?;

        Ok(Ast {
            data: AstData::UnExpr {
                op,
                expr: Box::new(expr),
            },
            ty,
            span,
        })
    }

    fn call_expr(
        &mut self,
        callee: &'i str,
        args: Vec<Ast<'i>>,
        span: Span,
    ) -> CheckResult<Ast<'i>> {
        let callee_sig = self
            .get_proc(callee)
            .ok_or(CheckError::new(
                CheckErrorData::UndefinedSymbol(callee.to_string()),
                span,
            ))?
            .clone();

        if callee_sig.params.len() != args.len() {
            return Err(CheckError::new(
                CheckErrorData::TypeError(TypeError::WrongArgCount(
                    callee_sig.params.len(),
                    args.len(),
                )),
                span,
            ));
        }

        let args = args
            .into_iter()
            .map(|arg| self.ast(arg))
            .collect::<CheckResult<Vec<_>>>()?;

        for (arg, param) in args.iter().zip(callee_sig.params.iter()) {
            if arg.ty != *param {
                return Err(CheckError::new(
                    CheckErrorData::TypeError(TypeError::Mismatch(arg.ty.clone(), param.clone())),
                    span,
                ));
            }
        }

        Ok(Ast {
            data: AstData::CallExpr { callee, args },
            ty: callee_sig.ret.clone(),
            span,
        })
    }

    fn ident_expr(&mut self, ident: &'i str, span: Span) -> CheckResult<Ast<'i>> {
        let Some(ty) = ({
            if let Some(ty) = self.get_local(ident) {
                Some(ty.clone())
            } else if let Some(ty) = self.get_proc(ident) {
                Some(Type::Proc(ty.clone()))
            } else {
                None
            }
        }) else {
            return Err(CheckError::new(
                CheckErrorData::UndefinedSymbol(ident.to_string()),
                span,
            ));
        };

        Ok(Ast {
            data: AstData::IdentExpr(ident),
            ty,
            span,
        })
    }

    fn ret_stmt(&mut self, expr: Ast<'i>, span: Span) -> CheckResult<Ast<'i>> {
        let expr = self.ast(expr)?;

        let ret_ty = self.ret_stack.last().unwrap();

        if expr.ty != *ret_ty {
            return Err(CheckError::new(
                CheckErrorData::TypeError(TypeError::Mismatch(expr.ty, ret_ty.clone())),
                span,
            ));
        }

        Ok(Ast {
            data: AstData::ReturnStmt(Box::new(expr)),
            ty: Type::Unit,
            span,
        })
    }

    fn proc_decl(
        &mut self,
        sig: Rc<ProcSig>,
        name: &'i str,
        params: Vec<&'i str>,
        body: Vec<Ast<'i>>,
        span: Span,
    ) -> CheckResult<Ast<'i>> {
        if self.add_proc(name, sig.clone()).is_some() {
            return Err(CheckError::new(
                CheckErrorData::AlreadyDefinedProc(name.to_string()),
                span,
            ));
        }

        self.begin_proc_scope(sig.ret.clone());

        for (param, ty) in params.iter().zip(sig.params.iter()) {
            self.add_local(param, ty.clone());
        }

        let body = body
            .into_iter()
            .map(|expr| self.ast(expr))
            .collect::<CheckResult<Vec<_>>>()?;

        self.end_proc_scope();

        Ok(Ast {
            data: AstData::ProcDecl {
                sig,
                name,
                params,
                body,
            },
            ty: Type::Unit,
            span,
        })
    }

    fn let_decl(
        &mut self,
        name: &'i str,
        ty: Type,
        value: Option<Box<Ast<'i>>>,
        span: Span,
    ) -> CheckResult<Ast<'i>> {
        let (value, ty) = if let Some(value) = value {
            let value = self.ast(*value)?;

            if ty != Type::Unknown && value.ty != ty {
                return Err(CheckError::new(
                    CheckErrorData::TypeError(TypeError::Mismatch(value.ty, ty)),
                    span,
                ));
            }

            let ty = value.ty.clone();

            (Some(Box::new(value)), ty)
        } else {
            (None, ty)
        };

        if ty == Type::Unknown {
            return Err(CheckError::new(
                CheckErrorData::TypeError(TypeError::UnknownType),
                span,
            ));
        }

        if self.add_local(name, ty.clone()).is_some() {
            return Err(CheckError::new(
                CheckErrorData::AlreadyDefinedLocal(name.to_string()),
                span,
            ));
        }

        Ok(Ast {
            data: AstData::LetDecl { name, ty, value },
            ty: Type::Unit,
            span,
        })
    }

    fn if_stmt(
        &mut self,
        cond: Ast<'i>,
        then: Ast<'i>,
        else_: Option<Box<Ast<'i>>>,
        span: Span,
    ) -> CheckResult<Ast<'i>> {
        let cond = self.ast(cond)?;

        if cond.ty != Type::Bool {
            return Err(CheckError::new(
                CheckErrorData::TypeError(TypeError::Expected(Type::Bool, cond.ty)),
                span,
            ));
        }

        let then = self.ast(then)?;

        let else_ = if let Some(else_) = else_ {
            Some(Box::new(self.ast(*else_)?))
        } else {
            None
        };

        Ok(Ast {
            data: AstData::IfStmt {
                cond: Box::new(cond),
                then: Box::new(then),
                else_,
            },
            ty: Type::Unit,
            span,
        })
    }

    fn while_stmt(&mut self, cond: Ast<'i>, body: Ast<'i>, span: Span) -> CheckResult<Ast<'i>> {
        let cond = self.ast(cond)?;

        if cond.ty != Type::Bool {
            return Err(CheckError::new(
                CheckErrorData::TypeError(TypeError::Expected(Type::Bool, cond.ty)),
                span,
            ));
        }

        let body = self.ast(body)?;

        Ok(Ast {
            data: AstData::WhileStmt {
                cond: Box::new(cond),
                body: Box::new(body),
            },
            ty: Type::Unit,
            span,
        })
    }

    fn block_stmt(&mut self, stmts: Vec<Ast<'i>>, span: Span) -> CheckResult<Ast<'i>> {
        self.begin_scope();

        let stmts = stmts
            .into_iter()
            .map(|stmt| self.ast(stmt))
            .collect::<CheckResult<Vec<_>>>()?;

        self.end_scope();

        Ok(Ast {
            data: AstData::BlockStmt(stmts),
            ty: Type::Unit,
            span,
        })
    }

    pub fn ast(&mut self, expr: Ast<'i>) -> CheckResult<Ast<'i>> {
        use AstData::*;

        let span = expr.span;

        match expr.data {
            BinExpr { op, lhs, rhs } => self.binary_expr(op, *lhs, *rhs, span),
            UnExpr { op, expr } => self.unary_expr(op, *expr, span),
            CallExpr { callee, args } => self.call_expr(callee, args, span),

            UnitExpr => Ok(Ast {
                data: AstData::UnitExpr,
                ty: Type::Unit,
                span,
            }),

            IntExpr(int) => Ok(Ast {
                data: AstData::IntExpr(int),
                ty: Type::Int,
                span,
            }),

            FloatExpr(float) => Ok(Ast {
                data: AstData::FloatExpr(float),
                ty: Type::Float,
                span,
            }),

            BoolExpr(boolean) => Ok(Ast {
                data: AstData::BoolExpr(boolean),
                ty: Type::Bool,
                span,
            }),

            CharExpr(character) => Ok(Ast {
                data: AstData::CharExpr(character),
                ty: Type::Char,
                span,
            }),

            StringExpr(string) => Ok(Ast {
                data: AstData::StringExpr(string),
                ty: Type::String,
                span,
            }),

            IdentExpr(ident) => self.ident_expr(ident, span),

            ReturnStmt(expr) => self.ret_stmt(*expr, span),

            ProcDecl {
                sig,
                name,
                params,
                body,
            } => self.proc_decl(sig, name, params, body, span),

            LetDecl { name, ty, value } => self.let_decl(name, ty, value, span),

            IfStmt { cond, then, else_ } => self.if_stmt(*cond, *then, else_, span),

            WhileStmt { cond, body } => self.while_stmt(*cond, *body, span),

            BlockStmt(stmts) => self.block_stmt(stmts, span),
        }
    }

    pub fn check(&mut self, program: Vec<Ast<'i>>) -> CheckResult<Vec<Ast<'i>>> {
        let program = program
            .into_iter()
            .map(|expr| self.ast(expr))
            .collect::<CheckResult<Vec<_>>>()?;

        Ok(program)
    }
}
