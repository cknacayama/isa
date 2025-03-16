use std::rc::Rc;

use crate::span::Span;

use super::{
    ast::{BinOp, Expr, ExprKind, TypedExpr, TypedExprKind, UnOp},
    env::{Env, TypeEnv},
    error::InferError,
    infer::{Constr, ConstrSet, InferResult, Subs, Substitute},
    types::{Fn, Type},
};

#[derive(Debug, Default)]
pub struct Checker<'a> {
    env:      Env<'a>,
    type_env: TypeEnv,
    cur_var:  u64,
}

impl<'a> Checker<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn type_env(&self) -> &TypeEnv {
        &self.type_env
    }

    pub fn type_env_mut(&mut self) -> &mut TypeEnv {
        &mut self.type_env
    }

    pub fn unify(&mut self, constr: ConstrSet) -> InferResult<'static, Vec<Subs>> {
        constr.unify(&mut self.type_env)
    }

    fn get_type(&mut self, ty: Type) -> Rc<Type> {
        self.type_env.get_type(ty)
    }

    fn new_type_variable(&mut self) -> Rc<Type> {
        let cur = self.cur_var;
        self.cur_var += 1;
        self.get_type(Type::Var(cur))
    }

    fn get_int(&self) -> Rc<Type> {
        self.type_env.get_int()
    }

    fn get_bool(&self) -> Rc<Type> {
        self.type_env.get_bool()
    }

    fn check_if(
        &mut self,
        cond: Expr<'a>,
        then: Expr<'a>,
        otherwise: Expr<'a>,
        span: Span,
    ) -> InferResult<'a, (TypedExpr<'a>, ConstrSet)> {
        let (cond, mut c1) = self.check(cond)?;
        let (then, c2) = self.check(then)?;
        let (otherwise, c3) = self.check(otherwise)?;
        let c_cond = Constr::new(cond.ty.clone(), self.get_bool());
        let var = self.new_type_variable();
        let c_then = Constr::new(var.clone(), then.ty.clone());
        let c_otherwise = Constr::new(var.clone(), then.ty.clone());

        c1.append(c2);
        c1.append(c3);
        c1.push(c_cond);
        c1.push(c_then);
        c1.push(c_otherwise);

        let kind = TypedExprKind::If {
            cond:      Box::new(cond),
            then:      Box::new(then),
            otherwise: Box::new(otherwise),
        };

        Ok((TypedExpr::new(kind, span, var), c1))
    }

    fn check_fn(
        &mut self,
        param: &'a str,
        expr: Expr<'a>,
        span: Span,
    ) -> InferResult<'a, (TypedExpr<'a>, ConstrSet)> {
        let var = self.new_type_variable();
        let old = self.env.insert(param, var);
        let (expr, c) = self.check(expr)?;
        let var = match old {
            Some(old) => self.env.insert(param, old).unwrap(),
            None => self.env.remove(param).unwrap(),
        };

        let ty = Type::Fn(Fn::new(var, expr.ty.clone()));
        let ty = self.get_type(ty);
        let kind = TypedExprKind::Fn {
            param,
            expr: Box::new(expr),
        };

        Ok((TypedExpr::new(kind, span, ty), c))
    }

    fn check_call(
        &mut self,
        callee: Expr<'a>,
        arg: Expr<'a>,
        span: Span,
    ) -> InferResult<'a, (TypedExpr<'a>, ConstrSet)> {
        let (callee, mut c1) = self.check(callee)?;
        let (arg, c2) = self.check(arg)?;
        let var = self.new_type_variable();
        let fn_ty = Type::Fn(Fn::new(arg.ty.clone(), var.clone()));
        let fn_ty = self.get_type(fn_ty);
        let constr = Constr::new(callee.ty.clone(), fn_ty);

        c1.append(c2);
        c1.push(constr);

        let kind = TypedExprKind::Call {
            callee: Box::new(callee),
            arg:    Box::new(arg),
        };

        Ok((TypedExpr::new(kind, span, var), c1))
    }

    fn check_let(
        &mut self,
        id: &'a str,
        expr: Expr<'a>,
        body: Expr<'a>,
        span: Span,
    ) -> InferResult<'a, (TypedExpr<'a>, ConstrSet)> {
        let (expr, mut c1) = self.check(expr)?;
        let s = self.unify(c1.clone())?;
        let u1 = expr
            .ty
            .clone()
            .substitute_many(s.iter(), &mut self.type_env);
        let mut env1 = self
            .env
            .clone()
            .substitute_many(s.iter(), &mut self.type_env);
        let u1 = env1.generalize(u1, &mut self.type_env);

        std::mem::swap(&mut self.env, &mut env1);
        self.env.insert(id, u1);
        let (body, c2) = self.check(body)?;
        std::mem::swap(&mut self.env, &mut env1);

        c1.append(c2);

        let ty = body.ty.clone();
        let kind = TypedExprKind::Let {
            id,
            expr: Box::new(expr),
            body: Box::new(body),
        };

        Ok((TypedExpr::new(kind, span, ty), c1))
    }

    fn instantiate(&mut self, ty: Rc<Type>) -> Rc<Type> {
        match ty.as_ref() {
            Type::Generic { quant, ty } => quant.iter().copied().fold(ty.clone(), |ty, quant| {
                let var = self.new_type_variable();
                let subs = Subs::new(quant, var);
                ty.substitute(&subs, &mut self.type_env)
            }),
            _ => ty,
        }
    }

    fn bin_op(&mut self, lhs: Rc<Type>, rhs: Rc<Type>, ret: Rc<Type>) -> Rc<Type> {
        let f2 = Type::Fn(Fn::new(rhs, ret));
        let f1 = Type::Fn(Fn::new(lhs, self.get_type(f2)));
        self.get_type(f1)
    }

    pub fn check(&mut self, expr: Expr<'a>) -> InferResult<'a, (TypedExpr<'a>, ConstrSet)> {
        let span = expr.span;
        match expr.kind {
            ExprKind::Int(i) => Ok((
                TypedExpr::new(TypedExprKind::Int(i), span, self.get_int()),
                ConstrSet::new(),
            )),
            ExprKind::Bool(b) => Ok((
                TypedExpr::new(TypedExprKind::Bool(b), span, self.get_bool()),
                ConstrSet::new(),
            )),
            ExprKind::Ident(id) => {
                let t = self.env.get(id).ok_or(InferError::Unbound(id))?.clone();
                Ok((
                    TypedExpr::new(TypedExprKind::Ident(id), span, self.instantiate(t)),
                    ConstrSet::new(),
                ))
            }
            ExprKind::BinOp(bin_op) => {
                let kind = TypedExprKind::BinOp(bin_op);
                let int = self.get_int();
                let bol = self.get_bool();
                match bin_op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Pow => {
                        Ok((
                            TypedExpr::new(kind, span, self.bin_op(int.clone(), int.clone(), int)),
                            ConstrSet::new(),
                        ))
                    }
                    BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Ge | BinOp::Lt | BinOp::Le => Ok((
                        TypedExpr::new(kind, span, self.bin_op(int.clone(), int, bol)),
                        ConstrSet::new(),
                    )),
                    BinOp::And | BinOp::Or => Ok((
                        TypedExpr::new(kind, span, self.bin_op(bol.clone(), bol.clone(), bol)),
                        ConstrSet::new(),
                    )),
                }
            }
            ExprKind::UnOp(un_op) => {
                let kind = TypedExprKind::UnOp(un_op);
                let ty = match un_op {
                    UnOp::Not => self.get_bool(),
                    UnOp::Neg => self.get_int(),
                };
                let ty = self.get_type(Type::Fn(Fn::new(ty.clone(), ty)));
                Ok((TypedExpr::new(kind, span, ty), ConstrSet::new()))
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => self.check_if(*cond, *then, *otherwise, span),
            ExprKind::Fn { param, expr } => self.check_fn(param, *expr, span),
            ExprKind::Call { callee, arg } => self.check_call(*callee, *arg, span),

            ExprKind::Let { id, expr, body } => self.check_let(id, *expr, *body, span),
        }
    }
}
