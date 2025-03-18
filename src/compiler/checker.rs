use std::rc::Rc;

use crate::span::Span;

use super::{
    ast::{BinOp, Constructor, Expr, ExprKind, TypedExpr, TypedExprKind, UnOp},
    env::{Env, TypeEnv},
    error::InferError,
    infer::{Constr, ConstrSet, InferResult, Subs, Substitute},
    types::Type,
};

#[derive(Debug, Default)]
pub struct Checker {
    env:      Env,
    type_env: TypeEnv,
    cur_var:  u64,
}

impl Checker {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn with_types(type_env: TypeEnv) -> Self {
        Self {
            env: Env::default(),
            type_env,
            cur_var: 0,
        }
    }

    #[must_use]
    pub fn env(&self) -> &Env {
        &self.env
    }

    #[must_use]
    pub fn type_env(&self) -> &TypeEnv {
        &self.type_env
    }

    pub fn type_env_mut(&mut self) -> &mut TypeEnv {
        &mut self.type_env
    }

    pub fn unify(&mut self, constr: ConstrSet) -> InferResult<Vec<Subs>> {
        constr.unify(&mut self.type_env)
    }

    fn get_type(&mut self, ty: Type) -> Rc<Type> {
        self.type_env.get_type(ty)
    }

    fn new_type_variable_id(&mut self) -> u64 {
        let cur = self.cur_var;
        self.cur_var += 1;
        cur
    }

    fn new_type_variable(&mut self) -> Rc<Type> {
        let id = self.new_type_variable_id();
        self.get_type(Type::Var(id))
    }

    fn get_int(&self) -> Rc<Type> {
        self.type_env.get_int()
    }

    fn get_unit(&self) -> Rc<Type> {
        self.type_env.get_unit()
    }

    fn get_bool(&self) -> Rc<Type> {
        self.type_env.get_bool()
    }

    fn check_if(
        &mut self,
        cond: Expr,
        then: Expr,
        otherwise: Expr,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        let (cond, mut c1) = self.check(cond)?;
        let (then, c2) = self.check(then)?;
        let (otherwise, c3) = self.check(otherwise)?;
        let c_cond = Constr::new(cond.ty.clone(), self.get_bool());
        let var = self.new_type_variable();
        let c_then = Constr::new(var.clone(), then.ty.clone());
        let c_otherwise = Constr::new(var.clone(), otherwise.ty.clone());

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
        param: Rc<str>,
        expr: Expr,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        let var = self.new_type_variable();
        let old = self.env.insert(param.clone(), var);
        let (expr, c) = self.check(expr)?;
        let var = match old {
            Some(old) => self.env.insert(param.clone(), old).unwrap(),
            None => self.env.remove(&param).unwrap(),
        };

        let ty = Type::Fn {
            param: var,
            ret:   expr.ty.clone(),
        };
        let ty = self.get_type(ty);
        let kind = TypedExprKind::Fn {
            param,
            expr: Box::new(expr),
        };

        Ok((TypedExpr::new(kind, span, ty), c))
    }

    fn check_call(
        &mut self,
        callee: Expr,
        arg: Expr,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        let (callee, mut c1) = self.check(callee)?;
        let (arg, c2) = self.check(arg)?;
        let var = self.new_type_variable();
        let fn_ty = Type::Fn {
            param: arg.ty.clone(),
            ret:   var.clone(),
        };
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
        rec: bool,
        id: Rc<str>,
        expr: Expr,
        body: Option<Expr>,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        let (expr, mut c1) = if rec {
            let var = self.new_type_variable();
            let old = self.env.insert(id.clone(), var);
            let (expr, mut c1) = self.check(expr)?;
            let var = match old {
                Some(old) => self.env.insert(id.clone(), old).unwrap(),
                None => self.env.remove(&id).unwrap(),
            };
            let constr = Constr::new(expr.ty.clone(), var);
            c1.push(constr);
            (expr, c1)
        } else {
            self.check(expr)?
        };

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
        self.env.insert(id.clone(), u1);

        let (body, ty) = match body {
            Some(body) => {
                let (body, c2) = self.check(body)?;
                std::mem::swap(&mut self.env, &mut env1);
                c1.append(c2);
                let ty = body.ty.clone();
                (Some(body), ty)
            }
            _ => (None, self.get_unit()),
        };

        let kind = TypedExprKind::Let {
            rec: false,
            id,
            expr: Box::new(expr),
            body: body.map(Box::new),
        };

        Ok((TypedExpr::new(kind, span, ty), c1))
    }

    fn check_constructor(
        &mut self,
        constructor: &Constructor,
        parameters: &[Rc<str>],
        parameters_id: &[Rc<Type>],
        quant: Box<[u64]>,
        mut ret: Rc<Type>,
    ) {
        for param in constructor
            .params
            .iter()
            .rev()
            .map(|param| match param.as_ref() {
                Type::Named { name, args } if args.is_empty() => {
                    if let Some(pos) = parameters.iter().position(|p| p == name) {
                        parameters_id[pos].clone()
                    } else {
                        param.clone()
                    }
                }
                _ => param.clone(),
            })
        {
            ret = self.get_type(Type::Fn { param, ret });
        }
        if !quant.is_empty() {
            ret = self.get_type(Type::Generic { quant, ty: ret });
        }
        self.env.insert(constructor.id.clone(), ret);
    }

    fn check_type(
        &mut self,
        name: Rc<str>,
        parameters: Box<[Rc<str>]>,
        constructors: Box<[Constructor]>,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        let mut args = Vec::new();
        let mut quant = Vec::new();

        for _ in parameters.iter() {
            let id = self.new_type_variable_id();
            args.push(self.get_type(Type::Var(id)));
            quant.push(id);
        }

        let quant = quant.into_boxed_slice();

        let ty = self.get_type(Type::Named {
            name: name.clone(),
            args: args.clone().into_boxed_slice(),
        });

        for c in constructors.iter() {
            self.check_constructor(c, &parameters, &args, quant.clone(), ty.clone());
        }

        let kind = TypedExprKind::Type {
            id: name,
            parameters,
            constructors,
        };
        let expr = TypedExpr::new(kind, span, self.get_unit());

        Ok((expr, ConstrSet::new()))
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
        let f2 = Type::Fn { param: lhs, ret };
        let f1 = Type::Fn {
            param: rhs,
            ret:   self.get_type(f2),
        };
        self.get_type(f1)
    }

    pub fn check_many<I>(&mut self, expr: I) -> InferResult<(Vec<TypedExpr>, ConstrSet)>
    where
        I: IntoIterator<Item = Expr>,
    {
        let mut exprs = Vec::new();
        let mut cset = ConstrSet::new();

        for expr in expr {
            let (expr, c) = self.check(expr)?;
            exprs.push(expr);
            cset.append(c);
        }

        Ok((exprs, cset))
    }

    pub fn check(&mut self, expr: Expr) -> InferResult<(TypedExpr, ConstrSet)> {
        let span = expr.span;
        match expr.kind {
            ExprKind::Unit => Ok((
                TypedExpr::new(TypedExprKind::Unit, span, self.get_unit()),
                ConstrSet::new(),
            )),
            ExprKind::Int(i) => Ok((
                TypedExpr::new(TypedExprKind::Int(i), span, self.get_int()),
                ConstrSet::new(),
            )),
            ExprKind::Bool(b) => Ok((
                TypedExpr::new(TypedExprKind::Bool(b), span, self.get_bool()),
                ConstrSet::new(),
            )),
            ExprKind::Ident(id) => {
                let t = self
                    .env
                    .get(&id)
                    .ok_or_else(|| InferError::Unbound(id.clone()))?
                    .clone();
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
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => Ok((
                        TypedExpr::new(kind, span, self.bin_op(int.clone(), int.clone(), int)),
                        ConstrSet::new(),
                    )),
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
                let ty = self.get_type(Type::Fn {
                    param: ty.clone(),
                    ret:   ty,
                });
                Ok((TypedExpr::new(kind, span, ty), ConstrSet::new()))
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => self.check_if(*cond, *then, *otherwise, span),
            ExprKind::Fn { param, expr } => self.check_fn(param, *expr, span),
            ExprKind::Call { callee, arg } => self.check_call(*callee, *arg, span),
            ExprKind::Let {
                rec,
                id,
                expr,
                body,
            } => self.check_let(rec, id, *expr, body.map(|body| *body), span),
            ExprKind::Semi(expr) => {
                let (mut expr, cset) = self.check(*expr)?;
                expr.ty = self.get_unit();
                Ok((expr, cset))
            }
            ExprKind::Type {
                id,
                parameters,
                constructors,
            } => self.check_type(id, parameters, constructors, span),
        }
    }
}
