use std::rc::Rc;

use super::ast::typed::{
    TypedExpr, TypedExprKind, TypedMatchArm, TypedModule, TypedParam, TypedPat, TypedPatKind,
};
use super::ast::untyped::{
    UntypedExpr, UntypedExprKind, UntypedMatchArm, UntypedModule, UntypedParam, UntypedPat,
    UntypedPatKind,
};
use super::ast::{BinOp, Constructor, ModuleIdent, PathIdent, UnOp};
use super::ctx::TypeCtx;
use super::env::{Env, VarData};
use super::error::{InferError, InferErrorKind};
use super::infer::{Constraint, ConstraintSet, InferResult, Subs, Substitute, unify};
use super::types::Ty;
use crate::global::Symbol;
use crate::span::Span;

#[derive(Debug, Default)]
pub struct Checker {
    env:            Env,
    type_ctx:       TypeCtx,
    cur_module:     Option<Symbol>,
    declared_types: Vec<Symbol>,
}

impl Checker {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn with_types(type_env: TypeCtx) -> Self {
        Self {
            env:            Env::default(),
            type_ctx:       type_env,
            cur_module:     None,
            declared_types: Vec::new(),
        }
    }

    fn unify<C>(&mut self, constr: C) -> InferResult<Vec<Subs>>
    where
        ConstraintSet: From<C>,
    {
        unify(constr, &mut self.type_ctx).inspect(|subs| {
            self.env.substitute_many(subs, &mut self.type_ctx);
        })
    }

    #[must_use]
    pub fn type_ctx(&self) -> &TypeCtx {
        &self.type_ctx
    }

    fn insert_variable(&mut self, id: Symbol, ty: Rc<Ty>) -> Option<VarData> {
        self.env.insert(id, ty)
    }

    fn get_variable(&self, id: Symbol) -> Option<Rc<Ty>> {
        self.env.get(&id).map(VarData::ty).cloned()
    }

    fn insert_constructor(&mut self, name: Symbol, ty: Rc<Ty>) -> Option<VarData> {
        self.env.insert_constructor(name, ty)
    }

    fn get_constructor(&self, name: Symbol) -> Option<Rc<Ty>> {
        self.env.get_constructor(&name)
    }

    fn intern_type(&mut self, ty: Ty) -> Rc<Ty> {
        self.type_ctx.intern_type(ty)
    }

    const fn gen_id(&mut self) -> u64 {
        self.type_ctx.gen_id()
    }

    fn gen_type_var(&mut self) -> Rc<Ty> {
        self.type_ctx.gen_type_var()
    }

    fn get_int(&self) -> Rc<Ty> {
        self.type_ctx.get_int()
    }

    fn get_unit(&self) -> Rc<Ty> {
        self.type_ctx.get_unit()
    }

    fn get_bool(&self) -> Rc<Ty> {
        self.type_ctx.get_bool()
    }

    fn check_if(
        &mut self,
        cond: UntypedExpr,
        then: UntypedExpr,
        otherwise: UntypedExpr,
        span: Span,
    ) -> InferResult<TypedExpr> {
        let mut cond = self.check(cond)?;
        let mut then = self.check(then)?;
        let mut otherwise = self.check(otherwise)?;

        let var = self.gen_type_var();

        let c_cond = Constraint::new(self.get_bool(), cond.ty.clone(), [cond.span, span]);
        let c_then = Constraint::new(var.clone(), then.ty.clone(), [then.span, span]);
        let c_otherwise =
            Constraint::new(var.clone(), otherwise.ty.clone(), [otherwise.span, span]);

        let subs = self.unify([c_cond, c_then, c_otherwise])?;

        cond.substitute_many(&subs, &mut self.type_ctx);
        then.substitute_many(&subs, &mut self.type_ctx);
        otherwise.substitute_many(&subs, &mut self.type_ctx);
        let var = var.substitute_many(&subs, &mut self.type_ctx);

        let kind = TypedExprKind::If {
            cond:      Box::new(cond),
            then:      Box::new(then),
            otherwise: Box::new(otherwise),
        };

        Ok(TypedExpr::new(kind, span, var))
    }

    fn check_fn(
        &mut self,
        param: UntypedParam,
        expr: UntypedExpr,
        span: Span,
    ) -> InferResult<TypedExpr> {
        self.env.push_scope();

        let var = self.gen_type_var();
        self.insert_variable(param.name, var);

        let expr = self.check(expr)?;
        let var = self
            .get_variable(param.name)
            .unwrap_or_else(|| unreachable!());

        self.env.pop_scope();

        let ty = self.intern_type(Ty::Fn {
            param: var.clone(),
            ret:   expr.ty.clone(),
        });

        let kind = TypedExprKind::Fn {
            param: TypedParam::new(param.name, var, param.span),
            expr:  Box::new(expr),
        };

        Ok(TypedExpr::new(kind, span, ty))
    }

    fn check_call(
        &mut self,
        callee: UntypedExpr,
        arg: UntypedExpr,
        span: Span,
    ) -> InferResult<TypedExpr> {
        let mut callee = self.check(callee)?;
        let mut arg = self.check(arg)?;

        let var = self.gen_type_var();
        let fn_ty = self.intern_type(Ty::Fn {
            param: arg.ty.clone(),
            ret:   var.clone(),
        });
        let subs = self.unify(Constraint::new(
            callee.ty.clone(),
            fn_ty,
            [callee.span, arg.span, span],
        ))?;

        callee.substitute_many(&subs, &mut self.type_ctx);
        arg.substitute_many(&subs, &mut self.type_ctx);

        let var = var.substitute_many(&subs, &mut self.type_ctx);

        let kind = TypedExprKind::Call {
            callee: Box::new(callee),
            arg:    Box::new(arg),
        };

        Ok(TypedExpr::new(kind, span, var))
    }

    fn function_type<I>(&mut self, params: I, ret: Rc<Ty>) -> Rc<Ty>
    where
        I: IntoIterator<Item = Rc<Ty>>,
        I::IntoIter: DoubleEndedIterator,
    {
        params
            .into_iter()
            .rev()
            .fold(ret, |ret, param| self.intern_type(Ty::Fn { param, ret }))
    }

    fn check_let_value(
        &mut self,
        id: Symbol,
        params: Box<[UntypedParam]>,
        expr: UntypedExpr,
    ) -> InferResult<(TypedExpr, Box<[TypedParam]>)> {
        self.env.push_scope();

        let mut typed_params = params
            .into_iter()
            .map(|p| {
                let var = self.gen_type_var();
                self.insert_variable(p.name, var.clone());
                TypedParam::new(p.name, var, p.span)
            })
            .collect::<Box<_>>();

        let expr = if typed_params.is_empty() {
            self.check(expr)?
        } else {
            let var_id = self.gen_id();
            let var = self.intern_type(Ty::Var(var_id));
            self.insert_variable(id, var);

            let mut expr = self.check(expr)?;

            for p in &mut typed_params {
                p.ty = self.get_variable(p.name).unwrap_or_else(|| unreachable!());
            }

            expr.ty = self.function_type(typed_params.iter().map(TypedParam::ty).cloned(), expr.ty);

            let subs = Subs::new(var_id, expr.ty.clone());

            expr.substitute_eq(&subs, &mut self.type_ctx);
            expr
        };

        self.env.pop_scope();
        Ok((expr, typed_params))
    }

    fn check_let(
        &mut self,
        id: Symbol,
        params: Box<[UntypedParam]>,
        expr: UntypedExpr,
        body: Option<UntypedExpr>,
        span: Span,
    ) -> InferResult<TypedExpr> {
        let (expr, params) = self.check_let_value(id, params, expr)?;

        let u1 = self.env.generalize(expr.ty.clone(), &mut self.type_ctx);
        let mut env1 = self.env.clone();
        std::mem::swap(&mut self.env, &mut env1);
        self.insert_variable(id, u1);

        let (body, ty) = match body {
            Some(body) => {
                let body = self.check(body)?;
                std::mem::swap(&mut self.env, &mut env1);
                let ty = body.ty.clone();
                (Some(body), ty)
            }
            None => (None, self.get_unit()),
        };

        let kind = TypedExprKind::Let {
            id,
            params,
            expr: Box::new(expr),
            body: body.map(Box::new),
        };

        Ok(TypedExpr::new(kind, span, ty))
    }

    fn check_constructor(
        &mut self,
        constructor: &mut Constructor,
        subs: &[(Rc<Ty>, Rc<Ty>)],
        quant: Rc<[u64]>,
        mut ret: Rc<Ty>,
    ) {
        for param in constructor.params.iter_mut().rev() {
            *param = param.clone().substitute(
                &mut |ty, _| {
                    subs.iter().find_map(|(old, new)| {
                        let old = Rc::as_ptr(old);
                        if std::ptr::eq(ty, old) {
                            Some(new.clone())
                        } else {
                            None
                        }
                    })
                },
                &mut self.type_ctx,
            );
            ret = self.intern_type(Ty::Fn {
                param: param.clone(),
                ret,
            });
        }
        if !quant.is_empty() {
            ret = self.intern_type(Ty::Scheme { quant, ty: ret });
        }
        self.insert_variable(constructor.name, ret.clone());
        self.insert_constructor(constructor.name, ret);
    }

    fn check_type(
        &mut self,
        name: Symbol,
        parameters: Box<[Rc<Ty>]>,
        mut constructors: Box<[Constructor]>,
        span: Span,
    ) -> TypedExpr {
        let mut args = Vec::new();
        let mut subs = Vec::new();
        let mut quant = Vec::new();

        for param in parameters {
            let id = self.gen_id();
            let new = self.intern_type(Ty::Var(id));
            subs.push((param, new.clone()));
            args.push(new);
            quant.push(id);
        }

        let quant = Rc::<[u64]>::from(quant);

        self.declared_types.push(name);

        let ty = self.intern_type(Ty::Named {
            name: PathIdent::Ident(name),
            args: args.clone().into(),
        });

        let ty_with_module = self.cur_module.map_or_else(
            || ty.clone(),
            |module| {
                self.intern_type(Ty::Named {
                    name: PathIdent::Module(ModuleIdent::new(module, name)),
                    args: args.clone().into(),
                })
            },
        );

        for c in &mut constructors {
            self.check_constructor(c, &subs, quant.clone(), ty.clone());
            self.type_ctx.insert_constructor(&ty_with_module, c.clone());
        }

        let kind = TypedExprKind::Type {
            id: name,
            parameters: args.into_boxed_slice(),
            constructors,
        };

        TypedExpr::new(kind, span, self.get_unit())
    }

    fn check_pat(&mut self, UntypedPat { kind, span, .. }: UntypedPat) -> InferResult<TypedPat> {
        match kind {
            UntypedPatKind::Wild => {
                let var = self.gen_type_var();
                Ok(TypedPat::new(TypedPatKind::Wild, span, var))
            }
            UntypedPatKind::Or(spanneds) => {
                let mut patterns = Vec::new();
                let mut c = ConstraintSet::new();

                let var = self.gen_type_var();
                for pat in spanneds {
                    let pat = self.check_pat(pat)?;
                    c.push(Constraint::new(
                        pat.ty.clone(),
                        var.clone(),
                        [pat.span, span],
                    ));
                    patterns.push(pat);
                }

                let subs = self.unify(c)?;

                for p in &mut patterns {
                    p.substitute_many(&subs, &mut self.type_ctx);
                }
                let var = var.substitute_many(&subs, &mut self.type_ctx);

                Ok(TypedPat::new(
                    TypedPatKind::Or(patterns.into_boxed_slice()),
                    span,
                    var,
                ))
            }
            UntypedPatKind::Unit => Ok(TypedPat::new(TypedPatKind::Unit, span, self.get_unit())),
            UntypedPatKind::Int(i) => Ok(TypedPat::new(TypedPatKind::Int(i), span, self.get_int())),
            UntypedPatKind::Bool(b) => {
                Ok(TypedPat::new(TypedPatKind::Bool(b), span, self.get_bool()))
            }
            UntypedPatKind::Constructor { name, args } => {
                let ty = match name {
                    PathIdent::Module(module) => self
                        .env
                        .get_constructor_from_module(&module)
                        .map_err(|err| InferError::new(err, span))?,

                    PathIdent::Ident(name) => match self.get_constructor(name) {
                        Some(ty) => ty,
                        None if args.is_empty() => {
                            let var = self.gen_type_var();
                            self.insert_variable(name, var.clone());
                            return Ok(TypedPat::new(TypedPatKind::Ident(name), span, var));
                        }
                        None => return Err(InferError::new(InferErrorKind::Unbound(name), span)),
                    },
                };

                let mut ty = self.instantiate(ty);

                let mut c = ConstraintSet::new();
                let mut typed_args = Vec::new();

                for arg in args {
                    let arg = self.check_pat(arg)?;
                    let Ty::Fn { param, ret } = ty.as_ref() else {
                        return Err(InferError::new(InferErrorKind::Kind(ty), arg.span));
                    };
                    c.push(Constraint::new(
                        param.clone(),
                        arg.ty.clone(),
                        [arg.span, span],
                    ));
                    ty = ret.clone();
                    typed_args.push(arg);
                }

                if ty.is_fn() {
                    return Err(InferError::new(InferErrorKind::Kind(ty), span));
                }

                let subs = self.unify(c)?;
                for arg in &mut typed_args {
                    arg.substitute_many(&subs, &mut self.type_ctx);
                }
                ty = ty.substitute_many(&subs, &mut self.type_ctx);

                let kind = TypedPatKind::Constructor {
                    name,
                    args: typed_args.into_boxed_slice(),
                };

                Ok(TypedPat::new(kind, span, ty))
            }

            UntypedPatKind::Ident(name) => {
                let var = self.gen_type_var();
                self.insert_variable(name, var.clone());
                Ok(TypedPat::new(TypedPatKind::Ident(name), span, var))
            }

            UntypedPatKind::Module(_) => {
                unreachable!()
            }

            UntypedPatKind::IntRange(range) => Ok(TypedPat::new(
                TypedPatKind::IntRange(range),
                span,
                self.type_ctx().get_int(),
            )),
        }
    }

    fn check_match_arm(
        &mut self,
        pat: UntypedPat,
        expr: UntypedExpr,
    ) -> InferResult<(TypedPat, TypedExpr)> {
        self.env.push_scope();

        let pat = self.check_pat(pat)?;
        let expr = self.check(expr)?;

        self.env.pop_scope();

        Ok((pat, expr))
    }

    fn check_match(
        &mut self,
        expr: UntypedExpr,
        arms: Box<[UntypedMatchArm]>,
        span: Span,
    ) -> InferResult<TypedExpr> {
        let mut expr = self.check(expr)?;

        let var = self.gen_type_var();
        let mut typed_arms = Vec::new();

        let mut c = ConstraintSet::new();

        for arm in arms {
            let (pat, aexpr) = self.check_match_arm(arm.pat, arm.expr)?;
            c.push(Constraint::new(
                aexpr.ty.clone(),
                var.clone(),
                [aexpr.span, span],
            ));
            c.push(Constraint::new(
                expr.ty.clone(),
                pat.ty.clone(),
                [expr.span, pat.span, span],
            ));
            typed_arms.push(TypedMatchArm::new(pat, aexpr));
        }

        let subs = self.unify(c)?;

        expr.substitute_many(&subs, &mut self.type_ctx);
        for arm in &mut typed_arms {
            arm.pat.substitute_many(&subs, &mut self.type_ctx);
            arm.expr.substitute_many(&subs, &mut self.type_ctx);
        }
        let var = var.substitute_many(&subs, &mut self.type_ctx);

        let kind = TypedExprKind::Match {
            expr: Box::new(expr),
            arms: typed_arms.into_boxed_slice(),
        };

        Ok(TypedExpr::new(kind, span, var))
    }

    fn check_bin(
        &mut self,
        op: BinOp,
        lhs: UntypedExpr,
        rhs: UntypedExpr,
        span: Span,
    ) -> InferResult<TypedExpr> {
        if op.is_pipe() {
            return self.check_call(rhs, lhs, span);
        }

        let mut lhs = self.check(lhs)?;
        let mut rhs = self.check(rhs)?;

        let int = self.get_int();
        let bol = self.get_bool();

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                let c1 = Constraint::new(int.clone(), lhs.ty.clone(), [lhs.span, span]);
                let c2 = Constraint::new(int.clone(), rhs.ty.clone(), [rhs.span, span]);

                let subs = self.unify([c1, c2])?;

                lhs.substitute_many(&subs, &mut self.type_ctx);
                rhs.substitute_many(&subs, &mut self.type_ctx);

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok(TypedExpr::new(kind, span, int))
            }
            BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Ge | BinOp::Lt | BinOp::Le => {
                let c1 = Constraint::new(int.clone(), lhs.ty.clone(), [lhs.span, span]);
                let c2 = Constraint::new(int, rhs.ty.clone(), [rhs.span, span]);

                let subs = self.unify([c1, c2])?;

                lhs.substitute_many(&subs, &mut self.type_ctx);
                rhs.substitute_many(&subs, &mut self.type_ctx);

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok(TypedExpr::new(kind, span, bol))
            }
            BinOp::And | BinOp::Or => {
                let c1 = Constraint::new(bol.clone(), lhs.ty.clone(), [lhs.span, span]);
                let c2 = Constraint::new(bol.clone(), rhs.ty.clone(), [rhs.span, span]);

                let subs = self.unify([c1, c2])?;

                lhs.substitute_many(&subs, &mut self.type_ctx);
                rhs.substitute_many(&subs, &mut self.type_ctx);

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok(TypedExpr::new(kind, span, bol))
            }

            BinOp::Pipe => unreachable!(),
        }
    }

    fn check_un(&mut self, op: UnOp, expr: UntypedExpr, span: Span) -> InferResult<TypedExpr> {
        let mut expr = self.check(expr)?;

        let ty = match op {
            UnOp::Not => self.get_bool(),
            UnOp::Neg => self.get_int(),
        };
        let subs = self.unify(Constraint::new(
            ty.clone(),
            expr.ty.clone(),
            [expr.span, span],
        ))?;
        expr.substitute_many(&subs, &mut self.type_ctx);

        let kind = TypedExprKind::Un {
            op,
            expr: Box::new(expr),
        };

        Ok(TypedExpr::new(kind, span, ty))
    }

    fn instantiate(&mut self, ty: Rc<Ty>) -> Rc<Ty> {
        match ty.as_ref() {
            Ty::Scheme { quant, ty } => quant.iter().copied().fold(ty.clone(), |ty, quant| {
                let old = quant;
                let new = self.gen_type_var();
                let subs = Subs::new(old, new);
                ty.substitute_eq(&subs, &mut self.type_ctx)
            }),
            _ => ty,
        }
    }

    pub fn check_many_modules<I>(&mut self, modules: I) -> InferResult<Vec<TypedModule>>
    where
        I: IntoIterator<Item = UntypedModule>,
    {
        modules
            .into_iter()
            .map(|module| self.check_module(module))
            .collect()
    }

    pub fn check_module(&mut self, module: UntypedModule) -> InferResult<TypedModule> {
        self.env.push_scope();
        self.cur_module = module.name;

        let exprs = self.check_many(module.exprs)?;
        let declared = self.env.pop_scope().unwrap_or_else(|| unreachable!());
        let mut typed =
            TypedModule::new(module.name, declared, exprs.into_boxed_slice(), module.span);

        if let Some(mod_name) = module.name {
            while let Some(decl) = self.declared_types.pop() {
                let new_name = PathIdent::Module(ModuleIdent::new(mod_name, decl));
                let decl = PathIdent::Ident(decl);
                let mut subs = |ty: &Ty, env: &mut TypeCtx| match ty {
                    Ty::Named { name, args } if *name == decl => Some(env.intern_type(Ty::Named {
                        name: new_name,
                        args: args.clone(),
                    })),
                    _ => None,
                };
                typed.substitute(&mut subs, &mut self.type_ctx);
            }
            self.env.insert_module(mod_name, typed.declared.clone());
        } else {
            self.env
                .extend_global(typed.declared.iter().map(|(k, v)| (*k, v.clone())));
            self.declared_types.clear();
        }

        Ok(typed)
    }

    pub fn check_many<I>(&mut self, expr: I) -> InferResult<Vec<TypedExpr>>
    where
        I: IntoIterator<Item = UntypedExpr>,
    {
        expr.into_iter().map(|expr| self.check(expr)).collect()
    }

    pub fn check(&mut self, expr: UntypedExpr) -> InferResult<TypedExpr> {
        let span = expr.span;
        match expr.kind {
            UntypedExprKind::Acess(acess) => {
                let t = self
                    .env
                    .get_from_module(&acess)
                    .map_err(|kind| InferError::new(kind, span))?;

                Ok(TypedExpr::new(
                    TypedExprKind::Acess(acess),
                    span,
                    self.instantiate(t.ty().clone()),
                ))
            }

            UntypedExprKind::Unit => Ok(TypedExpr::new(TypedExprKind::Unit, span, self.get_unit())),

            UntypedExprKind::Int(i) => {
                Ok(TypedExpr::new(TypedExprKind::Int(i), span, self.get_int()))
            }

            UntypedExprKind::Bool(b) => Ok(TypedExpr::new(
                TypedExprKind::Bool(b),
                span,
                self.get_bool(),
            )),

            UntypedExprKind::Ident(id) => {
                let t = self
                    .get_variable(id)
                    .ok_or_else(|| InferError::new(InferErrorKind::Unbound(id), span))?;
                Ok(TypedExpr::new(
                    TypedExprKind::Ident(id),
                    span,
                    self.instantiate(t),
                ))
            }

            UntypedExprKind::Bin { op, lhs, rhs } => self.check_bin(op, *lhs, *rhs, span),

            UntypedExprKind::Un { op, expr } => self.check_un(op, *expr, span),

            UntypedExprKind::If {
                cond,
                then,
                otherwise,
            } => self.check_if(*cond, *then, *otherwise, span),

            UntypedExprKind::Fn { param, expr } => self.check_fn(param, *expr, span),

            UntypedExprKind::Call { callee, arg } => self.check_call(*callee, *arg, span),

            UntypedExprKind::Let {
                id,
                params,
                expr,
                body,
            } => self.check_let(id, params, *expr, body.map(|body| *body), span),

            UntypedExprKind::Semi(expr) => {
                let mut expr = self.check(*expr)?;
                expr.ty = self.get_unit();
                Ok(expr)
            }

            UntypedExprKind::Type {
                id,
                parameters,
                constructors,
            } => Ok(self.check_type(id, parameters, constructors, span)),

            UntypedExprKind::Match { expr, arms } => self.check_match(*expr, arms, span),
        }
    }

    pub fn type_ctx_mut(&mut self) -> &mut TypeCtx {
        &mut self.type_ctx
    }
}
