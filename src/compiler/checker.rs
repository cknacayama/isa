use super::{
    ast::{
        typed::{
            TypedExpr, TypedExprKind, TypedMatchArm, TypedModule, TypedParam, TypedPat,
            TypedPatKind,
        },
        untyped::{Expr, ExprKind, Module, Pat, PatKind},
        BinOp, Constructor, UnOp,
    },
    ctx::TypeCtx,
    env::Env,
    error::InferError,
    infer::{Constr, ConstrSet, InferResult, Subs, Substitute},
    types::Ty,
};
use crate::{
    global::Symbol,
    span::{Span, Spanned},
};
use std::rc::Rc;

#[derive(Debug, Default)]
pub struct Checker {
    env:            Env,
    type_env:       TypeCtx,
    cur_var:        u64,
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
            env: Env::default(),
            type_env,
            cur_var: 0,
            cur_module: None,
            declared_types: Vec::new(),
        }
    }

    #[must_use]
    pub fn env(&self) -> &Env {
        &self.env
    }

    #[must_use]
    pub fn type_env(&self) -> &TypeCtx {
        &self.type_env
    }

    pub fn type_env_mut(&mut self) -> &mut TypeCtx {
        &mut self.type_env
    }

    pub fn unify(&mut self, mut constr: ConstrSet) -> InferResult<Vec<Subs>> {
        constr.unify(&mut self.type_env)
    }

    fn insert_variable(&mut self, id: Symbol, ty: Rc<Ty>) -> Option<Rc<Ty>> {
        self.env.insert(id, ty)
    }

    fn intern_type(&mut self, ty: Ty) -> Rc<Ty> {
        self.type_env.intern_type(ty)
    }

    fn new_type_variable_id(&mut self) -> u64 {
        let cur = self.cur_var;
        self.cur_var += 1;
        cur
    }

    fn new_type_variable(&mut self) -> Rc<Ty> {
        let id = self.new_type_variable_id();
        self.intern_type(Ty::Var(id))
    }

    fn get_int(&self) -> Rc<Ty> {
        self.type_env.get_int()
    }

    fn get_unit(&self) -> Rc<Ty> {
        self.type_env.get_unit()
    }

    fn get_bool(&self) -> Rc<Ty> {
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
        let c_cond = Constr::new(cond.ty.clone(), self.get_bool(), cond.span);
        let var = self.new_type_variable();
        let c_then = Constr::new(var.clone(), then.ty.clone(), then.span);
        let c_otherwise = Constr::new(var.clone(), otherwise.ty.clone(), otherwise.span);

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
        param: Symbol,
        expr: Expr,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        self.env.push_scope();
        let var = self.new_type_variable();
        self.insert_variable(param, var.clone());
        let (expr, c) = self.check(expr)?;
        self.env.pop_scope();

        let ty = Ty::Fn {
            param: var.clone(),
            ret:   expr.ty.clone(),
        };
        let ty = self.intern_type(ty);
        let kind = TypedExprKind::Fn {
            param: TypedParam::new(param, var),
            expr:  Box::new(expr),
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
        let fn_ty = Ty::Fn {
            param: arg.ty.clone(),
            ret:   var.clone(),
        };
        let fn_ty = self.intern_type(fn_ty);
        let constr = Constr::new(callee.ty.clone(), fn_ty, span);

        c1.append(c2);
        c1.push(constr);

        let kind = TypedExprKind::Call {
            callee: Box::new(callee),
            arg:    Box::new(arg),
        };

        Ok((TypedExpr::new(kind, span, var), c1))
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
        params: Box<[Symbol]>,
        expr: Expr,
    ) -> InferResult<(TypedExpr, Box<[TypedParam]>, ConstrSet)> {
        self.env.push_scope();
        let rec = !params.is_empty();
        let mut c = ConstrSet::new();
        let mut typed_params = Vec::new();
        for p in params {
            let var = self.new_type_variable();
            self.insert_variable(p, var.clone());
            typed_params.push(TypedParam::new(p, var));
        }
        let (expr, c_expr) = if rec {
            let var = self.new_type_variable();
            self.insert_variable(id, var.clone());
            let (mut expr, c1) = self.check(expr)?;
            expr.ty = self.function_type(typed_params.iter().map(TypedParam::ty).cloned(), expr.ty);
            let constr = Constr::new(expr.ty.clone(), var, expr.span);
            c.push(constr);
            (expr, c1)
        } else {
            let (mut expr, c) = self.check(expr)?;
            expr.ty = self.function_type(typed_params.iter().map(TypedParam::ty).cloned(), expr.ty);
            (expr, c)
        };
        c.append(c_expr);
        self.env.pop_scope();
        Ok((expr, typed_params.into_boxed_slice(), c))
    }

    fn check_let(
        &mut self,
        id: Symbol,
        params: Box<[Symbol]>,
        expr: Expr,
        body: Option<Expr>,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        let (expr, params, mut c1) = self.check_let_value(id, params, expr)?;

        let s = self.unify(c1.clone())?;
        let u1 = expr.ty.clone().substitute_many(&s, &mut self.type_env);
        let mut env1 = self.env.clone().substitute_many(&s, &mut self.type_env);
        let u1 = env1.generalize(u1, &mut self.type_env);

        std::mem::swap(&mut self.env, &mut env1);
        self.insert_variable(id, u1);

        let (body, ty) = match body {
            Some(body) => {
                let (body, c2) = self.check(body)?;
                std::mem::swap(&mut self.env, &mut env1);
                c1.append(c2);
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

        Ok((TypedExpr::new(kind, span, ty), c1))
    }

    fn check_constructor(
        &mut self,
        constructor: &mut Constructor,
        subs: &[Subs],
        quant: Rc<[u64]>,
        mut ret: Rc<Ty>,
    ) {
        for param in constructor.params.iter_mut().rev() {
            *param = param.clone().substitute_many(subs, &mut self.type_env);
            ret = self.intern_type(Ty::Fn {
                param: param.clone(),
                ret,
            });
        }
        if !quant.is_empty() {
            ret = self.intern_type(Ty::Scheme { quant, ty: ret });
        }
        self.insert_variable(constructor.id, ret.clone());
        self.type_env.insert_constructor(constructor.id, ret);
    }

    fn check_type(
        &mut self,
        name: Symbol,
        parameters: Box<[Symbol]>,
        mut constructors: Box<[Constructor]>,
        span: Span,
    ) -> (TypedExpr, ConstrSet) {
        let mut args = Vec::new();
        let mut subs = Vec::new();
        let mut quant = Vec::new();

        for param in parameters {
            let id = self.new_type_variable_id();
            let new = self.intern_type(Ty::Var(id));
            let param = self.intern_type(Ty::Named {
                name: param,
                args: Rc::from([]),
            });
            subs.push(Subs::new(param, new.clone()));
            args.push(new);
            quant.push(id);
        }

        let quant = Rc::<[u64]>::from(quant);

        self.declared_types.push(name);

        let ty = self.intern_type(Ty::Named {
            name,
            args: args.clone().into(),
        });

        for c in &mut constructors {
            self.check_constructor(c, &subs, quant.clone(), ty.clone());
        }

        let kind = TypedExprKind::Type {
            id: name,
            parameters: args.into_boxed_slice(),
            constructors,
        };
        let expr = TypedExpr::new(kind, span, self.get_unit());

        (expr, ConstrSet::new())
    }

    fn check_pat(&mut self, Pat { data, span }: Pat) -> InferResult<(TypedPat, ConstrSet)> {
        match data {
            PatKind::Wild => {
                let var = self.new_type_variable();
                Ok((
                    TypedPat::new(TypedPatKind::Wild, span, var),
                    ConstrSet::new(),
                ))
            }
            PatKind::Ident(name) => {
                if let Some(constructor) = self.type_env.get_constructor(&name).cloned() {
                    let ty = self.instantiate(constructor);
                    if ty.is_named() {
                        let kind = TypedPatKind::Type {
                            name,
                            args: Box::from([]),
                        };
                        Ok((TypedPat::new(kind, span, ty), ConstrSet::new()))
                    } else {
                        Err(Spanned::new(InferError::Kind(ty), span))
                    }
                } else {
                    let var = self.new_type_variable();
                    self.insert_variable(name, var.clone());
                    Ok((
                        TypedPat::new(TypedPatKind::Ident(name), span, var),
                        ConstrSet::new(),
                    ))
                }
            }
            PatKind::Or(spanneds) => {
                let mut patterns = Vec::new();
                let mut c = ConstrSet::new();

                let var = self.new_type_variable();
                for pat in spanneds {
                    let (pat, c_pat) = self.check_pat(pat)?;
                    c.append(c_pat);
                    c.push(Constr::new(pat.ty.clone(), var.clone(), pat.span));
                    patterns.push(pat);
                }

                Ok((
                    TypedPat::new(TypedPatKind::Or(patterns.into_boxed_slice()), span, var),
                    c,
                ))
            }
            PatKind::Unit => Ok((
                TypedPat::new(TypedPatKind::Unit, span, self.get_unit()),
                ConstrSet::new(),
            )),
            PatKind::Int(i) => Ok((
                TypedPat::new(TypedPatKind::Int(i), span, self.get_int()),
                ConstrSet::new(),
            )),
            PatKind::Bool(b) => Ok((
                TypedPat::new(TypedPatKind::Bool(b), span, self.get_bool()),
                ConstrSet::new(),
            )),
            PatKind::Type { name, args } => match self.type_env.get_constructor(&name).cloned() {
                Some(mut ty) => {
                    ty = self.instantiate(ty);
                    let mut c = ConstrSet::new();
                    let mut typed_args = Vec::new();

                    for arg in args {
                        let (arg, c_arg) = self.check_pat(arg)?;
                        let Ty::Fn { param, ret } = ty.as_ref() else {
                            return Err(Spanned::new(InferError::Kind(ty), arg.span));
                        };
                        c.append(c_arg);
                        c.push(Constr::new(arg.ty.clone(), param.clone(), arg.span));
                        ty = ret.clone();
                        typed_args.push(arg);
                    }

                    let kind = TypedPatKind::Type {
                        name,
                        args: typed_args.into_boxed_slice(),
                    };

                    Ok((TypedPat::new(kind, span, ty), c))
                }
                None if args.is_empty() => {
                    let var = self.new_type_variable();
                    self.insert_variable(name, var.clone());
                    Ok((
                        TypedPat::new(TypedPatKind::Ident(name), span, var),
                        ConstrSet::new(),
                    ))
                }
                None => Err(Spanned::new(InferError::Unbound(name), span)),
            },
        }
    }

    fn check_match_arm(
        &mut self,
        pat: Pat,
        expr: Expr,
    ) -> InferResult<((TypedPat, TypedExpr), ConstrSet)> {
        self.env.push_scope();
        let (pat, mut c1) = self.check_pat(pat)?;
        let (expr, c2) = self.check(expr)?;

        c1.append(c2);

        self.env.pop_scope();

        Ok(((pat, expr), c1))
    }

    fn check_match(
        &mut self,
        expr: Expr,
        arms: Box<[(Pat, Expr)]>,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        let (expr, mut c1) = self.check(expr)?;

        let var = self.new_type_variable();
        let mut typed_arms = Vec::new();
        for (pat, aexpr) in arms {
            let ((pat, aexpr), c) = self.check_match_arm(pat, aexpr)?;
            c1.append(c);

            c1.push(Constr::new(expr.ty.clone(), pat.ty.clone(), pat.span));
            c1.push(Constr::new(aexpr.ty.clone(), var.clone(), aexpr.span));
            typed_arms.push(TypedMatchArm::new(pat, aexpr));
        }

        let kind = TypedExprKind::Match {
            expr: Box::new(expr),
            arms: typed_arms.into_boxed_slice(),
        };

        Ok((TypedExpr::new(kind, span, var), c1))
    }

    fn check_bin(
        &mut self,
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        let (lhs, mut c1) = self.check(lhs)?;
        let (rhs, c2) = self.check(rhs)?;
        c1.append(c2);

        let int = self.get_int();
        let bol = self.get_bool();

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                c1.push(Constr::new(int.clone(), lhs.ty.clone(), lhs.span));
                c1.push(Constr::new(int.clone(), rhs.ty.clone(), rhs.span));

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok((TypedExpr::new(kind, span, int), c1))
            }
            BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Ge | BinOp::Lt | BinOp::Le => {
                c1.push(Constr::new(int.clone(), lhs.ty.clone(), lhs.span));
                c1.push(Constr::new(int, rhs.ty.clone(), rhs.span));

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok((TypedExpr::new(kind, span, bol), c1))
            }
            BinOp::And | BinOp::Or => {
                c1.push(Constr::new(bol.clone(), lhs.ty.clone(), lhs.span));
                c1.push(Constr::new(bol.clone(), rhs.ty.clone(), rhs.span));

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok((TypedExpr::new(kind, span, bol), c1))
            }
        }
    }
    fn check_un(
        &mut self,
        op: UnOp,
        expr: Expr,
        span: Span,
    ) -> InferResult<(TypedExpr, ConstrSet)> {
        let (expr, mut c1) = self.check(expr)?;

        let ty = match op {
            UnOp::Not => self.get_bool(),
            UnOp::Neg => self.get_int(),
        };
        c1.push(Constr::new(ty.clone(), expr.ty.clone(), expr.span));

        let kind = TypedExprKind::Un {
            op,
            expr: Box::new(expr),
        };

        Ok((TypedExpr::new(kind, span, ty), c1))
    }

    fn instantiate(&mut self, ty: Rc<Ty>) -> Rc<Ty> {
        match ty.as_ref() {
            Ty::Scheme { quant, ty } => quant.iter().copied().fold(ty.clone(), |ty, quant| {
                let var = self.new_type_variable();
                let old = self.intern_type(Ty::Var(quant));
                let subs = Subs::new(old, var);
                ty.substitute_eq(&subs, &mut self.type_env)
            }),
            _ => ty,
        }
    }

    pub fn check_many_modules<I>(
        &mut self,
        modules: I,
    ) -> InferResult<(Vec<TypedModule>, ConstrSet)>
    where
        I: IntoIterator<Item = Module>,
    {
        let mut typed_modules = Vec::new();
        let mut cset = ConstrSet::new();

        for module in modules {
            let (module, c) = self.check_module(module)?;
            typed_modules.push(module);
            cset.append(c);
        }

        Ok((typed_modules, cset))
    }

    pub fn check_module(&mut self, module: Module) -> InferResult<(TypedModule, ConstrSet)> {
        self.env.push_scope();
        self.cur_module = module.name;

        let (exprs, mut cset) = self.check_many(module.exprs)?;
        let declared = self.env.pop_scope().unwrap_or_else(|| unreachable!());
        let mut typed =
            TypedModule::new(module.name, declared, exprs.into_boxed_slice(), module.span);

        if let Some(mod_name) = module.name {
            while let Some(decl) = self.declared_types.pop() {
                let new_name = mod_name.concat(decl, '.');
                let mut subs = |ty: &Ty, env: &mut TypeCtx| match ty {
                    Ty::Named { name, args } if name == &decl => Some(env.intern_type(Ty::Named {
                        name: new_name,
                        args: args.clone(),
                    })),
                    _ => None,
                };
                cset.substitute(&mut subs, &mut self.type_env);
                typed.substitute(&mut subs, &mut self.type_env);
            }
        } else {
            self.declared_types.clear();
        }

        Ok((typed, cset))
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
                    .ok_or_else(|| Spanned::new(InferError::Unbound(id), span))?
                    .clone();
                Ok((
                    TypedExpr::new(TypedExprKind::Ident(id), span, self.instantiate(t)),
                    ConstrSet::new(),
                ))
            }
            ExprKind::Bin { op, lhs, rhs } => self.check_bin(op, *lhs, *rhs, span),
            ExprKind::Un { op, expr } => self.check_un(op, *expr, span),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => self.check_if(*cond, *then, *otherwise, span),
            ExprKind::Fn { param, expr } => self.check_fn(param, *expr, span),
            ExprKind::Call { callee, arg } => self.check_call(*callee, *arg, span),
            ExprKind::Let {
                id,
                params,
                expr,
                body,
            } => self.check_let(id, params, *expr, body.map(|body| *body), span),
            ExprKind::Semi(expr) => {
                let (mut expr, cset) = self.check(*expr)?;
                expr.ty = self.get_unit();
                Ok((expr, cset))
            }
            ExprKind::Type {
                id,
                parameters,
                constructors,
            } => Ok(self.check_type(id, parameters, constructors, span)),

            ExprKind::Match { expr, arms } => self.check_match(*expr, arms, span),
        }
    }
}
