use std::rc::Rc;

use rustc_hash::FxHashMap;

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
use super::error::{DiagnosticLabel, InferError, InferErrorKind, IsaError, Uninferable};
use super::infer::{Constraint, ConstraintSet, Subs, Substitute, unify};
use super::types::Ty;
use crate::global::Symbol;
use crate::span::Span;

#[derive(Debug, Default)]
pub struct Checker {
    env:        Env,
    type_ctx:   TypeCtx,
    cur_module: Symbol,
}

pub type IsaResult<T> = Result<T, IsaError>;

impl Checker {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn unify<C>(&mut self, constr: C) -> Result<Vec<Subs>, Uninferable>
    where
        ConstraintSet: From<C>,
    {
        unify(constr).inspect(|subs| {
            self.env.substitute_many(subs);
        })
    }

    pub const fn modules(&self) -> &FxHashMap<Symbol, FxHashMap<Symbol, VarData>> {
        self.env.modules()
    }

    #[must_use]
    pub const fn type_ctx(&self) -> &TypeCtx {
        &self.type_ctx
    }

    fn insert_val(&mut self, id: Symbol, ty: Ty) -> Option<VarData> {
        self.env.insert_val(id, ty)
    }

    fn get_val_from_module(&self, id: &ModuleIdent) -> Result<Ty, InferErrorKind> {
        self.env.get_val_from_module(id)
    }

    fn insert_variable(&mut self, id: Symbol, ty: Ty) -> Option<VarData> {
        self.env.insert(id, ty)
    }

    fn get_variable(&self, id: Symbol) -> Option<Ty> {
        self.env
            .get(id)
            .or_else(|| {
                let module_access = ModuleIdent::new(self.cur_module, id);
                self.env.get_from_module(&module_access).ok()
            })
            .map(VarData::ty)
            .cloned()
    }

    fn insert_constructor(&mut self, name: Symbol, ty: Ty) -> Option<VarData> {
        self.env.insert_constructor(name, ty)
    }

    fn get_constructor(&self, name: Symbol) -> Option<Ty> {
        self.env.get_constructor(name).or_else(|| {
            let module_access = ModuleIdent::new(self.cur_module, name);
            self.env.get_constructor_from_module(&module_access).ok()
        })
    }

    const fn gen_id(&mut self) -> u64 {
        self.type_ctx.gen_id()
    }

    const fn gen_type_var(&mut self) -> Ty {
        self.type_ctx.gen_type_var()
    }

    fn check_if(
        &mut self,
        cond: UntypedExpr,
        then: UntypedExpr,
        otherwise: UntypedExpr,
        span: Span,
    ) -> IsaResult<TypedExpr> {
        let mut cond = self.check(cond)?;
        let mut then = self.check(then)?;
        let mut otherwise = self.check(otherwise)?;

        let mut var = self.gen_type_var();

        let c_cond = Constraint::new(Ty::Bool, cond.ty.clone(), cond.span);
        let c_then = Constraint::new(var.clone(), then.ty.clone(), then.span);
        let c_otherwise = Constraint::new(var.clone(), otherwise.ty.clone(), otherwise.span);

        let subs = self.unify([c_cond, c_then, c_otherwise]).map_err(|err| {
            let err_span = err.constr().span();

            let (fst_label, labels) = if err_span == cond.span {
                let mut ty = cond.ty.clone();
                ty.substitute_many(err.subs());
                let fst =
                    DiagnosticLabel::new("expected `if` condition to have type `bool`", err_span);
                let snd = DiagnosticLabel::new(format!("this is of type `{ty}`"), err_span);
                (fst, vec![snd])
            } else {
                let mut then_ty = then.ty.clone();
                let mut els_ty = otherwise.ty.clone();
                then_ty.substitute_many(err.subs());
                els_ty.substitute_many(err.subs());
                let fst = DiagnosticLabel::new("`if` and `else` have different types", span);
                let snd = DiagnosticLabel::new(format!("`if` has type `{then_ty}`"), then.span);
                let trd =
                    DiagnosticLabel::new(format!("`else` has type `{els_ty}`"), otherwise.span);

                (fst, vec![snd, trd])
            };

            IsaError::new("type mismatch", fst_label, labels)
        })?;

        var.substitute_many(&subs);
        cond.substitute_many(&subs);
        then.substitute_many(&subs);
        otherwise.substitute_many(&subs);

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
    ) -> IsaResult<TypedExpr> {
        self.env.push_scope();

        let var = self.gen_type_var();
        self.insert_variable(param.name, var);

        let expr = self.check(expr)?;
        let var = self.get_variable(param.name).unwrap();

        self.env.pop_scope();

        let ty = Ty::Fn {
            param: Rc::new(var.clone()),
            ret:   Rc::new(expr.ty.clone()),
        };

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
    ) -> IsaResult<TypedExpr> {
        let mut callee = self.check(callee)?;
        let mut arg = self.check(arg)?;

        let mut var = self.gen_type_var();
        let fn_ty = Ty::Fn {
            param: Rc::new(arg.ty.clone()),
            ret:   Rc::new(var.clone()),
        };
        let constr = Constraint::new(callee.ty.clone(), fn_ty, span);
        let subs = self.unify(constr).map_err(|err| {
            callee.ty.substitute_many(err.subs());
            arg.ty.substitute_many(err.subs());
            let (fst, labels) = if let Ty::Fn { ref param, .. } = callee.ty {
                let fst =
                    DiagnosticLabel::new(format!("expected `{param}`, got {}", arg.ty), arg.span);
                let snd =
                    DiagnosticLabel::new(format!("this is of type `{}`", callee.ty), callee.span);
                (fst, vec![snd])
            } else {
                let fst = DiagnosticLabel::new(
                    format!("expected callable, got `{}`", callee.ty),
                    callee.span,
                );
                (fst, Vec::new())
            };

            IsaError::new("type mismatch", fst, labels)
        })?;

        callee.substitute_many(&subs);
        arg.substitute_many(&subs);

        var.substitute_many(&subs);

        let kind = TypedExprKind::Call {
            callee: Box::new(callee),
            arg:    Box::new(arg),
        };

        Ok(TypedExpr::new(kind, span, var))
    }

    fn function_type<I>(params: I, ret: Ty) -> Ty
    where
        I: IntoIterator<Item = Ty>,
        I::IntoIter: DoubleEndedIterator,
    {
        params.into_iter().rev().fold(ret, |ret, param| Ty::Fn {
            param: Rc::new(param),
            ret:   Rc::new(ret),
        })
    }

    fn check_let_value(
        &mut self,
        id: Symbol,
        params: Box<[UntypedParam]>,
        expr: UntypedExpr,
    ) -> IsaResult<(TypedExpr, Box<[TypedParam]>)> {
        self.env.push_scope();

        let mut typed_params = params
            .into_iter()
            .map(|p| {
                let var = self.gen_type_var();
                self.insert_variable(p.name, var.clone());
                TypedParam::new(p.name, var, p.span)
            })
            .collect::<Box<_>>();

        let mut expr = if typed_params.is_empty() {
            self.check(expr)?
        } else {
            let var_id = self.gen_id();
            let var = Ty::Var(var_id);
            self.insert_variable(id, var);

            let mut expr = self.check(expr)?;

            for p in &mut typed_params {
                p.ty = self.get_variable(p.name).unwrap();
            }

            expr.ty =
                Self::function_type(typed_params.iter().map(TypedParam::ty).cloned(), expr.ty);

            let subs = Subs::new(var_id, expr.ty.clone());

            expr.substitute_eq(&subs);
            expr
        };

        self.env.pop_scope();

        let module_id = ModuleIdent::new(self.cur_module, id);

        if let Ok(val_ty) = self.get_val_from_module(&module_id) {
            let constr = Constraint::new(val_ty.clone(), expr.ty.clone(), expr.span);
            let subs = self.unify(constr).map_err(|err| {
                let fst = DiagnosticLabel::new(
                    format!("expected `let` bind expression to have type `{val_ty}`"),
                    err.constr().span(),
                );
                let snd = DiagnosticLabel::new(
                    format!("this is of type `{}`", err.constr().rhs()),
                    err.constr().span(),
                );

                IsaError::new("type mismatch", fst, vec![snd])
            })?;

            expr.substitute_many(&subs);
            for p in &mut typed_params {
                p.substitute_many(&subs);
            }
        }

        Ok((expr, typed_params))
    }

    fn check_let(
        &mut self,
        id: Symbol,
        params: Box<[UntypedParam]>,
        expr: UntypedExpr,
        body: Option<UntypedExpr>,
        span: Span,
    ) -> IsaResult<TypedExpr> {
        let (expr, params) = self.check_let_value(id, params, expr)?;

        let u1 = self.env.generalize(expr.ty.clone());
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
            None => (None, Ty::Unit),
        };

        let kind = TypedExprKind::Let {
            name: id,
            params,
            expr: Box::new(expr),
            body: body.map(Box::new),
        };

        Ok(TypedExpr::new(kind, span, ty))
    }

    fn check_constructor(&mut self, constructor: &Constructor, quant: Rc<[u64]>, mut ret: Ty) {
        for param in constructor.params.iter().rev() {
            ret = Ty::Fn {
                param: Rc::new(param.clone()),
                ret:   Rc::new(ret),
            };
        }
        if !quant.is_empty() {
            ret = Ty::Scheme {
                quant,
                ty: Rc::new(ret),
            };
        }
        self.insert_constructor(constructor.name, ret);
    }

    fn check_type_definition(
        &mut self,
        name: Symbol,
        parameters: Box<[Ty]>,
        constructors: Box<[Constructor]>,
        span: Span,
    ) -> TypedExpr {
        let mut quant = Vec::new();

        for param in &parameters {
            let new = param.as_var().unwrap();
            quant.push(new);
        }

        let quant = Rc::<[u64]>::from(quant);

        let ty = Ty::Named {
            name: PathIdent::Module(ModuleIdent::new(self.cur_module, name)),
            args: parameters.clone().into(),
        };

        for c in &constructors {
            self.check_constructor(c, quant.clone(), ty.clone());
            self.type_ctx.insert_constructor(&ty, c.clone());
        }

        let kind = TypedExprKind::Type {
            name,
            parameters,
            constructors,
        };

        TypedExpr::new(kind, span, Ty::Unit)
    }

    fn check_val(&mut self, name: Symbol, params: Box<[Ty]>, mut ty: Ty, span: Span) -> TypedExpr {
        let mut new_params = Vec::new();
        let mut quant = Vec::new();
        for p in params {
            let new = self.gen_id();
            quant.push(new);
            new_params.push((p, new));
        }

        if !new_params.is_empty() {
            ty.substitute(&mut |ty| {
                new_params
                    .iter()
                    .find_map(|(old, new)| if ty == old { Some(Ty::Var(*new)) } else { None })
            });
            ty = Ty::Scheme {
                quant: quant.clone().into(),
                ty:    Rc::new(ty),
            }
        }

        self.insert_val(name, ty.clone());

        let kind = TypedExprKind::Val {
            name,
            parameters: quant.into_iter().map(Ty::Var).collect(),
            ty,
        };

        TypedExpr::new(kind, span, Ty::Unit)
    }

    fn check_pat(&mut self, UntypedPat { kind, span, .. }: UntypedPat) -> IsaResult<TypedPat> {
        match kind {
            UntypedPatKind::Wild => {
                let var = self.gen_type_var();
                Ok(TypedPat::new(TypedPatKind::Wild, span, var))
            }
            UntypedPatKind::Or(spanneds) => {
                let mut patterns = Vec::new();
                let mut c = ConstraintSet::new();

                let mut var = self.gen_type_var();
                for pat in spanneds {
                    let pat = self.check_pat(pat)?;
                    c.push(Constraint::new(pat.ty.clone(), var.clone(), pat.span));
                    patterns.push(pat);
                }

                let subs = match self.unify(c) {
                    Ok(subs) => subs,
                    Err(_) => todo!(),
                };

                for p in &mut patterns {
                    p.substitute_many(&subs);
                }
                var.substitute_many(&subs);

                Ok(TypedPat::new(
                    TypedPatKind::Or(patterns.into_boxed_slice()),
                    span,
                    var,
                ))
            }
            UntypedPatKind::Unit => Ok(TypedPat::new(TypedPatKind::Unit, span, Ty::Unit)),
            UntypedPatKind::Int(i) => Ok(TypedPat::new(TypedPatKind::Int(i), span, Ty::Int)),
            UntypedPatKind::Bool(b) => Ok(TypedPat::new(TypedPatKind::Bool(b), span, Ty::Bool)),
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
                        None => {
                            return Err(InferError::new(InferErrorKind::Unbound(name), span).into());
                        }
                    },
                };

                let mut ty = self.instantiate(ty);

                let mut c = ConstraintSet::new();
                let mut typed_args = Vec::new();

                for arg in args {
                    let arg = self.check_pat(arg)?;
                    let Ty::Fn { param, ret } = &ty else {
                        return Err(
                            InferError::new(InferErrorKind::NotConstructor(ty), arg.span).into(),
                        );
                    };
                    c.push(Constraint::new(
                        param.as_ref().clone(),
                        arg.ty.clone(),
                        span,
                    ));
                    ty = ret.as_ref().clone();
                    typed_args.push(arg);
                }

                if ty.is_fn() {
                    return Err(InferError::new(InferErrorKind::Kind(ty), span).into());
                }

                let subs = self.unify(c)?;
                for arg in &mut typed_args {
                    arg.substitute_many(&subs);
                }
                ty.substitute_many(&subs);

                let kind = TypedPatKind::Constructor {
                    name,
                    args: typed_args.into_boxed_slice(),
                };

                Ok(TypedPat::new(kind, span, ty))
            }

            UntypedPatKind::Ident(_) => {
                unreachable!("Parser never returns Ident pattern")
            }

            UntypedPatKind::IntRange(range) => {
                Ok(TypedPat::new(TypedPatKind::IntRange(range), span, Ty::Int))
            }
        }
    }

    fn check_match_arm(
        &mut self,
        pat: UntypedPat,
        expr: UntypedExpr,
    ) -> IsaResult<(TypedPat, TypedExpr)> {
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
    ) -> IsaResult<TypedExpr> {
        let mut expr = self.check(expr)?;

        let mut var = self.gen_type_var();
        let mut typed_arms = Vec::new();

        let mut c = ConstraintSet::new();

        for arm in arms {
            let (pat, aexpr) = self.check_match_arm(arm.pat, arm.expr)?;
            c.push(Constraint::new(var.clone(), aexpr.ty.clone(), aexpr.span));
            c.push(Constraint::new(expr.ty.clone(), pat.ty.clone(), pat.span));
            typed_arms.push(TypedMatchArm::new(pat, aexpr));
        }

        let subs = self.unify(c)?;

        expr.substitute_many(&subs);
        for arm in &mut typed_arms {
            arm.pat.substitute_many(&subs);
            arm.expr.substitute_many(&subs);
        }
        var.substitute_many(&subs);

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
    ) -> IsaResult<TypedExpr> {
        if op.is_pipe() {
            return self.check_call(rhs, lhs, span);
        }

        let mut lhs = self.check(lhs)?;
        let mut rhs = self.check(rhs)?;

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                let c1 = Constraint::new(Ty::Int, lhs.ty.clone(), lhs.span);
                let c2 = Constraint::new(Ty::Int, rhs.ty.clone(), rhs.span);

                let subs = self.unify([c1, c2]).map_err(|err| {
                    let fst = DiagnosticLabel::new(
                        format!("expected `int`, got `{}`", err.constr().rhs()),
                        err.constr().span(),
                    );
                    let note = format!("operator `{op}` expects operands of type `int`");

                    IsaError::new("type mismatch", fst, Vec::new()).with_note(note)
                })?;

                lhs.substitute_many(&subs);
                rhs.substitute_many(&subs);

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok(TypedExpr::new(kind, span, Ty::Int))
            }
            BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Ge | BinOp::Lt | BinOp::Le => {
                let c1 = Constraint::new(Ty::Int, lhs.ty.clone(), lhs.span);
                let c2 = Constraint::new(Ty::Int, rhs.ty.clone(), rhs.span);

                let subs = self.unify([c1, c2]).map_err(|err| {
                    let fst = DiagnosticLabel::new(
                        format!("expected `int`, got `{}`", err.constr().rhs()),
                        err.constr().span(),
                    );
                    let note = format!("operator `{op}` expects operands of type `int`");

                    IsaError::new("type mismatch", fst, Vec::new()).with_note(note)
                })?;

                lhs.substitute_many(&subs);
                rhs.substitute_many(&subs);

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok(TypedExpr::new(kind, span, Ty::Bool))
            }
            BinOp::And | BinOp::Or => {
                let c1 = Constraint::new(Ty::Bool, lhs.ty.clone(), lhs.span);
                let c2 = Constraint::new(Ty::Bool, rhs.ty.clone(), rhs.span);

                let subs = self.unify([c1, c2]).map_err(|err| {
                    let fst = DiagnosticLabel::new(
                        format!("expected `bool`, got `{}`", err.constr().rhs()),
                        err.constr().span(),
                    );
                    let note = format!("operator `{op}` expects operands of type `bool`");

                    IsaError::new("type mismatch", fst, Vec::new()).with_note(note)
                })?;

                lhs.substitute_many(&subs);
                rhs.substitute_many(&subs);

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok(TypedExpr::new(kind, span, Ty::Bool))
            }

            BinOp::Pipe => unreachable!(),
        }
    }

    fn check_un(&mut self, op: UnOp, expr: UntypedExpr, span: Span) -> IsaResult<TypedExpr> {
        let mut expr = self.check(expr)?;

        let ty = match op {
            UnOp::Not => Ty::Bool,
            UnOp::Neg => Ty::Int,
        };
        let constr = Constraint::new(ty.clone(), expr.ty.clone(), expr.span);

        let subs = self.unify(constr).map_err(|err| {
            let note = format!("{op} operates on type `{ty}`");
            IsaError::from(err).with_note(note)
        })?;

        expr.substitute_many(&subs);

        let kind = TypedExprKind::Un {
            op,
            expr: Box::new(expr),
        };

        Ok(TypedExpr::new(kind, span, ty))
    }

    fn instantiate(&mut self, ty: Ty) -> Ty {
        match ty {
            Ty::Scheme { quant, ty } => {
                let subs: Vec<_> = (0..quant.len()).map(|_| self.gen_type_var()).collect();
                let mut ty = ty.as_ref().clone();

                ty.substitute(&mut |ty| {
                    let v = ty.as_var()?;
                    quant
                        .iter()
                        .copied()
                        .enumerate()
                        .find_map(|(i, n)| if v == n { Some(subs[i].clone()) } else { None })
                });
                ty
            }
            _ => ty,
        }
    }

    fn check_module_types(&mut self, module: &mut UntypedModule) {
        let mut declared = Vec::new();
        let mod_name = module.name;

        for decl in module
            .exprs
            .iter_mut()
            .filter_map(|expr| self.check_type_declaration(expr))
        {
            let new_name = PathIdent::Module(ModuleIdent::new(mod_name, decl));
            let decl = PathIdent::Ident(decl);
            declared.push((decl, new_name));
        }

        if declared.is_empty() {
            return;
        }

        module.substitute(&mut |ty| match ty {
            Ty::Named { name, args } => declared.iter().find_map(|(decl, new)| {
                if name == decl {
                    Some(Ty::Named {
                        name: *new,
                        args: args.clone(),
                    })
                } else {
                    None
                }
            }),
            _ => None,
        });
    }

    fn check_type_declaration(&mut self, expr: &mut UntypedExpr) -> Option<Symbol> {
        match &mut expr.kind {
            UntypedExprKind::Semi(e) => self.check_type_declaration(e),
            UntypedExprKind::Type {
                name,
                parameters,
                constructors,
            } => {
                let mut subs = Vec::new();

                for param in parameters {
                    let id = self.gen_id();
                    let mut new = Ty::Var(id);
                    std::mem::swap(param, &mut new);
                    subs.push((new, id));
                }

                for ctor in constructors {
                    ctor.substitute(&mut |ty| {
                        subs.iter().find_map(
                            |(old, new)| {
                                if ty == old { Some(Ty::Var(*new)) } else { None }
                            },
                        )
                    });
                }

                Some(*name)
            }

            _ => None,
        }
    }

    pub fn check_many_modules(
        &mut self,
        mut modules: Vec<UntypedModule>,
    ) -> IsaResult<Vec<TypedModule>> {
        let mut decl = Vec::new();
        for module in &mut modules {
            self.check_module_types(module);

            self.env.push_scope();
            self.cur_module = module.name;

            let exprs = module
                .exprs
                .extract_if(.., |e| e.kind.is_type_or_val())
                .map(|e| self.check(e))
                .collect::<IsaResult<Vec<_>>>()?;

            let declared = self.env.pop_scope().unwrap();
            self.env.extend_module(module.name, declared.into_iter());

            decl.push(exprs);
        }

        modules
            .into_iter()
            .zip(decl)
            .map(|(module, mut decl)| {
                let mut module = self.check_module(module)?;
                decl.append(&mut module.exprs);
                module.exprs = decl;
                Ok(module)
            })
            .collect()
    }

    fn check_module(&mut self, module: UntypedModule) -> IsaResult<TypedModule> {
        self.env.push_scope();
        self.cur_module = module.name;

        let exprs = module
            .exprs
            .into_iter()
            .map(|expr| self.check(expr))
            .collect::<IsaResult<_>>()?;
        let declared = self.env.pop_scope().unwrap();
        let typed = TypedModule::new(module.name, exprs, module.span);

        self.env.extend_module(module.name, declared.into_iter());

        Ok(typed)
    }

    fn check(&mut self, expr: UntypedExpr) -> IsaResult<TypedExpr> {
        let span = expr.span;
        match expr.kind {
            UntypedExprKind::ModuleIdent(acess) => {
                let t = self
                    .env
                    .get_from_module(&acess)
                    .map_err(|kind| InferError::new(kind, span))?;

                Ok(TypedExpr::new(
                    TypedExprKind::ModuleIdent(acess),
                    span,
                    self.instantiate(t.ty().clone()),
                ))
            }

            UntypedExprKind::Unit => Ok(TypedExpr::new(TypedExprKind::Unit, span, Ty::Unit)),

            UntypedExprKind::Int(i) => Ok(TypedExpr::new(TypedExprKind::Int(i), span, Ty::Int)),

            UntypedExprKind::Bool(b) => Ok(TypedExpr::new(TypedExprKind::Bool(b), span, Ty::Bool)),

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
                name,
                params,
                expr,
                body,
            } => self.check_let(name, params, *expr, body.map(|body| *body), span),

            UntypedExprKind::Semi(expr) => {
                let mut expr = self.check(*expr)?;
                expr.ty = Ty::Unit;
                Ok(expr)
            }

            UntypedExprKind::Type {
                name,
                parameters,
                constructors,
            } => Ok(self.check_type_definition(name, parameters, constructors, span)),

            UntypedExprKind::Val {
                name,
                parameters,
                ty,
            } => Ok(self.check_val(name, parameters, ty, span)),

            UntypedExprKind::Match { expr, arms } => self.check_match(*expr, arms, span),
        }
    }
}
