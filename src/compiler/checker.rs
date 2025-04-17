use std::rc::Rc;

use rustc_hash::FxHashMap;
use smallvec::smallvec;

use super::ast::typed::{
    TypedConstructor, TypedExpr, TypedExprKind, TypedLetBind, TypedMatchArm, TypedModule,
    TypedParam, TypedPat, TypedPatKind,
};
use super::ast::untyped::{
    UntypedConstructor, UntypedExpr, UntypedExprKind, UntypedLetBind, UntypedMatchArm,
    UntypedModule, UntypedParam, UntypedPat, UntypedPatKind,
};
use super::ast::{BinOp, Constructor, Path, UnOp, ValDeclaration};
use super::ctx::{
    AliasData, ClassData, Ctx, Generator, IdGenerator, InstanceData, MemberData, ModuleData,
    VarData,
};
use super::error::{
    CheckError, CheckErrorKind, CheckResult, DiagnosticLabel, IsaError, Uninferable,
};
use super::infer::{
    ClassConstraint, ClassConstraintSet as Set, Constraint, EqConstraint, EqConstraintSet, Subs,
    Substitute, unify,
};
use super::token::Ident;
use super::types::Ty;
use crate::global::{self};
use crate::span::Span;

#[derive(Debug, Default)]
pub struct Checker {
    ctx:       Ctx,
    generator: IdGenerator,
}

pub type IsaResult<T> = Result<T, IsaError>;

impl Checker {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn unify<EqSet, ClassSet>(
        &mut self,
        constr: EqSet,
        classes: ClassSet,
    ) -> Result<(Vec<Subs>, Set), Uninferable>
    where
        EqConstraintSet: From<EqSet>,
        Set: From<ClassSet>,
    {
        unify(constr, classes, &self.ctx).inspect(|(subs, _)| {
            self.ctx.substitute_many(subs);
        })
    }

    #[must_use]
    pub const fn ctx(&self) -> &Ctx {
        &self.ctx
    }

    fn insert_val<ClassSet>(
        &mut self,
        id: Ident,
        ty: Ty,
        set: ClassSet,
        span: Span,
    ) -> Option<VarData>
    where
        Set: From<ClassSet>,
    {
        self.ctx
            .current_mut()
            .unwrap()
            .insert_val(id, VarData::new(ty, Set::from(set), span))
    }

    fn insert_let<ClassSet>(
        &mut self,
        id: Ident,
        ty: Ty,
        set: ClassSet,
        span: Span,
    ) -> Option<VarData>
    where
        Set: From<ClassSet>,
    {
        self.ctx
            .insert_var(id, VarData::new(ty, Set::from(set), span))
    }

    fn get_var_ty(&self, id: Ident) -> CheckResult<Ty> {
        self.ctx.get_var(id).map(VarData::ty).cloned()
    }

    fn gen_id(&mut self) -> u64 {
        self.generator.gen_id()
    }

    fn gen_type_var(&mut self) -> Ty {
        self.generator.gen_type_var()
    }

    fn check_if(
        &mut self,
        cond: UntypedExpr,
        then: UntypedExpr,
        otherwise: UntypedExpr,
        span: Span,
    ) -> IsaResult<(TypedExpr, Set)> {
        let (mut cond, set) = self.check(cond)?;
        let (mut then, then_set) = self.check(then)?;
        let (mut otherwise, else_set) = self.check(otherwise)?;

        let c_cond = EqConstraint::new(Ty::Bool, cond.ty.clone(), cond.span);
        let c_body = EqConstraint::new(then.ty.clone(), otherwise.ty.clone(), otherwise.span);

        let (subs, set) = self
            .unify([c_cond, c_body], set.concat(then_set).concat(else_set))
            .map_err(|err| {
                if err.constr().is_class() {
                    return IsaError::from(err);
                }

                let err_span = err.constr().span();

                let (fst_label, labels) = match err.constr() {
                    Constraint::Eq(constr) if err_span == cond.span => {
                        let fst = DiagnosticLabel::new(
                            "expected if condition to have type `bool`",
                            err_span,
                        );
                        let snd = DiagnosticLabel::new(
                            format!("this is of type `{}`", constr.rhs()),
                            err_span,
                        );
                        (fst, vec![snd])
                    }
                    Constraint::Eq(_) => {
                        let mut then_ty = then.ty.clone();
                        let mut els_ty = otherwise.ty.clone();
                        then_ty.substitute_many(err.subs());
                        els_ty.substitute_many(err.subs());
                        let fst = DiagnosticLabel::new("if and else have different types", span);
                        let snd =
                            DiagnosticLabel::new(format!("if has type `{then_ty}`"), then.span);
                        let trd = DiagnosticLabel::new(
                            format!("else has type `{els_ty}`"),
                            otherwise.span,
                        );

                        (fst, vec![snd, trd])
                    }
                    Constraint::Class(_) => unreachable!(),
                };

                IsaError::new("type mismatch", fst_label, labels)
            })?;

        cond.substitute_many(&subs);
        then.substitute_many(&subs);
        otherwise.substitute_many(&subs);

        let ty = then.ty.clone();

        let kind = TypedExprKind::If {
            cond:      Box::new(cond),
            then:      Box::new(then),
            otherwise: Box::new(otherwise),
        };

        Ok((TypedExpr::new(kind, span, ty), set))
    }

    fn check_fn(
        &mut self,
        param: UntypedParam,
        expr: UntypedExpr,
        span: Span,
    ) -> IsaResult<(TypedExpr, Set)> {
        self.ctx.push_scope();

        let var = self.gen_type_var();
        self.insert_let(param.name, var, [], param.name.span);

        let (expr, set) = self.check(expr)?;
        let var = self.get_var_ty(param.name).unwrap();

        self.ctx.pop_scope();

        let ty = Ty::Fn {
            param: Rc::new(var.clone()),
            ret:   Rc::new(expr.ty.clone()),
        };

        let kind = TypedExprKind::Fn {
            param: TypedParam::new(param.name, var),
            expr:  Box::new(expr),
        };

        Ok((TypedExpr::new(kind, span, ty), set))
    }

    fn check_call(
        &mut self,
        callee: UntypedExpr,
        arg: UntypedExpr,
        span: Span,
    ) -> IsaResult<(TypedExpr, Set)> {
        let (mut callee, set) = self.check(callee)?;
        let (mut arg, arg_set) = self.check(arg)?;

        let mut var = self.gen_type_var();
        let fn_ty = Ty::Fn {
            param: Rc::new(arg.ty.clone()),
            ret:   Rc::new(var.clone()),
        };
        let constr = EqConstraint::new(callee.ty.clone(), fn_ty, span);
        let (subs, set) = self.unify(constr, set.concat(arg_set)).map_err(|err| {
            if err.constr().is_class() {
                return IsaError::from(err);
            }

            callee.ty.substitute_many(err.subs());
            arg.ty.substitute_many(err.subs());

            let (fst, labels) = if let Ty::Fn { ref param, .. } = callee.ty {
                let fst = DiagnosticLabel::new(
                    format!("expected `{param}` argument, got `{}`", arg.ty),
                    arg.span,
                );
                let snd =
                    DiagnosticLabel::new(format!("this has type `{}`", callee.ty), callee.span);
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

        Ok((TypedExpr::new(kind, span, var), set))
    }

    fn check_let_bind_with_val(
        &mut self,
        bind: UntypedLetBind,
        val_decl: &Ty,
        val_set: Set,
        ty_span: Span,
    ) -> IsaResult<(Ty, TypedExpr, Box<[TypedParam]>, Set)> {
        self.ctx.push_scope();

        let mut param_iter = val_decl.param_iter();

        let mut typed_params = bind
            .params
            .into_iter()
            .map(|p| {
                let decl = param_iter.next().ok_or_else(|| {
                    let fst =
                        DiagnosticLabel::new(format!("expected `{val_decl}`"), bind.name.span);
                    let snd = DiagnosticLabel::new("more parameters than expected", p.name.span);
                    let trd = DiagnosticLabel::new("expected due to this", ty_span);

                    IsaError::new("type mismatch", fst, vec![snd, trd])
                        .with_note("let bind should have same type as val declaration")
                })?;
                self.insert_let(p.name, decl.clone(), [], p.name.span);
                Ok(TypedParam::new(p.name, decl))
            })
            .collect::<IsaResult<Box<_>>>()?;

        let (mut expr, set) = if typed_params.is_empty() {
            self.check(*bind.expr)?
        } else {
            self.ctx.assume_constraints(&val_set);
            let (mut expr, set) = self.check(*bind.expr)?;

            for p in &mut typed_params {
                p.ty = self.get_var_ty(p.name).unwrap();
            }

            expr.ty = Ty::function_type(typed_params.iter().map(TypedParam::ty).cloned(), expr.ty);
            (expr, set)
        };

        self.ctx.pop_scope();

        let (val_ty, val_subs) = self.instantiate(val_decl.clone());
        let ty = expr.ty.clone();
        let val_free = val_ty.free_type_variables();

        let mut val_set = val_set;
        val_set.substitute_many(&val_subs);

        let constr = EqConstraint::new(val_ty, ty, expr.span);

        let val_error = |ty: &Ty, span| {
            let fst = DiagnosticLabel::new(format!("expected `{val_decl}`"), bind.name.span);
            let snd = DiagnosticLabel::new(format!("this has type `{ty}`"), span);
            let trd = DiagnosticLabel::new("expected due to this", ty_span);

            IsaError::new("type mismatch", fst, vec![snd, trd])
                .with_note("let bind should have same type as val declaration")
        };

        let (subs, set) = unify(constr, set, &self.ctx)
            .map_err(|err| {
                if let Constraint::Eq(eq_constraint) = err.constr() {
                    val_error(eq_constraint.rhs(), eq_constraint.span())
                } else {
                    IsaError::from(err)
                        .with_note("let bind should have same type as val declaration")
                }
            })
            .and_then(|(subs, set)| {
                if subs.iter().any(|s| val_free.contains(&s.old())) {
                    expr.ty.substitute_many(&subs);
                    let ty = self.ctx.generalize(expr.ty.clone());
                    Err(val_error(&ty, expr.span))
                } else {
                    Ok((subs, set))
                }
            })?;

        if let Some(c) = set.iter().find(|c| !val_set.contains(c)) {
            let fst = DiagnosticLabel::new(
                format!("type `{}` is not instance of `{}`", c.ty(), c.class()),
                c.span(),
            );
            let snd = DiagnosticLabel::new("declared here", ty_span);

            return Err(IsaError::new("class mismatch", fst, vec![snd])
                .with_note("let bind should have same type as val declaration"));
        }

        expr.ty.substitute_many(&subs);
        for p in &mut typed_params {
            p.ty.substitute_many(&subs);
        }

        let ty = self.ctx.generalize(expr.ty.clone());

        Ok((ty, expr, typed_params, val_set))
    }

    fn check_let_bind(
        &mut self,
        bind: UntypedLetBind,
    ) -> IsaResult<(Ty, TypedExpr, Box<[TypedParam]>, Set)> {
        if let Ok(val) = self.ctx.current()?.get_val(bind.name) {
            let VarData {
                ty, constrs, span, ..
            } = val.clone();
            return self.check_let_bind_with_val(bind, &ty, constrs, span);
        }

        self.ctx.push_scope();

        let mut typed_params = bind
            .params
            .into_iter()
            .map(|p| {
                let var = self.gen_type_var();
                self.insert_let(p.name, var.clone(), [], p.name.span);
                TypedParam::new(p.name, var)
            })
            .collect::<Box<_>>();

        let (expr, set) = if typed_params.is_empty() {
            self.check(*bind.expr)?
        } else {
            let var_id = self.gen_id();
            let var = Ty::Var(var_id);
            self.insert_let(bind.name, var, [], bind.name.span);

            let (mut expr, set) = self.check(*bind.expr)?;

            for p in &mut typed_params {
                p.ty = self.get_var_ty(p.name).unwrap();
            }

            expr.ty = Ty::function_type(typed_params.iter().map(TypedParam::ty).cloned(), expr.ty);

            let subs = Subs::new(var_id, expr.ty.clone());

            expr.substitute_eq(&subs);
            (expr, set)
        };

        self.ctx.pop_scope();

        let ty = self.ctx.generalize(expr.ty.clone());

        Ok((ty, expr, typed_params, set))
    }

    fn check_let(
        &mut self,
        bind: UntypedLetBind,
        body: Option<UntypedExpr>,
        span: Span,
    ) -> IsaResult<(TypedExpr, Set)> {
        let name = bind.name;
        let name_span = bind.name.span;

        let (u1, expr, params, set) = self.check_let_bind(bind)?;

        let mut env1 = self.ctx.clone();
        std::mem::swap(&mut self.ctx, &mut env1);
        self.insert_let(name, u1, set.clone(), name_span);

        let (body, ty, set) = match body {
            Some(body) => {
                let (body, body_set) = self.check(body)?;
                std::mem::swap(&mut self.ctx, &mut env1);
                let ty = body.ty.clone();
                (Some(body), ty, set.concat(body_set))
            }
            None => (None, Ty::Unit, set),
        };

        let bind = TypedLetBind::new(name, params, Box::new(expr));

        let kind = TypedExprKind::Let {
            bind,
            body: body.map(Box::new),
        };

        Ok((TypedExpr::new(kind, span, ty), set))
    }

    fn check_constructor(
        constructor: UntypedConstructor,
        quant: Rc<[u64]>,
        mut ret: Ty,
    ) -> TypedConstructor {
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
        Constructor {
            name:   constructor.name,
            params: constructor.params,
            span:   constructor.span,
            ty:     ret,
        }
    }

    fn check_type_definition(
        &mut self,
        name: Ident,
        parameters: Box<[Ty]>,
        constructors: Box<[UntypedConstructor]>,
        span: Span,
    ) -> IsaResult<TypedExpr> {
        let mut quant = Vec::new();

        for param in &parameters {
            let new = param.as_var().unwrap();
            quant.push(new);
        }

        let quant = Rc::<[u64]>::from(quant);

        let ty = Ty::Named {
            name: self.ctx.new_path_from_current(name),
            args: parameters.clone().into(),
        };

        let mut typed_constructors = Vec::new();
        for c in constructors {
            let ctor = Self::check_constructor(c, quant.clone(), ty.clone());
            self.ctx.insert_constructor_for_ty(name, &quant, &ctor)?;
            typed_constructors.push(ctor);
        }

        let constructors = typed_constructors.into_boxed_slice();

        let kind = TypedExprKind::Type {
            name,
            parameters,
            constructors,
        };

        Ok(TypedExpr::new(kind, span, Ty::Unit))
    }

    fn check_val(&mut self, val: &mut ValDeclaration) {
        let mut subs = Vec::new();
        let mut quant = Vec::new();

        for param in &mut val.params {
            let id = self.gen_id();
            let mut new = Ty::Var(id);
            std::mem::swap(param, &mut new);
            let old = new.get_ident().unwrap();
            quant.push(id);
            subs.push((old, id));
        }

        if !subs.is_empty() {
            val.ty.substitute_param(&subs);
            val.set.substitute_param(&subs);
            val.ty = Ty::Scheme {
                quant: quant.into(),
                ty:    Rc::new(val.ty.clone()),
            };
        }
    }

    fn check_val_expr(&mut self, mut val: ValDeclaration, span: Span) -> TypedExpr {
        self.check_val(&mut val);

        self.insert_val(val.name, val.ty.clone(), val.set.clone(), val.span);

        let kind = TypedExprKind::Val(val);

        TypedExpr::new(kind, span, Ty::Unit)
    }

    fn check_constructor_pat(
        &mut self,
        name: Path,
        args: Box<[UntypedPat]>,
        span: Span,
    ) -> IsaResult<TypedPat> {
        let ctor = match (self.ctx.get_constructor(&name), name.segments.as_slice()) {
            (Ok(ctor), _) => ctor.clone(),
            (Err(_), [name]) if args.is_empty() => {
                let var = self.gen_type_var();
                self.insert_let(*name, var.clone(), [], span);
                return Ok(TypedPat::new(TypedPatKind::Ident(*name), span, var));
            }
            (Err(err), _) => {
                return Err(IsaError::from(err));
            }
        };

        let (mut ty, _) = self.instantiate(ctor);

        let mut c = EqConstraintSet::new();
        let mut typed_args = Vec::new();

        for arg in args {
            let arg = self.check_pat(arg)?;
            let Ty::Fn { param, ret } = &ty else {
                return Err(CheckError::new(CheckErrorKind::NotConstructor(ty), span).into());
            };
            c.push(EqConstraint::new(
                param.as_ref().clone(),
                arg.ty.clone(),
                arg.span,
            ));
            ty = ret.as_ref().clone();
            typed_args.push(arg);
        }

        if ty.is_fn() {
            return Err(CheckError::new(CheckErrorKind::Kind(ty), span).into());
        }

        let (subs, _) = self.unify(c, [])?;

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

    fn check_class_signatures(
        &mut self,
        name: Ident,
        signatures: &mut [ValDeclaration],
        defaults: &[UntypedLetBind],
    ) {
        for val in signatures.iter_mut() {
            self.check_val(val);
        }

        let val_signatures = signatures.iter().map(|val| {
            (
                val.name,
                MemberData {
                    has_default: defaults.iter().any(|bind| bind.name == val.name),
                    set:         val.set.clone(),
                    ty:          val.ty.clone(),
                    span:        val.span,
                },
            )
        });

        self.ctx
            .current_mut()
            .unwrap()
            .get_class_data_mut(name)
            .unwrap()
            .extend_signature(val_signatures);
    }

    fn check_class(
        &mut self,
        set: Set,
        name: Ident,
        instance: Ident,
        signatures: Box<[ValDeclaration]>,
        defaults: Box<[UntypedLetBind]>,
        span: Span,
    ) -> IsaResult<(TypedExpr, Set)> {
        let path = Path::from_ident(name);
        let data = self.ctx.get_class(&path).unwrap().instance_var();

        self.ctx.assume_constraint_tree(&Ty::Var(data), &set);

        let (defaults, def_set) =
            self.check_instance_impls(&path, Set::new(), defaults, |_| None)?;

        let kind = TypedExprKind::Class {
            set,
            name,
            instance,
            signatures,
            defaults: defaults.into_boxed_slice(),
        };

        Ok((TypedExpr::new(kind, span, Ty::Unit), def_set))
    }

    fn check_instance_impls<F>(
        &mut self,
        class: &Path,
        mut set: Set,
        impls: impl IntoIterator<Item = UntypedLetBind>,
        mut subs: F,
    ) -> IsaResult<(Vec<TypedLetBind>, Set)>
    where
        F: FnMut(&Ty) -> Option<Ty>,
    {
        set.substitute(&mut subs);
        let impls = impls
            .into_iter()
            .map(|bind| {
                let class_data = self.ctx.get_class(class).unwrap();
                let MemberData {
                    mut ty,
                    set: member_set,
                    span: ty_span,
                    ..
                } = class_data
                    .signatures()
                    .get(&bind.name)
                    .cloned()
                    .ok_or_else(|| {
                        let fst = DiagnosticLabel::new(
                            format!("`{}` is not a member o type class `{class}`", bind.name),
                            bind.name.span,
                        );
                        let snd =
                            DiagnosticLabel::new("type class declared here", class_data.span());
                        IsaError::new("not a member", fst, vec![snd])
                    })?;
                ty.substitute(&mut subs);
                let name = bind.name;
                let (_, expr, params, mut bind_set) =
                    self.check_let_bind_with_val(bind, &ty, member_set, ty_span)?;
                set.append(&mut bind_set);
                Ok(TypedLetBind::new(name, params, Box::new(expr)))
            })
            .collect::<IsaResult<_>>()?;
        Ok((impls, set))
    }

    fn check_instance(
        &mut self,
        params: Box<[Ty]>,
        set: Set,
        class: Path,
        instance: Ty,
        impls: Box<[UntypedLetBind]>,
        span: Span,
    ) -> IsaResult<(TypedExpr, Set)> {
        let class_data = self.ctx.get_class(&class)?;

        let scheme = self.ctx.generalize(instance.clone());
        for constr in class_data.constraints().iter() {
            if self.ctx.implementation(&scheme, constr.class()).is_err() {
                let fst = DiagnosticLabel::new(
                    format!("type `{scheme}` doesn't implement `{}`", constr.class()),
                    span,
                );
                let snd = DiagnosticLabel::new("declared here", class_data.span());

                return Err(IsaError::new("class mismatch", fst, vec![snd]));
            }
        }

        if let Some((
            not_implemented,
            MemberData {
                span: member_span, ..
            },
        )) = class_data
            .signatures()
            .iter()
            .find(|(name, data)| !data.has_default && !impls.iter().any(|bind| bind.name.eq(name)))
        {
            let fst = DiagnosticLabel::new(
                format!("member `{not_implemented}` of `{class}` not implemented"),
                span,
            );
            let snd = DiagnosticLabel::new("declared here", *member_span);

            return Err(IsaError::new("member not implemented", fst, vec![snd]));
        }

        let instance_var = class_data.instance_var();
        let mut arity_error = false;

        self.ctx.set_constraints(&class, scheme, set.clone());
        self.ctx.assume_constraints(&set);

        let (impls, set) = if let Ty::Named {
            name: ref instance_name,
            ref args,
        } = instance
        {
            let arity = self.ctx.get_type_arity(instance_name).unwrap();
            let var_args_len = arity - args.len();
            self.check_instance_impls(&class, set, impls, |ty| match ty {
                Ty::Generic {
                    var,
                    args: var_args,
                } if *var == instance_var => {
                    if var_args.len() == var_args_len {
                        let mut args = args.to_vec();
                        args.extend_from_slice(var_args);
                        Some(Ty::Named {
                            name: instance_name.clone(),
                            args: args.into(),
                        })
                    } else {
                        arity_error = true;
                        None
                    }
                }
                Ty::Var(var) if *var == instance_var => Some(instance.clone()),
                _ => None,
            })
        } else {
            self.check_instance_impls(&class, set, impls, |ty| match ty {
                Ty::Var(var) if *var == instance_var => Some(instance.clone()),
                _ => None,
            })
        }?;

        let kind = TypedExprKind::Instance {
            params,
            set: set.clone(),
            class,
            instance,
            impls: impls.into(),
        };

        Ok((TypedExpr::new(kind, span, Ty::Unit), set))
    }

    fn check_pat(&mut self, UntypedPat { kind, span, .. }: UntypedPat) -> IsaResult<TypedPat> {
        match kind {
            UntypedPatKind::Wild => {
                let var = self.gen_type_var();
                Ok(TypedPat::new(TypedPatKind::Wild, span, var))
            }
            UntypedPatKind::Or(spanneds) => {
                let mut patterns = Vec::new();
                let mut c = EqConstraintSet::new();

                let mut var = self.gen_type_var();
                for pat in spanneds {
                    let pat = self.check_pat(pat)?;
                    c.push(EqConstraint::new(pat.ty.clone(), var.clone(), pat.span));
                    patterns.push(pat);
                }

                let (subs, _) = self.unify(c, []).map_err(|err| {
                    IsaError::from(err).with_note("or sub-patterns should have same type")
                })?;

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
            UntypedPatKind::Int(i) => Ok(TypedPat::new(TypedPatKind::Int(i), span, Ty::Int)),
            UntypedPatKind::Bool(b) => Ok(TypedPat::new(TypedPatKind::Bool(b), span, Ty::Bool)),
            UntypedPatKind::Char(c) => Ok(TypedPat::new(TypedPatKind::Char(c), span, Ty::Char)),
            UntypedPatKind::Tuple(pats) => {
                if pats.is_empty() {
                    return Ok(TypedPat::new(
                        TypedPatKind::Tuple(Box::new([])),
                        span,
                        Ty::Unit,
                    ));
                }

                let mut typed_pats = Vec::new();
                let mut types = Vec::new();

                for pat in pats {
                    let pat = self.check_pat(pat)?;
                    types.push(pat.ty.clone());
                    typed_pats.push(pat);
                }

                let kind = TypedPatKind::Tuple(typed_pats.into_boxed_slice());
                let ty = Ty::Tuple(types.into());

                Ok(TypedPat::new(kind, span, ty))
            }
            UntypedPatKind::Constructor { name, args } => {
                self.check_constructor_pat(name, args, span)
            }

            UntypedPatKind::Ident(_) => {
                unreachable!("Parser never returns Ident pattern")
            }

            UntypedPatKind::IntRange(range) => {
                Ok(TypedPat::new(TypedPatKind::IntRange(range), span, Ty::Int))
            }

            UntypedPatKind::CharRange(range) => Ok(TypedPat::new(
                TypedPatKind::CharRange(range),
                span,
                Ty::Char,
            )),
        }
    }

    fn check_match_arm(
        &mut self,
        pat: UntypedPat,
        expr: UntypedExpr,
    ) -> IsaResult<(TypedPat, TypedExpr, Set)> {
        self.ctx.push_scope();

        let mut pat = self.check_pat(pat)?;

        let scope = self.ctx.current_scope().unwrap().clone();

        let (expr, set) = self.check(expr)?;

        let new_scope = self.ctx.pop_scope().unwrap();

        for (k, v) in scope {
            let Some(old) = v.ty().as_var() else {
                continue;
            };
            let new = new_scope.get(&k).unwrap().ty().clone();
            pat.substitute_eq(&Subs::new(old, new));
        }

        Ok((pat, expr, set))
    }

    fn check_match(
        &mut self,
        expr: UntypedExpr,
        arms: Box<[UntypedMatchArm]>,
        span: Span,
    ) -> IsaResult<(TypedExpr, Set)> {
        let (mut expr, mut set) = self.check(expr)?;

        let mut var = self.gen_type_var();
        let mut typed_arms = Vec::new();

        let mut c = EqConstraintSet::new();

        for arm in arms {
            let (pat, aexpr, mut arm_set) = self.check_match_arm(arm.pat, arm.expr)?;
            set.append(&mut arm_set);
            c.push(EqConstraint::new(var.clone(), aexpr.ty.clone(), aexpr.span));
            c.push(EqConstraint::new(expr.ty.clone(), pat.ty.clone(), pat.span));
            typed_arms.push(TypedMatchArm::new(pat, aexpr));
        }

        let (subs, set) = self.unify(c, set).map_err(|err| {
            let is_pat = typed_arms
                .iter()
                .find_map(|arm| {
                    if err.constr().span() == arm.pat().span {
                        Some(true)
                    } else if err.constr().span() == arm.expr().span {
                        Some(false)
                    } else {
                        None
                    }
                })
                .unwrap();

            let (snd, note) = if is_pat {
                let snd = DiagnosticLabel::new("expected due to this pattern", expr.span);
                (snd, "match patterns should have same type as scrutinee")
            } else {
                let snd = DiagnosticLabel::new(
                    "expected due to this",
                    typed_arms.first().unwrap().expr().span,
                );
                (snd, "match arms should have same type")
            };

            IsaError::from(err).with_label(snd).with_note(note)
        })?;

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

        Ok((TypedExpr::new(kind, span, var), set))
    }

    fn check_path_simple(
        module_name: Ident,
        ctx: &ModuleData,
        path: &[Ident],
        generator: &mut impl Generator,
        span: Span,
    ) -> IsaResult<(Path, Ty, Set)> {
        match path {
            [] => unreachable!(),
            &[id] => {
                let VarData {
                    ty, mut constrs, ..
                } = ctx.get_var(id)?.clone();
                let (ty, subs) = ty.instantiate(generator);
                constrs.substitute_many(&subs);

                Ok((Path::from_ident(id), ty, constrs))
            }
            &[first, id] => {
                todo!()
            }
            _ => Err(IsaError::from(CheckError::new(
                CheckErrorKind::InvalidPath(Path {
                    segments: path.into(),
                }),
                span,
            ))),
        }
    }

    fn check_path(
        ctx: &Ctx,
        path: &[Ident],
        generator: &mut impl Generator,
        span: Span,
    ) -> IsaResult<(Path, Ty, Set)> {
        match path {
            [] => unreachable!(),

            &[id] => {
                let VarData {
                    ty, mut constrs, ..
                } = ctx.get_var(id)?.clone();
                let (ty, subs) = ty.instantiate(generator);
                constrs.substitute_many(&subs);

                Ok((Path::from_ident(id), ty, constrs))
            }

            &[first, id] => {
                let path = Path {
                    segments: smallvec![first, id],
                };

                if let Ok(ty) = ctx.get_constructor(&path) {
                    let (ty, _) = ty.clone().instantiate(generator);
                    return Ok((path, ty, Set::new()));
                }

                if let Ok((ty, set)) = ctx.get_class(&Path::from_ident(first)).and_then(|data| {
                    Self::check_class_member(Path::from_ident(first), data, id, generator, span)
                }) {
                    return Ok((path, ty, set));
                }

                let module = ctx.get_module(first)?;

                Self::check_path_simple(first, module, &[id], generator, span)
            }

            &[first, ref rest @ ..] => {
                todo!()
            }
        }
    }

    fn check_bin(
        &mut self,
        op: BinOp,
        lhs: UntypedExpr,
        rhs: UntypedExpr,
        span: Span,
    ) -> IsaResult<(TypedExpr, Set)> {
        if op.is_pipe() {
            return self.check_call(rhs, lhs, span);
        }

        let (mut lhs, lhs_set) = self.check(lhs)?;
        let (mut rhs, rhs_set) = self.check(rhs)?;

        let mut set = lhs_set.concat(rhs_set);

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                let c = EqConstraint::new(lhs.ty.clone(), rhs.ty.clone(), rhs.span);

                set.push(ClassConstraint::new(
                    Path::from_ident(Ident {
                        ident: global::intern_symbol(op.class()),
                        span,
                    }),
                    lhs.ty.clone(),
                    span,
                ));
                let (subs, set) = self.unify(c, set)?;
                lhs.substitute_many(&subs);
                rhs.substitute_many(&subs);

                let ty = lhs.ty.clone();

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok((TypedExpr::new(kind, span, ty), set))
            }

            BinOp::Gt
            | BinOp::Ge
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Eq
            | BinOp::Ne
            | BinOp::And
            | BinOp::Or => {
                let c = EqConstraint::new(lhs.ty.clone(), rhs.ty.clone(), rhs.span);

                set.push(ClassConstraint::new(
                    Path::from_ident(Ident {
                        ident: global::intern_symbol(op.class()),
                        span,
                    }),
                    lhs.ty.clone(),
                    span,
                ));
                let (subs, set) = self.unify(c, set)?;

                lhs.substitute_many(&subs);
                rhs.substitute_many(&subs);

                let kind = TypedExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok((TypedExpr::new(kind, span, Ty::Bool), set))
            }

            BinOp::Pipe => unreachable!(),
        }
    }

    fn check_un(&mut self, op: UnOp, expr: UntypedExpr, span: Span) -> IsaResult<(TypedExpr, Set)> {
        let (mut expr, mut set) = self.check(expr)?;

        let class = match op {
            UnOp::Not => global::intern_symbol("Not"),
            UnOp::Neg => global::intern_symbol("Neg"),
        };
        let class = Ident { ident: class, span };
        let class = Path::from_ident(class);
        let constr = ClassConstraint::new(class, expr.ty.clone(), expr.span);
        set.push(constr);

        let (subs, set) = self.unify([], set)?;

        expr.substitute_many(&subs);
        let ty = expr.ty.clone();

        let kind = TypedExprKind::Un {
            op,
            expr: Box::new(expr),
        };

        Ok((TypedExpr::new(kind, span, ty), set))
    }

    fn check_tuple(
        &mut self,
        exprs: Box<[UntypedExpr]>,
        span: Span,
    ) -> IsaResult<(TypedExpr, Set)> {
        if exprs.is_empty() {
            return Ok((
                TypedExpr::new(TypedExprKind::Tuple(Box::new([])), span, Ty::Unit),
                Set::new(),
            ));
        }

        let mut typed_exprs = Vec::new();
        let mut types = Vec::new();

        let mut set = Set::new();

        for expr in exprs {
            let (expr, mut expr_set) = self.check(expr)?;
            set.append(&mut expr_set);
            types.push(expr.ty.clone());
            typed_exprs.push(expr);
        }

        let kind = TypedExprKind::Tuple(typed_exprs.into_boxed_slice());
        let ty = Ty::Tuple(types.into());

        Ok((TypedExpr::new(kind, span, ty), set))
    }

    fn instantiate(&mut self, ty: Ty) -> (Ty, Vec<Subs>) {
        ty.instantiate(&mut self.generator)
    }

    fn check_module_types(
        &mut self,
        module: &mut UntypedModule,
    ) -> IsaResult<Vec<(Ident, AliasData)>> {
        let _ = self.ctx.create_module(module.name);
        let module_name = module.name;
        let mut declared = FxHashMap::default();
        for expr in &mut module.exprs {
            self.check_type_declaration(expr, &mut declared)?;
        }

        for expr in &mut module.exprs {
            expr.substitute(&mut |ty| match ty {
                Ty::Named { name, args } => name.as_ident().map(|name| Ty::Named {
                    name: Path {
                        segments: smallvec![module_name, name],
                    },
                    args: args.clone(),
                }),
                _ => None,
            });
        }

        if declared.is_empty() {
            return Ok(Vec::new());
        }

        Ok(module
            .exprs
            .iter()
            .filter_map(Self::check_alias_declaration)
            .collect())
    }

    fn check_type_declaration(
        &mut self,
        expr: &mut UntypedExpr,
        declared: &mut FxHashMap<Ident, Span>,
    ) -> IsaResult<()> {
        if let Some((name, span)) = match &mut expr.kind {
            UntypedExprKind::Semi(e) => return self.check_type_declaration(e, declared),
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
                    let old = new.get_ident().unwrap();
                    subs.push((old, id));
                }

                for ctor in constructors {
                    ctor.substitute_param(&subs);
                }

                Some((*name, expr.span))
            }

            UntypedExprKind::Alias {
                name,
                parameters,
                ty,
            } => {
                let mut subs = Vec::new();

                for param in parameters {
                    let id = self.gen_id();
                    let mut new = Ty::Var(id);
                    std::mem::swap(param, &mut new);
                    let old = new.get_ident().unwrap();
                    subs.push((old, id));
                }

                ty.substitute_param(&subs);

                Some((*name, expr.span))
            }

            UntypedExprKind::Class {
                set,
                name,
                instance,
                signatures,
                ..
            } => {
                let var = self.gen_id();
                let mut subs = |ty: &Ty| match ty {
                    Ty::Named { name, args } if name.is_ident(*instance) => {
                        if args.is_empty() {
                            Some(Ty::Var(var))
                        } else {
                            Some(Ty::Generic {
                                var,
                                args: args.clone(),
                            })
                        }
                    }
                    _ => None,
                };
                set.substitute(&mut subs);
                for sig in signatures {
                    sig.substitute(&mut subs);
                }

                let class = ClassData::new(set.clone(), var, expr.span);
                let _ = self.ctx.insert_class(*name, class);
                let _ = self.ctx.insert_instance_at_env(
                    Ty::Var(var),
                    *name,
                    InstanceData::new(Set::new(), expr.span),
                );
                self.ctx.assume_constraints(set);

                Some((*name, expr.span))
            }

            UntypedExprKind::Instance {
                params,
                set,
                instance,
                ..
            } => {
                let mut subs = Vec::new();

                for param in params {
                    let id = self.gen_id();
                    let mut new = Ty::Var(id);
                    std::mem::swap(param, &mut new);
                    let old = new.get_ident().unwrap();
                    subs.push((old, id));
                }

                set.substitute_param(&subs);
                instance.substitute_param(&subs);

                None
            }

            _ => None,
        } {
            if let Some(previous) = declared.insert(name, span) {
                let fst = DiagnosticLabel::new(format!("multiple definitons of `{name}`"), span);
                let snd = DiagnosticLabel::new("previously defined here", previous);
                return Err(IsaError::new("multiple definitons", fst, vec![snd]));
            }
        }

        Ok(())
    }

    fn check_alias_declaration(expr: &UntypedExpr) -> Option<(Ident, AliasData)> {
        match &expr.kind {
            UntypedExprKind::Semi(e) => Self::check_alias_declaration(e),
            UntypedExprKind::Alias {
                name,
                parameters,
                ty,
            } => {
                let mut vars = Vec::new();

                for param in parameters {
                    let id = param.as_var().unwrap();
                    vars.push(id);
                }

                Some((*name, AliasData::new(vars.into(), ty.clone())))
            }

            _ => None,
        }
    }

    fn check_class_member(
        class: Path,
        data: &ClassData,
        member: Ident,
        generator: &mut impl Generator,
        span: Span,
    ) -> CheckResult<(Ty, Set)> {
        let instance_var = data.instance_var();
        let mut constraints = data.constraints().clone();
        let MemberData {
            ty: sig,
            set: mut member_set,
            ..
        } = data
            .signatures()
            .get(&member)
            .cloned()
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(member.ident), span))?;

        for c in &mut member_set.constrs {
            *c.span_mut() = span;
        }

        let (mut sig, sig_subs) = sig.instantiate(generator);
        let new_var = generator.gen_id();
        let mut subs = |ty: &Ty| match ty {
            Ty::Generic { var, args } if *var == instance_var => Some(Ty::Generic {
                var:  new_var,
                args: args.clone(),
            }),
            Ty::Var(var) if *var == instance_var => Some(Ty::Var(new_var)),
            _ => None,
        };

        constraints.append(&mut member_set);

        constraints.substitute(&mut subs);
        constraints.substitute_many(&sig_subs);
        sig.substitute(&mut subs);
        sig.substitute_many(&sig_subs);

        constraints.push(ClassConstraint::new(class, Ty::Var(new_var), span));

        Ok((sig, constraints))
    }

    fn check_expr_for_class_signatures(&mut self, expr: &mut UntypedExpr) -> IsaResult<()> {
        match &mut expr.kind {
            UntypedExprKind::Class {
                name,
                signatures,
                defaults,
                ..
            } => {
                self.check_class_signatures(*name, signatures, defaults);
                Ok(())
            }
            UntypedExprKind::Instance {
                set,
                class,
                instance,
                ..
            } => {
                let data = InstanceData::new(set.clone(), expr.span);
                let instance = self.ctx.generalize(instance.clone());
                self.ctx.insert_instance(instance, class, data)?;
                Ok(())
            }
            UntypedExprKind::Semi(expr) => self.check_expr_for_class_signatures(expr),
            _ => Ok(()),
        }
    }

    pub fn check_many_modules(
        &mut self,
        mut modules: Vec<UntypedModule>,
    ) -> IsaResult<(Vec<TypedModule>, Set)> {
        let mut aliases = FxHashMap::default();

        for types in modules
            .iter_mut()
            .map(|module| self.check_module_types(module))
        {
            aliases.extend(types?);
        }

        let mut decl = Vec::new();
        let mut set = Set::new();

        for module in &mut modules {
            if !aliases.is_empty() {
                module.substitute(&mut |ty| {
                    let Ty::Named { name, args } = ty else {
                        return None;
                    };
                    let name = name.as_ident()?;

                    aliases.get(&name).map(|alias| alias.subs(args))
                });
            }
            self.ctx.set_current_module(module.name);

            self.ctx.push_scope();

            for expr in &mut module.exprs {
                self.check_expr_for_class_signatures(expr)?;
            }

            let mut exprs = Vec::new();

            for res in module
                .exprs
                .extract_if(.., |e| e.kind.is_type_or_val())
                .map(|e| self.check(e))
            {
                let (expr, mut expr_set) = res?;
                exprs.push(expr);
                set.append(&mut expr_set);
            }

            let scope = self.ctx.pop_scope().unwrap();
            self.ctx.extend_module(module.name, scope);

            decl.push(exprs);
        }

        // for c in set.iter() {
        //     println!("{} {:?}", c.class(), c.constrained());
        // }

        let modules = modules
            .into_iter()
            .zip(decl)
            .map(|(module, mut decl)| {
                let (mut module, mut module_set) = self.check_module(module)?;
                decl.append(&mut module.exprs);
                module.exprs = decl;
                set.append(&mut module_set);
                Ok(module)
            })
            .collect::<IsaResult<_>>()?;

        Ok((modules, set))
    }

    fn check_module(&mut self, module: UntypedModule) -> IsaResult<(TypedModule, Set)> {
        self.ctx.push_scope();

        self.ctx.set_current_module(module.name);

        let mut exprs = Vec::new();
        let mut set = Set::new();

        for res in module.exprs.into_iter().map(|expr| self.check(expr)) {
            let (expr, mut expr_set) = res?;
            exprs.push(expr);
            set.append(&mut expr_set);
        }
        let scope = self.ctx.pop_scope().unwrap();
        self.ctx.extend_module(module.name, scope);
        let typed = TypedModule::new(module.name, module.imports, exprs, module.span);

        Ok((typed, set))
    }

    fn check(&mut self, expr: UntypedExpr) -> IsaResult<(TypedExpr, Set)> {
        let span = expr.span;
        match expr.kind {
            UntypedExprKind::Int(i) => Ok((
                TypedExpr::new(TypedExprKind::Int(i), span, Ty::Int),
                Set::new(),
            )),

            UntypedExprKind::Bool(b) => Ok((
                TypedExpr::new(TypedExprKind::Bool(b), span, Ty::Bool),
                Set::new(),
            )),

            UntypedExprKind::Char(c) => Ok((
                TypedExpr::new(TypedExprKind::Char(c), span, Ty::Char),
                Set::new(),
            )),

            UntypedExprKind::Path(path) => {
                let (path, ty, set) =
                    Self::check_path(&self.ctx, &path.segments, &mut self.generator, span)?;
                Ok((TypedExpr::new(TypedExprKind::Path(path), span, ty), set))
            }

            UntypedExprKind::Tuple(exprs) => self.check_tuple(exprs, span),

            UntypedExprKind::Bin { op, lhs, rhs } => self.check_bin(op, *lhs, *rhs, span),

            UntypedExprKind::Un { op, expr } => self.check_un(op, *expr, span),

            UntypedExprKind::If {
                cond,
                then,
                otherwise,
            } => self.check_if(*cond, *then, *otherwise, span),

            UntypedExprKind::Fn { param, expr } => self.check_fn(param, *expr, span),

            UntypedExprKind::Call { callee, arg } => self.check_call(*callee, *arg, span),

            UntypedExprKind::Let { bind, body } => {
                self.check_let(bind, body.map(|body| *body), span)
            }

            UntypedExprKind::Semi(expr) => {
                let (mut expr, constr) = self.check(*expr)?;
                expr.ty = Ty::Unit;
                Ok((expr, constr))
            }

            UntypedExprKind::Type {
                name,
                parameters,
                constructors,
            } => Ok((
                self.check_type_definition(name, parameters, constructors, span)?,
                Set::new(),
            )),

            UntypedExprKind::Alias {
                name,
                parameters,
                ty,
            } => Ok((
                TypedExpr::new(
                    TypedExprKind::Alias {
                        name,
                        parameters,
                        ty,
                    },
                    span,
                    Ty::Unit,
                ),
                Set::new(),
            )),

            UntypedExprKind::Val(val) => Ok((self.check_val_expr(val, span), Set::new())),

            UntypedExprKind::Match { expr, arms } => self.check_match(*expr, arms, span),

            UntypedExprKind::Class {
                set,
                name,
                instance,
                signatures,
                defaults,
            } => self.check_class(set, name, instance, signatures, defaults, span),

            UntypedExprKind::Instance {
                params,
                set,
                class: name,
                instance,
                impls,
            } => self.check_instance(params, set, name, instance, impls, span),
        }
    }
}
