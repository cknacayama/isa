use std::rc::Rc;

use rustc_hash::FxHashMap;
use smallvec::smallvec;

use super::ast::{
    Constructor, Expr, ExprKind, LetBind, ListPat, MatchArm, Module, OpDeclaration, Param, Pat,
    PatKind, Path, Stmt, StmtKind, UntypedConstructor, UntypedExpr, UntypedLetBind,
    UntypedMatchArm, UntypedModule, UntypedParam, UntypedPat, UntypedStmt, ValDeclaration,
};
use super::ctx::{
    AliasData, ClassData, Ctx, Generator, IdGenerator, InstanceData, MemberData, VarData,
};
use super::error::{
    CheckError, CheckErrorKind, CheckResult, DiagnosticLabel, IsaError, Uninferable,
};
use super::infer::{
    ClassConstraint, ClassConstraintSet as Set, Constraint, EqConstraint, EqConstraintSet, Subs,
    Substitute,
};
use super::token::Ident;
use super::types::Ty;
use crate::compiler::ctx::OperatorData;
use crate::global::Symbol;
use crate::span::Span;

#[derive(Debug, Default)]
pub struct Checker {
    ctx:       Ctx,
    subs:      Vec<Subs>,
    generator: IdGenerator,
}

pub type IsaResult<T> = Result<T, IsaError>;

impl Checker {
    fn unify<EqSet, ClassSet>(
        &mut self,
        constr: EqSet,
        classes: ClassSet,
    ) -> Result<(Vec<Subs>, Set), Uninferable>
    where
        EqConstraintSet: From<EqSet>,
        Set: From<ClassSet>,
    {
        self.ctx
            .unify(EqConstraintSet::from(constr), Set::from(classes))
            .inspect(|(subs, _)| self.subs.extend_from_slice(subs))
    }

    #[must_use]
    pub const fn ctx(&self) -> &Ctx {
        &self.ctx
    }

    const fn subs_count(&self) -> usize {
        self.subs.len()
    }

    fn subs_from(&self, pos: usize) -> &[Subs] {
        &self.subs[pos..]
    }

    fn insert_val<ClassSet>(
        &mut self,
        id: Symbol,
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

    fn insert_let<ClassSet>(&mut self, id: Ident, ty: Ty, set: ClassSet) -> Option<VarData>
    where
        Set: From<ClassSet>,
    {
        self.ctx
            .insert_var(id.ident, VarData::new(ty, Set::from(set), id.span))
    }

    fn gen_id(&mut self) -> u64 {
        self.generator.gen_id()
    }

    fn gen_type_var(&mut self) -> Ty {
        self.generator.gen_type_var()
    }

    fn check_valid_type(&self, ty: &Ty) -> IsaResult<()> {
        match ty {
            Ty::Generic { args, .. } | Ty::Tuple(args) => {
                args.iter().try_for_each(|ty| self.check_valid_type(ty))
            }
            Ty::Fn { param, ret } => {
                self.check_valid_type(param)?;
                self.check_valid_type(ret)
            }
            Ty::Scheme { ty, .. } => self.check_valid_type(ty),
            Ty::Named { name, args } => {
                self.ctx.get_ty_data(name)?;
                args.iter().try_for_each(|ty| self.check_valid_type(ty))
            }

            Ty::Unit | Ty::Int | Ty::Bool | Ty::Char | Ty::Var(_) => Ok(()),
        }
    }

    fn check_if(
        &mut self,
        cond: UntypedExpr,
        then: UntypedExpr,
        otherwise: UntypedExpr,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
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

        let kind = ExprKind::If {
            cond:      Box::new(cond),
            then:      Box::new(then),
            otherwise: Box::new(otherwise),
        };

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_fn(
        &mut self,
        param: UntypedParam,
        expr: UntypedExpr,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        self.ctx.push_scope();

        let mut pat = self.check_pat(param.pat)?;
        let pos = self.subs_count();

        let (expr, set) = self.check(expr)?;
        pat.ty.substitute_many(self.subs_from(pos));

        self.ctx.pop_scope();

        let ty = Ty::Fn {
            param: Rc::new(pat.ty.clone()),
            ret:   Rc::new(expr.ty.clone()),
        };

        let kind = ExprKind::Fn {
            param: Param::new(pat),
            expr:  Box::new(expr),
        };

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_call(
        &mut self,
        callee: UntypedExpr,
        arg: UntypedExpr,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
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

        let kind = ExprKind::Call {
            callee: Box::new(callee),
            arg:    Box::new(arg),
        };

        Ok((Expr::new(kind, span, var), set))
    }

    fn check_let_bind_with_val(
        &mut self,
        bind: UntypedLetBind,
        val_decl: &Ty,
        val_set: Set,
        ty_span: Span,
    ) -> IsaResult<(Ty, Expr<Ty>, Box<[Param<Ty>]>, Set)> {
        self.ctx.push_scope();

        let mut param_iter = val_decl.param_iter();

        let mut typed_params = bind
            .params
            .into_iter()
            .map(|p| {
                let decl = param_iter.next().ok_or_else(|| {
                    let fst =
                        DiagnosticLabel::new(format!("expected `{val_decl}`"), bind.name.span);
                    let snd = DiagnosticLabel::new("more parameters than expected", p.pat.span);
                    let trd = DiagnosticLabel::new("expected due to this", ty_span);

                    IsaError::new("type mismatch", fst, vec![snd, trd])
                        .with_note("let bind should have same type as val declaration")
                })?;
                let mut pat = self.check_pat(p.pat)?;
                let c = EqConstraint::new(decl, pat.ty.clone(), pat.span);
                let (subs, _) = self.unify(c, [])?;
                pat.ty.substitute_many(&subs);

                Ok(Param::new(pat))
            })
            .collect::<IsaResult<Box<_>>>()?;

        let (mut expr, set) = if typed_params.is_empty() {
            self.check(bind.expr)?
        } else {
            let pos = self.subs_count();
            self.ctx.assume_constraints(&val_set);
            let (mut expr, set) = self.check(bind.expr)?;

            let subs = self.subs_from(pos);
            for p in &mut typed_params {
                p.pat.ty.substitute_many(subs);
            }

            expr.ty = Ty::function(typed_params.iter().map(|p| p.pat.ty.clone()), expr.ty);
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

        let (subs, set) = self
            .unify(constr, set)
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
            p.pat.ty.substitute_many(&subs);
        }

        let ty = self.ctx.generalize(expr.ty.clone());

        Ok((ty, expr, typed_params, val_set))
    }

    fn check_let_bind(
        &mut self,
        bind: UntypedLetBind,
    ) -> IsaResult<(Ty, Expr<Ty>, Box<[Param<Ty>]>, Set)> {
        if self.ctx.current_depth() == 1
            && let Ok(val) = self.ctx.current()?.get_val(bind.name)
        {
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
                let pat = self.check_pat(p.pat)?;
                Ok(Param::new(pat))
            })
            .collect::<IsaResult<Box<_>>>()?;

        let (expr, set) = if typed_params.is_empty() {
            self.check(bind.expr)?
        } else {
            let pos = self.subs_count();
            let var_id = self.gen_id();
            let var = Ty::Var(var_id);
            self.insert_let(bind.name, var, []);

            let (mut expr, set) = self.check(bind.expr)?;

            let subs = self.subs_from(pos);
            for p in &mut typed_params {
                p.pat.ty.substitute_many(subs);
            }

            expr.ty = Ty::function(typed_params.iter().map(|p| p.pat.ty.clone()), expr.ty);

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
    ) -> IsaResult<(Expr<Ty>, Set)> {
        let name = bind.name;

        let (u1, expr, params, set) = self.check_let_bind(bind)?;

        let (body, ty, set) = if let Some(body) = body {
            self.ctx.push_scope();
            self.insert_let(name, u1, set.clone());
            let (body, body_set) = self.check(body)?;
            self.ctx.pop_scope();
            let ty = body.ty.clone();
            (Some(body), ty, set.concat(body_set))
        } else {
            self.insert_let(name, u1, set.clone());
            (None, Ty::Unit, set)
        };

        let bind = LetBind::new(name, params, expr);

        let kind = ExprKind::Let {
            bind: Box::new(bind),
            body: body.map(Box::new),
        };

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_constructor(
        &self,
        constructor: UntypedConstructor,
        quant: Rc<[u64]>,
        mut ret: Ty,
    ) -> IsaResult<Constructor<Ty>> {
        for param in constructor.params.iter().rev() {
            ret = Ty::Fn {
                param: Rc::new(param.clone()),
                ret:   Rc::new(ret),
            };
        }
        self.check_valid_type(&ret)?;
        if !quant.is_empty() {
            ret = Ty::Scheme {
                quant,
                ty: Rc::new(ret),
            };
        }
        Ok(Constructor {
            name:   constructor.name,
            params: constructor.params,
            span:   constructor.span,
            ty:     ret,
        })
    }

    fn check_type_definition(
        &mut self,
        name: Ident,
        parameters: Box<[Ty]>,
        constructors: Box<[UntypedConstructor]>,
        span: Span,
    ) -> IsaResult<Stmt<Ty>> {
        let quant = parameters
            .iter()
            .map(|p| p.as_var().unwrap())
            .collect::<Rc<_>>();

        let module = Ident::new(self.ctx.current_module().ident, name.span);
        let ty = Ty::Named {
            name: Path::new(smallvec![module, name]),
            args: parameters.clone().into(),
        };

        let constructors = constructors
            .into_iter()
            .map(|c| {
                let ctor = self.check_constructor(c, quant.clone(), ty.clone())?;
                self.ctx.insert_constructor_for_ty(name, &ctor)?;
                Ok(ctor)
            })
            .collect::<IsaResult<_>>()?;

        let kind = StmtKind::Type {
            name,
            parameters,
            constructors,
        };

        Ok(Stmt::new(kind, span))
    }

    fn check_operator(
        &mut self,
        params: Box<[Ty]>,
        set: Set,
        ops: Box<[OpDeclaration]>,
        span: Span,
    ) -> IsaResult<Stmt<Ty>> {
        let quant = params
            .iter()
            .map(|p| p.as_var().unwrap())
            .collect::<Rc<_>>();

        let ops = ops
            .into_iter()
            .map(|OpDeclaration { prefix, op, ty }| {
                let ty = Ty::Scheme {
                    quant: quant.clone(),
                    ty:    Rc::new(ty),
                };
                let data = OperatorData::new(ty.clone(), set.clone());
                if prefix {
                    self.ctx.insert_prefix(op, data);
                } else {
                    self.ctx.insert_infix(op, data);
                }
                OpDeclaration::new(prefix, op, ty)
            })
            .collect();

        let kind = StmtKind::Operator { params, set, ops };

        Ok(Stmt::new(kind, span))
    }

    fn check_val(&self, val: &mut ValDeclaration) -> IsaResult<()> {
        let quant = val
            .params
            .iter()
            .map(|p| p.as_var().unwrap())
            .collect::<Rc<_>>();

        if !quant.is_empty() {
            val.ty = Ty::Scheme {
                quant,
                ty: Rc::new(val.ty.clone()),
            };
        }

        self.check_valid_type(&val.ty)
    }

    fn check_val_stmt(&mut self, mut val: ValDeclaration, span: Span) -> IsaResult<Stmt<Ty>> {
        self.check_val(&mut val)?;

        self.insert_val(val.name.ident, val.ty.clone(), val.set.clone(), val.span);

        let kind = StmtKind::Val(val);

        Ok(Stmt::new(kind, span))
    }

    fn check_constructor_pat(
        &mut self,
        name: Path,
        args: Box<[UntypedPat]>,
        span: Span,
    ) -> IsaResult<Pat<Ty>> {
        let ctor = match (self.ctx.get_constructor(&name), name.segments.as_slice()) {
            (Ok(ctor), _) => ctor.clone(),
            (Err(_), [name]) if args.is_empty() => {
                let var = self.gen_type_var();
                self.insert_let(*name, var.clone(), []);
                return Ok(Pat::new(PatKind::Ident(*name), span, var));
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

        let kind = PatKind::Constructor {
            name,
            args: typed_args.into_boxed_slice(),
        };

        Ok(Pat::new(kind, span, ty))
    }

    fn check_class_signatures(
        &mut self,
        name: Ident,
        signatures: &mut [ValDeclaration],
        defaults: &[UntypedLetBind],
    ) -> IsaResult<()> {
        for val in signatures.iter_mut() {
            self.check_val(val)?;
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

        Ok(())
    }

    fn check_class(
        &mut self,
        set: Set,
        name: Ident,
        instance: Ident,
        signatures: Box<[ValDeclaration]>,
        defaults: Box<[UntypedLetBind]>,
        span: Span,
    ) -> IsaResult<(Stmt<Ty>, Set)> {
        let path = Path::from_ident(name);
        let data = self.ctx.get_class(&path).unwrap().instance_var();

        self.ctx.assume_constraint_tree(&Ty::Var(data), &set);

        let (defaults, def_set) =
            self.check_instance_impls(&path, Set::new(), defaults, |_| None)?;

        let kind = StmtKind::Class {
            set,
            name,
            instance,
            signatures,
            defaults: defaults.into_boxed_slice(),
        };

        Ok((Stmt::new(kind, span), def_set))
    }

    fn check_instance_impls<F>(
        &mut self,
        class: &Path,
        mut set: Set,
        impls: impl IntoIterator<Item = UntypedLetBind>,
        mut subs: F,
    ) -> IsaResult<(Vec<LetBind<Ty>>, Set)>
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
                let (_, expr, params, bind_set) =
                    self.check_let_bind_with_val(bind, &ty, member_set, ty_span)?;
                set.extend(bind_set);
                Ok(LetBind::new(name, params, expr))
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
    ) -> IsaResult<(Stmt<Ty>, Set)> {
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

        let kind = StmtKind::Instance {
            params,
            set: set.clone(),
            class,
            instance,
            impls: impls.into(),
        };

        Ok((Stmt::new(kind, span), set))
    }

    fn check_list_pat(&mut self, list: ListPat<()>, span: Span) -> IsaResult<Pat<Ty>> {
        match list {
            ListPat::Nil => {
                let ty = Ty::list(self.gen_type_var());
                Ok(Pat::new(PatKind::List(ListPat::Nil), span, ty))
            }
            ListPat::Single(pat) => {
                let pat = self.check_pat(*pat)?;
                let ty = Ty::list(pat.ty.clone());
                let kind = PatKind::List(ListPat::Single(Box::new(pat)));
                Ok(Pat::new(kind, span, ty))
            }
            ListPat::Cons(pat, pat1) => {
                let pat = self.check_pat(*pat)?;
                let pat1 = self.check_pat(*pat1)?;
                if !pat1.kind.is_rest_pat() {
                    let fst = DiagnosticLabel::new("expected rest pattern", pat1.span);
                    let note = "rest pattern should be of form _, identifier or list pattern";
                    return Err(IsaError::new("pattern error", fst, Vec::new()).with_note(note));
                }
                let mut ty = Ty::list(pat.ty.clone());
                let c = EqConstraint::new(ty.clone(), pat1.ty.clone(), span);
                let (subs, _) = self.unify(c, [])?;
                ty.substitute_many(&subs);
                let kind = PatKind::List(ListPat::Cons(Box::new(pat), Box::new(pat1)));

                Ok(Pat::new(kind, span, ty))
            }
        }
    }

    fn check_pat(&mut self, UntypedPat { kind, span, .. }: UntypedPat) -> IsaResult<Pat<Ty>> {
        match kind {
            PatKind::Wild => {
                let var = self.gen_type_var();
                Ok(Pat::new(PatKind::Wild, span, var))
            }
            PatKind::Or(spanneds) => {
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

                Ok(Pat::new(
                    PatKind::Or(patterns.into_boxed_slice()),
                    span,
                    var,
                ))
            }
            PatKind::List(list) => self.check_list_pat(list, span),
            PatKind::Int(i) => Ok(Pat::new(PatKind::Int(i), span, Ty::Int)),
            PatKind::Bool(b) => Ok(Pat::new(PatKind::Bool(b), span, Ty::Bool)),
            PatKind::Char(c) => Ok(Pat::new(PatKind::Char(c), span, Ty::Char)),
            PatKind::Tuple(pats) => {
                if pats.is_empty() {
                    return Ok(Pat::new(PatKind::Tuple(Box::new([])), span, Ty::Unit));
                }

                let mut typed_pats = Vec::new();
                let mut types = Vec::new();

                for pat in pats {
                    let pat = self.check_pat(pat)?;
                    types.push(pat.ty.clone());
                    typed_pats.push(pat);
                }

                let kind = PatKind::Tuple(typed_pats.into_boxed_slice());
                let ty = Ty::Tuple(types.into());

                Ok(Pat::new(kind, span, ty))
            }
            PatKind::Constructor { name, args } => self.check_constructor_pat(name, args, span),

            PatKind::Ident(_) => {
                unreachable!("Parser never returns Ident pattern")
            }

            PatKind::IntRange(range) => Ok(Pat::new(PatKind::IntRange(range), span, Ty::Int)),

            PatKind::CharRange(range) => Ok(Pat::new(PatKind::CharRange(range), span, Ty::Char)),
        }
    }

    fn check_match_arm(
        &mut self,
        pat: UntypedPat,
        expr: UntypedExpr,
    ) -> IsaResult<(Pat<Ty>, Expr<Ty>, Set)> {
        self.ctx.push_scope();

        let mut pat = self.check_pat(pat)?;

        let count = self.subs_count();

        let (expr, set) = self.check(expr)?;

        pat.ty.substitute_many(self.subs_from(count));

        self.ctx.pop_scope();

        Ok((pat, expr, set))
    }

    fn check_match(
        &mut self,
        expr: UntypedExpr,
        arms: Box<[UntypedMatchArm]>,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        let (mut expr, mut set) = self.check(expr)?;

        let mut var = self.gen_type_var();
        let mut typed_arms = Vec::new();

        let mut c = EqConstraintSet::new();

        for arm in arms {
            let (pat, aexpr, arm_set) = self.check_match_arm(arm.pat, arm.expr)?;
            set.extend(arm_set);
            c.push(EqConstraint::new(var.clone(), aexpr.ty.clone(), aexpr.span));
            c.push(EqConstraint::new(expr.ty.clone(), pat.ty.clone(), pat.span));
            typed_arms.push(MatchArm::new(pat, aexpr));
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

        let kind = ExprKind::Match {
            expr: Box::new(expr),
            arms: typed_arms.into_boxed_slice(),
        };

        Ok((Expr::new(kind, span, var), set))
    }

    fn check_path(
        ctx: &Ctx,
        generator: &mut impl Generator,
        path: Path,
        span: Span,
    ) -> IsaResult<(Path, Ty, Set)> {
        match path.segments.as_slice() {
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

                let VarData {
                    ty, mut constrs, ..
                } = module.get_var(id)?.clone();

                let (ty, subs) = ty.instantiate(generator);
                constrs.substitute_many(&subs);

                Ok((Path::from_ident(id), ty, constrs))
            }

            &[fst, snd, trd] => {
                if let Ok(ty) = ctx.get_constructor(&path) {
                    let (ty, _) = ty.clone().instantiate(generator);
                    return Ok((path, ty, Set::new()));
                }

                let class_path = Path {
                    segments: smallvec![fst, snd],
                };

                let data = ctx.get_class(&class_path)?;

                let (ty, set) = Self::check_class_member(class_path, data, trd, generator, span)?;

                Ok((path, ty, set))
            }

            _ => Err(IsaError::from(CheckError::new(
                CheckErrorKind::InvalidPath(path),
                span,
            ))),
        }
    }

    fn check_operator_expr(&mut self, op: Ident, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        let data = self
            .ctx
            .get_infix(op)
            .or_else(|_| self.ctx.get_prefix(op))?;
        let mut set = data.set().clone();
        for c in &mut set.constrs {
            *c.span_mut() = span;
        }
        let (ty, subs) = self.instantiate(data.ty().clone());
        set.substitute_many(&subs);

        let kind = ExprKind::Operator(op);

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_bin(
        &mut self,
        op: Ident,
        lhs: UntypedExpr,
        rhs: UntypedExpr,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        let (lhs, lhs_set) = self.check(lhs)?;
        let (rhs, rhs_set) = self.check(rhs)?;

        let data = self.ctx.get_infix(op)?;
        let mut set = data.set().clone();
        for c in &mut set.constrs {
            *c.span_mut() = span;
        }
        let (ty, subs) = self.instantiate(data.ty().clone());
        set.substitute_many(&subs);
        set.extend(lhs_set);
        set.extend(rhs_set);
        let Ty::Fn { param: lhs_ty, ret } = &ty else {
            return Err(CheckError::new(CheckErrorKind::NotConstructor(ty), span).into());
        };
        let Ty::Fn { param: rhs_ty, ret } = ret.as_ref() else {
            return Err(CheckError::new(
                CheckErrorKind::NotConstructor(ret.as_ref().clone()),
                span,
            )
            .into());
        };
        let mut ret = Ty::from(ret);
        let c1 = EqConstraint::new(lhs_ty.into(), lhs.ty.clone(), lhs.span);
        let c2 = EqConstraint::new(rhs_ty.into(), rhs.ty.clone(), rhs.span);
        let (subs, set) = self.unify([c1, c2], set).map_err(|err| {
            let label = DiagnosticLabel::new(format!("operator `{op}` has type `{ty}`"), op.span);
            IsaError::from(err).with_label(label)
        })?;
        ret.substitute_many(&subs);

        let kind = ExprKind::Bin {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };

        Ok((Expr::new(kind, span, ret), set))
    }

    fn check_un(&mut self, op: Ident, expr: UntypedExpr, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        let (expr, expr_set) = self.check(expr)?;
        let data = self.ctx.get_prefix(op)?;
        let mut set = data.set().clone();
        for c in &mut set.constrs {
            *c.span_mut() = op.span;
        }
        let (op_ty, subs) = self.instantiate(data.ty().clone());
        set.substitute_many(&subs);
        set.extend(expr_set);
        let Ty::Fn { param: ty, ret } = &op_ty else {
            return Err(CheckError::new(CheckErrorKind::NotConstructor(op_ty), span).into());
        };
        let mut ret = Ty::from(ret);
        let c = EqConstraint::new(ty.into(), expr.ty.clone(), expr.span);
        let (subs, set) = self.unify(c, set)?;
        ret.substitute_many(&subs);
        let kind = ExprKind::Un {
            op,
            expr: Box::new(expr),
        };

        Ok((Expr::new(kind, span, ret), set))
    }

    fn check_list(&mut self, exprs: Box<[UntypedExpr]>, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        let mut typed_exprs = Vec::new();
        let id = self.gen_id();

        let mut set = Set::new();
        let mut constrs = Vec::new();

        for expr in exprs {
            let (expr, expr_set) = self.check(expr)?;
            set.extend(expr_set);
            constrs.push(EqConstraint::new(Ty::Var(id), expr.ty.clone(), expr.span));
            typed_exprs.push(expr);
        }

        let (subs, set) = self.unify(constrs, set)?;
        let mut ty = Ty::Var(id);
        ty.substitute_many(&subs);

        let ty = Ty::list(ty);

        let kind = ExprKind::List(typed_exprs.into_boxed_slice());

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_tuple(&mut self, exprs: Box<[UntypedExpr]>, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        if exprs.is_empty() {
            return Ok((
                Expr::new(ExprKind::Tuple(Box::new([])), span, Ty::Unit),
                Set::new(),
            ));
        }

        let mut typed_exprs = Vec::new();
        let mut types = Vec::new();
        let mut set = Set::new();

        for expr in exprs {
            let (expr, expr_set) = self.check(expr)?;
            set.extend(expr_set);
            types.push(expr.ty.clone());
            typed_exprs.push(expr);
        }

        let kind = ExprKind::Tuple(typed_exprs.into_boxed_slice());
        let ty = Ty::Tuple(types.into());

        Ok((Expr::new(kind, span, ty), set))
    }

    fn instantiate(&mut self, ty: Ty) -> (Ty, Vec<Subs>) {
        ty.instantiate(&mut self.generator)
    }

    fn check_module_types(&mut self, module: &mut UntypedModule) -> IsaResult<()> {
        self.ctx.create_module(module.name);
        let mut declared = FxHashMap::default();
        for expr in &mut module.stmts {
            self.check_type_declaration(expr, &mut declared)?;
        }

        Ok(())
    }

    fn check_type_declaration(
        &mut self,
        stmt: &mut UntypedStmt,
        declared: &mut FxHashMap<Ident, Span>,
    ) -> IsaResult<()> {
        let (name, span) = match &mut stmt.kind {
            StmtKind::Type {
                name,
                parameters,
                constructors,
            } => {
                let mut subs = Vec::new();
                let mut params = Vec::new();

                for param in parameters {
                    let id = self.gen_id();
                    let mut new = Ty::Var(id);
                    std::mem::swap(param, &mut new);
                    let old = new.get_ident().unwrap();
                    subs.push((old, id));
                    params.push(id);
                }

                for ctor in constructors {
                    ctor.substitute_param(&subs);
                }

                self.ctx.insert_ty(*name, params.into())?;

                (*name, stmt.span)
            }
            StmtKind::Val(val) => {
                let mut subs = Vec::new();

                for param in &mut val.params {
                    let id = self.gen_id();
                    let mut new = Ty::Var(id);
                    std::mem::swap(param, &mut new);
                    let old = new.get_ident().unwrap();
                    subs.push((old, id));
                }

                val.ty.substitute_param(&subs);

                return Ok(());
            }
            StmtKind::Alias {
                name,
                parameters,
                ty,
            } => {
                let mut subs = Vec::new();
                let mut params = Vec::new();

                for param in parameters {
                    let id = self.gen_id();
                    let mut new = Ty::Var(id);
                    std::mem::swap(param, &mut new);
                    let old = new.get_ident().unwrap();
                    subs.push((old, id));
                    params.push(id);
                }

                ty.substitute_param(&subs);

                self.ctx.insert_ty(*name, params.into())?;

                (*name, stmt.span)
            }
            StmtKind::Class {
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

                    let mut subs = Vec::new();
                    for param in &mut sig.params {
                        let id = self.gen_id();
                        let mut new = Ty::Var(id);
                        std::mem::swap(param, &mut new);
                        let old = new.get_ident().unwrap();
                        subs.push((old, id));
                    }
                    sig.substitute_param(&subs);
                }

                let class = ClassData::new(set.clone(), var, stmt.span);
                let _ = self.ctx.insert_class(name.ident, class);
                let _ = self.ctx.insert_instance_at_env(
                    Ty::Var(var),
                    *name,
                    InstanceData::new(Set::new(), stmt.span),
                );
                self.ctx.assume_constraints(set);

                (*name, stmt.span)
            }
            StmtKind::Operator {
                params, set, ops, ..
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
                for op in ops {
                    op.ty.substitute_param(&subs);
                }

                return Ok(());
            }
            StmtKind::Instance {
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

                return Ok(());
            }

            StmtKind::Semi(_) => return Ok(()),
        };

        declared.insert(name, span).map_or(Ok(()), |previous| {
            let fst = DiagnosticLabel::new(format!("multiple definitons of `{name}`"), span);
            let snd = DiagnosticLabel::new("previously defined here", previous);
            Err(IsaError::new("multiple definitons", fst, vec![snd]))
        })
    }

    fn check_alias_declaration(
        &self,
        module: Ident,
        expr: &UntypedStmt,
    ) -> Option<IsaResult<(Path, AliasData)>> {
        match &expr.kind {
            StmtKind::Alias {
                name,
                parameters,
                ty,
            } => Some(self.check_valid_type(ty).map(|()| {
                let vars = parameters
                    .iter()
                    .map(|param| param.as_var().unwrap())
                    .collect();
                (
                    Path::new(smallvec![module, *name]),
                    AliasData::new(vars, ty.clone()),
                )
            })),

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
        for c in &mut constraints.constrs {
            *c.span_mut() = span;
        }
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

        constraints.extend(member_set);

        constraints.substitute(&mut subs);
        sig.substitute(&mut subs);
        constraints.substitute_many(&sig_subs);
        sig.substitute_many(&sig_subs);

        constraints.push(ClassConstraint::new(class, Ty::Var(new_var), span));

        Ok((sig, constraints))
    }

    fn check_for_class_signatures(&mut self, expr: &mut UntypedStmt) -> IsaResult<()> {
        match &mut expr.kind {
            StmtKind::Class {
                name,
                signatures,
                defaults,
                ..
            } => self.check_class_signatures(*name, signatures, defaults),
            StmtKind::Instance {
                set,
                class,
                instance,
                ..
            } => {
                let data = InstanceData::new(set.clone(), expr.span);
                self.check_valid_type(instance)?;
                let instance = self.ctx.generalize(instance.clone());
                self.ctx.insert_instance(instance, class, data)?;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn early_resolve_imports(&mut self, modules: &mut [UntypedModule]) -> Vec<CheckError> {
        loop {
            let mut errors = Vec::new();
            let mut changed = false;
            for module in modules.iter_mut() {
                self.ctx.set_current_module(module.name);
                let (cur, err) = self.ctx.import_clause(module.imports.clone());
                changed |= cur;
                errors.extend(err);
                if !module.no_prelude {
                    match self.ctx.import_prelude() {
                        Ok(ok) => changed |= ok,
                        Err(err) => errors.push(err),
                    }
                }
            }
            if !changed {
                break errors;
            }
        }
    }

    pub fn check_many_modules(
        &mut self,
        mut modules: Vec<UntypedModule>,
    ) -> IsaResult<(Vec<Module<Ty>>, Set)> {
        for module in &mut modules {
            self.check_module_types(module)?;
        }

        self.early_resolve_imports(&mut modules);

        let mut subs = |ty: &Ty| match ty {
            Ty::Named { name, args } => {
                let name = self.ctx.resolve_type_name(name).ok()?;
                Some(Ty::Named {
                    name,
                    args: args.clone(),
                })
            }
            _ => None,
        };

        let mut aliases = Vec::new();
        for module in &mut modules {
            for stmt in &mut module.stmts {
                stmt.substitute(&mut subs);
                if let Some(alias) = self.check_alias_declaration(module.name, stmt) {
                    aliases.push(alias?);
                }
            }
        }

        let mut decl = Vec::new();
        let mut set = Set::new();

        for module in &mut modules {
            self.ctx.set_current_module(module.name);

            for stmt in &mut module.stmts {
                self.check_for_class_signatures(stmt)?;
            }

            let mut stmts = Vec::new();
            for stmt in module
                .stmts
                .extract_if(.., |e| e.kind.is_type_or_val_or_op())
            {
                let (stmt, stmt_set) = self.check_stmt(stmt)?;
                stmts.push(stmt);
                set.extend(stmt_set);
            }

            decl.push(stmts);
        }

        let mut errs = self.early_resolve_imports(&mut modules);
        if let Some(err) = errs.pop() {
            return Err(IsaError::from(err));
        }

        let modules = modules
            .into_iter()
            .zip(decl)
            .map(|(module, mut decl)| {
                let (mut module, module_set) = self.check_module(module)?;
                decl.extend(module.stmts);
                module.stmts = decl;
                set.extend(module_set);
                Ok(module)
            })
            .collect::<IsaResult<_>>()?;

        Ok((modules, set))
    }

    fn check_module(&mut self, module: UntypedModule) -> IsaResult<(Module<Ty>, Set)> {
        self.ctx.push_scope();

        self.ctx.set_current_module(module.name);

        let mut stmts = Vec::new();
        let mut set = Set::new();

        for res in module.stmts.into_iter().map(|stmt| self.check_stmt(stmt)) {
            let (stmt, stmt_set) = res?;
            stmts.push(stmt);
            set.extend(stmt_set);
        }

        let scope = self.ctx.pop_scope().unwrap();
        self.ctx.extend_module(module.name.ident, scope);
        let typed = Module::new(
            module.no_prelude,
            module.name,
            module.imports,
            stmts,
            module.span,
        );

        Ok((typed, set))
    }

    fn check_stmt(&mut self, stmt: UntypedStmt) -> IsaResult<(Stmt<Ty>, Set)> {
        let span = stmt.span;
        match stmt.kind {
            StmtKind::Semi(expr) => {
                let (expr, set) = self.check(expr)?;
                Ok((Stmt::new(StmtKind::Semi(expr), span), set))
            }

            StmtKind::Type {
                name,
                parameters,
                constructors,
            } => Ok((
                self.check_type_definition(name, parameters, constructors, span)?,
                Set::new(),
            )),

            StmtKind::Alias {
                name,
                parameters,
                ty,
            } => Ok((
                Stmt::new(
                    StmtKind::Alias {
                        name,
                        parameters,
                        ty,
                    },
                    span,
                ),
                Set::new(),
            )),

            StmtKind::Val(val) => {
                let val = self.check_val_stmt(val, span)?;
                Ok((val, Set::new()))
            }
            StmtKind::Class {
                set,
                name,
                instance,
                signatures,
                defaults,
            } => self.check_class(set, name, instance, signatures, defaults, span),

            StmtKind::Instance {
                params,
                set,
                class: name,
                instance,
                impls,
            } => self.check_instance(params, set, name, instance, impls, span),

            StmtKind::Operator { params, set, ops } => {
                let operator = self.check_operator(params, set, ops, span)?;
                Ok((operator, Set::new()))
            }
        }
    }

    fn check(&mut self, expr: UntypedExpr) -> IsaResult<(Expr<Ty>, Set)> {
        let span = expr.span;
        match expr.kind {
            ExprKind::Int(i) => Ok((Expr::new(ExprKind::Int(i), span, Ty::Int), Set::new())),

            ExprKind::Bool(b) => Ok((Expr::new(ExprKind::Bool(b), span, Ty::Bool), Set::new())),

            ExprKind::Char(c) => Ok((Expr::new(ExprKind::Char(c), span, Ty::Char), Set::new())),

            ExprKind::Operator(op) => self.check_operator_expr(op, span),

            ExprKind::Path(path) => {
                let (path, ty, set) = Self::check_path(&self.ctx, &mut self.generator, path, span)?;
                Ok((Expr::new(ExprKind::Path(path), span, ty), set))
            }

            ExprKind::Tuple(exprs) => self.check_tuple(exprs, span),

            ExprKind::List(exprs) => self.check_list(exprs, span),

            ExprKind::Bin { op, lhs, rhs } => self.check_bin(op, *lhs, *rhs, span),

            ExprKind::Un { op, expr } => self.check_un(op, *expr, span),

            ExprKind::If {
                cond,
                then,
                otherwise,
            } => self.check_if(*cond, *then, *otherwise, span),

            ExprKind::Fn { param, expr } => self.check_fn(param, *expr, span),

            ExprKind::Call { callee, arg } => self.check_call(*callee, *arg, span),

            ExprKind::Let { bind, body } => self.check_let(*bind, body.map(|body| *body), span),

            ExprKind::Match { expr, arms } => self.check_match(*expr, arms, span),
        }
    }
}
