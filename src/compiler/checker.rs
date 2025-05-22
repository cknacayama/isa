use rustc_hash::FxHashMap;

use super::ast::{
    Expr, ExprKind, Fixity, HiConstraint, HiCtor, HiTy, HiTyKind, Ident, LetBind, ListPat,
    MatchArm, Module, ModuleRenamer, Operator, Param, ParamRenamer, Pat, PatKind, Path, Rename,
    Stmt, StmtKind, Val,
};
use super::ctx::{
    ClassData, Constructor, Ctx, Generator, IdGenerator, InstanceData, MemberData, VarData,
};
use super::error::{
    CheckError, CheckErrorKind, CheckResult, DiagnosticLabel, IsaError, Uninferable,
};
use super::infer::{
    ClassConstraint, ClassConstraintSet as Set, Constraint, EqConstraint, EqConstraintSet,
};
use super::subs::{SelfSub, Subs, Substitute};
use super::types::{Ty, TyId, TyKind, TyQuant, TySlice};
use crate::compiler::ctx::OperatorData;
use crate::global::{Span, Symbol};

#[derive(Debug, Default)]
pub struct Checker {
    ctx:       Ctx,
    subs:      Vec<Subs>,
    generator: IdGenerator,
}

pub type IsaResult<T> = Result<T, IsaError>;

impl Checker {
    #[must_use]
    pub const fn with_ctx(ctx: Ctx) -> Self {
        Self {
            ctx,
            subs: Vec::new(),
            generator: IdGenerator::new(),
        }
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

    fn insert_let<ClassSet>(&mut self, id: Ident, ty: Ty, set: ClassSet) -> Option<VarData>
    where
        Set: From<ClassSet>,
    {
        self.ctx
            .insert_var(id.ident, VarData::new(ty, Set::from(set), id.span))
    }

    fn gen_id(&mut self) -> TyId {
        self.generator.gen_id()
    }

    fn gen_type_var(&mut self) -> Ty {
        self.generator.gen_type_var()
    }

    fn check_valid_type<const SIG: bool>(&self, ty: &HiTy) -> IsaResult<Ty> {
        match ty.kind() {
            HiTyKind::Tuple(args) => {
                let args = args
                    .iter()
                    .map(|ty| self.check_valid_type::<SIG>(ty))
                    .collect::<IsaResult<_>>()?;
                Ok(Ty::tuple(args))
            }
            HiTyKind::Fn { param, ret } => {
                let param = self.check_valid_type::<SIG>(param)?;
                let ret = self.check_valid_type::<SIG>(ret)?;
                Ok(Ty::intern(TyKind::Fn { param, ret }))
            }
            HiTyKind::Named(name) => {
                self.ctx.get_ty_data(name)?;
                Ok(Ty::intern(TyKind::Named {
                    name: Ty::name_from_path(name),
                    args: Ty::empty_slice(),
                }))
            }
            HiTyKind::Var(var) => Ok(Ty::intern(TyKind::Var(*var))),
            HiTyKind::This if SIG => Ok(Ty::intern(TyKind::This(Ty::empty_slice()))),
            HiTyKind::This => {
                let fst = DiagnosticLabel::new(
                    "`Self` type not allowed outside class definition",
                    ty.span,
                );
                Err(IsaError::new("invalid `Self`", fst, Vec::new()))
            }
            HiTyKind::Parametric { ty, args } => {
                let ty = self.check_valid_type::<SIG>(ty)?;
                let args = args
                    .iter()
                    .map(|ty| self.check_valid_type::<SIG>(ty))
                    .collect::<IsaResult<_>>()?;
                let args = Ty::intern_slice(args);
                match ty.kind() {
                    TyKind::Var(var) => Ok(Ty::intern(TyKind::Generic { var: *var, args })),
                    TyKind::Named { name, .. } => {
                        Ok(Ty::intern(TyKind::Named { name: *name, args }))
                    }
                    TyKind::This(_) => Ok(Ty::intern(TyKind::This(args))),

                    TyKind::Scheme { .. }
                    | TyKind::Generic { .. }
                    | TyKind::Fn { .. }
                    | TyKind::Tuple(_)
                    | TyKind::Int
                    | TyKind::Bool
                    | TyKind::Char
                    | TyKind::Real => {
                        unreachable!()
                    }
                }
            }
            HiTyKind::Int => Ok(Ty::int()),
            HiTyKind::Bool => Ok(Ty::bool()),
            HiTyKind::Char => Ok(Ty::char()),
            HiTyKind::Real => Ok(Ty::real()),
        }
    }

    fn check_if(
        &mut self,
        cond: Expr<()>,
        then: Expr<()>,
        otherwise: Expr<()>,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        let (mut cond, set) = self.check_expr(cond)?;
        let (mut then, then_set) = self.check_expr(then)?;
        let (mut otherwise, else_set) = self.check_expr(otherwise)?;

        let c_cond = EqConstraint::new(Ty::bool(), cond.ty, cond.span);
        let c_body = EqConstraint::new(then.ty, otherwise.ty, otherwise.span);

        let (subs, set) = self
            .unify([c_cond, c_body], set.join(then_set).join(else_set))
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
                        let mut then_ty = then.ty;
                        let mut els_ty = otherwise.ty;
                        err.subs().walk_ty(&mut then_ty);
                        err.subs().walk_ty(&mut els_ty);
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

        subs.as_slice().substitute_expr(&mut cond);
        subs.as_slice().substitute_expr(&mut then);
        subs.as_slice().substitute_expr(&mut otherwise);

        let ty = then.ty;

        let kind = ExprKind::If {
            cond:      Box::new(cond),
            then:      Box::new(then),
            otherwise: Box::new(otherwise),
        };

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_fn(
        &mut self,
        param: Param<()>,
        expr: Expr<()>,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        self.ctx.push_scope();

        let mut pat = self.check_pat(param.pat)?;
        let pos = self.subs_count();

        let (expr, set) = self.check_expr(expr)?;
        self.subs_from(pos).substitute_pat(&mut pat);

        self.ctx.pop_scope();

        let ty = Ty::intern(TyKind::Fn {
            param: pat.ty,
            ret:   expr.ty,
        });

        let kind = ExprKind::Fn {
            param: Param::new(pat),
            expr:  Box::new(expr),
        };

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_call(
        &mut self,
        callee: Expr<()>,
        arg: Expr<()>,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        let (mut callee, set) = self.check_expr(callee)?;
        let (mut arg, arg_set) = self.check_expr(arg)?;

        let mut var = self.gen_type_var();
        let fn_ty = Ty::intern(TyKind::Fn {
            param: arg.ty,
            ret:   var,
        });
        let constr = EqConstraint::new(callee.ty, fn_ty, span);
        let (subs, set) = self.unify(constr, set.join(arg_set)).map_err(|err| {
            if err.constr().is_class() {
                return IsaError::from(err);
            }

            err.subs().walk_ty(&mut callee.ty);
            err.subs().walk_ty(&mut arg.ty);

            let (fst, labels) = if let TyKind::Fn { param, .. } = callee.ty.kind() {
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

        subs.as_slice().substitute_expr(&mut callee);
        subs.as_slice().substitute_expr(&mut arg);
        subs.as_slice().walk_ty(&mut var);

        let kind = ExprKind::Call {
            callee: Box::new(callee),
            arg:    Box::new(arg),
        };

        Ok((Expr::new(kind, span, var), set))
    }

    fn check_let_bind_with_val(
        &mut self,
        bind: LetBind<()>,
        val_decl: Ty,
        mut val_set: Set,
        ty_span: Span,
    ) -> IsaResult<(Ty, Expr<Ty>, Box<[Param<Ty>]>, Set)> {
        self.ctx.push_scope();

        let (val_decl, val_subs) = self.instantiate(val_decl);
        val_subs.as_slice().substitute_class_set(&mut val_set);

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
                let c = EqConstraint::new(decl, pat.ty, pat.span);
                let (subs, _) = self.unify(c, [])?;
                subs.as_slice().substitute_pat(&mut pat);

                Ok(Param::new(pat))
            })
            .collect::<IsaResult<Box<_>>>()?;

        self.ctx.assume_constraints(&val_set);

        let (mut expr, set) = if typed_params.is_empty() {
            self.check_expr(bind.expr)?
        } else {
            let pos = self.subs_count();
            let (mut expr, set) = self.check_expr(bind.expr)?;

            let subs = self.subs_from(pos);
            for param in &mut typed_params {
                subs.substitute_param(param);
            }

            expr.ty = Ty::function(typed_params.iter().map(|p| p.pat.ty), expr.ty);
            (expr, set)
        };

        self.ctx.pop_scope();

        let ty = expr.ty;

        let constr = EqConstraint::new(val_decl, ty, expr.span);

        let val_error = |ty: &Ty, span| {
            let fst = DiagnosticLabel::new(format!("expected `{val_decl}`"), bind.name.span);
            let snd = DiagnosticLabel::new(format!("this has type `{ty}`"), span);
            let trd = DiagnosticLabel::new("expected due to this", ty_span);

            IsaError::new("type mismatch", fst, vec![snd, trd])
                .with_note("let bind should have same type as val declaration")
        };

        let (subs, set) = self.unify(constr, set).map_err(|err| {
            if let Constraint::Eq(eq_constraint) = err.constr() {
                val_error(eq_constraint.rhs(), eq_constraint.span())
            } else {
                IsaError::from(err).with_note("let bind should have same type as val declaration")
            }
        })?;

        if subs.iter().any(|s| {
            val_subs
                .iter()
                .any(|v| v.subs().as_var().is_some_and(|v| v == s.old()))
        }) {
            subs.as_slice().walk_ty(&mut expr.ty);
            let ty = self.ctx.generalize(expr.ty);
            return Err(val_error(&ty, expr.span));
        }

        if let Some(c) = set.iter().find(|c| !val_set.contains(c)) {
            let fst = DiagnosticLabel::new(
                format!("type `{}` is not instance of `{}`", c.ty(), c.class()),
                c.span(),
            );
            let snd = DiagnosticLabel::new("declared here", ty_span);

            return Err(IsaError::new("class mismatch", fst, vec![snd])
                .with_note("let bind should have same type as val declaration"));
        }

        subs.as_slice().substitute_expr(&mut expr);
        for param in &mut typed_params {
            subs.as_slice().substitute_param(param);
        }

        let ty = self.ctx.generalize(expr.ty);

        Ok((ty, expr, typed_params, val_set))
    }

    fn check_let_bind(
        &mut self,
        bind: LetBind<()>,
    ) -> IsaResult<(Ty, Expr<Ty>, Box<[Param<Ty>]>, Set)> {
        if bind.operator {
            let mut op = self
                .ctx
                .get_infix(bind.name)
                .or_else(|_| self.ctx.get_prefix(bind.name))?
                .clone();
            if op.class_member() {
                let ty = self.gen_type_var();
                let subs = SelfSub::new(ty);
                subs.walk_ty(&mut op.ty);
                subs.substitute_class_set(&mut op.set);
            }

            return self.check_let_bind_with_val(bind, op.ty, op.set, op.span);
        }
        if self.ctx.current_depth() == 1
            && let Ok(val) = self.ctx.current()?.get_val(bind.name)
        {
            let VarData { ty, constrs, span } = val.clone();
            return self.check_let_bind_with_val(bind, ty, constrs, span);
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
            self.check_expr(bind.expr)?
        } else {
            let pos = self.subs_count();
            let var_id = self.gen_id();
            let var = Ty::force_insert(TyKind::Var(var_id));
            self.insert_let(bind.name, var, []);

            let (mut expr, set) = self.check_expr(bind.expr)?;

            let subs = self.subs_from(pos);
            for param in &mut typed_params {
                subs.substitute_param(param);
            }

            expr.ty = Ty::function(typed_params.iter().map(|p| p.pat.ty), expr.ty);

            let subs = Subs::new(var_id, expr.ty);

            subs.substitute_expr(&mut expr);

            (expr, set)
        };

        self.ctx.pop_scope();

        let ty = self.ctx.generalize(expr.ty);

        Ok((ty, expr, typed_params, set))
    }

    fn check_let_stmt(&mut self, bind: LetBind<()>, span: Span) -> IsaResult<Stmt<Ty>> {
        let name = bind.name;
        let operator = bind.operator;

        let (u1, expr, params, set) = self.check_let_bind(bind)?;

        self.insert_let(name, u1, set);

        let bind = LetBind::new(operator, name, params, expr);

        let kind = StmtKind::Let(bind);

        Ok(Stmt::new(kind, span))
    }

    fn check_let(
        &mut self,
        bind: LetBind<()>,
        body: Expr<()>,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        let name = bind.name;

        let (u1, expr, params, set) = self.check_let_bind(bind)?;

        self.ctx.push_scope();
        self.insert_let(name, u1, set.clone());
        let (body, body_set) = self.check_expr(body)?;
        self.ctx.pop_scope();
        let ty = body.ty;
        let set = set.join(body_set);

        let bind = LetBind::new(false, name, params, expr);

        let kind = ExprKind::Let {
            bind: Box::new(bind),
            body: Box::new(body),
        };

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_constructor(
        &self,
        constructor: HiCtor,
        quant: TyQuant,
        ret: Ty,
    ) -> IsaResult<(HiCtor, Constructor)> {
        let params = self.check_params(&constructor.params)?;
        let mut ret = Ty::function(params.iter().copied(), ret);
        if !quant.is_empty() {
            ret = Ty::intern(TyKind::Scheme { quant, ty: ret });
        }
        let ctor = Constructor::new(constructor.name, params, constructor.span, ret);
        Ok((constructor, ctor))
    }

    fn check_type_definition(
        &mut self,
        name: Ident,
        params: Box<[HiTy]>,
        constructors: Box<[HiCtor]>,
        span: Span,
    ) -> IsaResult<Stmt<Ty>> {
        let (quant, args) = self.check_quant(&params);

        let module = Ident::new(self.ctx.current_module().ident, name.span);
        let ty = Ty::intern(TyKind::Named {
            name: Ty::intern_path(vec![module.ident, name.ident]),
            args,
        });

        let constructors = constructors
            .into_iter()
            .map(|c| {
                let (hi, ctor) = self.check_constructor(c, quant, ty)?;
                self.ctx.insert_constructor_for_ty(name, &ctor)?;
                Ok(hi)
            })
            .collect::<IsaResult<_>>()?;

        let kind = StmtKind::Type {
            name,
            params,
            constructors,
        };

        Ok(Stmt::new(kind, span))
    }

    fn check_set<const SIG: bool>(&self, set: &[HiConstraint]) -> IsaResult<Set> {
        set.iter()
            .map(|c| {
                self.ctx.get_class(&c.class)?;
                let ty = self.check_valid_type::<SIG>(&c.ty)?;
                Ok(ClassConstraint::new(c.class.clone(), ty, c.span))
            })
            .collect()
    }

    fn check_quant(&self, quant: &[HiTy]) -> (TyQuant, TySlice) {
        let params = self.check_params(quant).unwrap();
        let quant = params.iter().map(|t| t.as_var().unwrap()).collect();
        (Ty::intern_quant(quant), params)
    }

    fn check_params(&self, quant: &[HiTy]) -> IsaResult<TySlice> {
        let quant = quant
            .iter()
            .map(|t| self.check_valid_type::<false>(t))
            .collect::<IsaResult<_>>()?;
        Ok(Ty::intern_slice(quant))
    }

    fn check_operator<const IS_CLASS: bool>(
        &mut self,
        fixity: Fixity,
        prec: u8,
        params: &[HiTy],
        set: &[HiConstraint],
        op: Symbol,
        hity: &HiTy,
        span: Span,
    ) -> IsaResult<(Ty, Set)> {
        let (quant, _) = self.check_quant(params);
        let set = self.check_set::<IS_CLASS>(set)?;

        let ty = self.check_valid_type::<IS_CLASS>(hity)?;
        let arity = ty.function_arity();
        let ty = if quant.is_empty() {
            ty
        } else {
            Ty::intern(TyKind::Scheme { quant, ty })
        };

        let data = OperatorData::new(IS_CLASS, fixity, prec, ty, set.clone(), span);
        let min = fixity.minimum_arity();
        if arity < min {
            let fst = DiagnosticLabel::new("invalid operator type", hity.span);
            let note = format!("{fixity} operator should have at least arity of {min}");
            return Err(IsaError::new("invalid operator", fst, Vec::new()).with_note(note));
        }

        let fixity_error = |prev: OperatorData| {
            let fst =
                DiagnosticLabel::new(format!("redefinition of {fixity} operator `{op}`"), span);
            let snd = DiagnosticLabel::new("previously defined here", prev.span());
            Err(IsaError::new("redefined operator", fst, vec![snd]))
        };

        if fixity.is_prefix() {
            self.ctx
                .insert_prefix(op, data)
                .map_or(Ok((ty, set)), fixity_error)
        } else {
            self.ctx
                .insert_infix(op, data)
                .map_or(Ok((ty, set)), fixity_error)
        }
    }

    fn check_operator_stmt(&mut self, op: &Operator) -> IsaResult<()> {
        self.check_operator::<false>(
            op.fixity,
            op.prec,
            &op.params,
            &op.set,
            op.op.ident,
            &op.ty,
            op.span,
        )
        .map(|_| ())
    }

    fn check_val<const IS_CLASS: bool>(&self, val: &Val) -> IsaResult<(Ty, Set)> {
        let (quant, _) = self.check_quant(&val.params);
        let set = self.check_set::<IS_CLASS>(&val.set)?;

        let ty = self.check_valid_type::<IS_CLASS>(&val.ty)?;

        if quant.is_empty() {
            Ok((Ty::intern(TyKind::Scheme { quant, ty }), set))
        } else {
            Ok((ty, set))
        }
    }

    fn check_val_stmt(&mut self, val: Val, span: Span) -> IsaResult<Stmt<Ty>> {
        let (ty, set) = self.check_val::<false>(&val)?;

        self.ctx
            .current_mut()
            .unwrap()
            .insert_val(val.name.ident, VarData::new(ty, set, val.span));

        let kind = StmtKind::Val(val);

        Ok(Stmt::new(kind, span))
    }

    fn check_constructor_pat(
        &mut self,
        name: Path,
        args: Box<[Pat<()>]>,
        span: Span,
    ) -> IsaResult<Pat<Ty>> {
        let ctor = match (self.ctx.get_constructor(&name), name.as_slice()) {
            (Ok(ctor), _) => *ctor,
            (Err(_), [name]) if args.is_empty() => {
                let var = self.gen_type_var();
                self.insert_let(*name, var, []);
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
            let TyKind::Fn { param, ret } = ty.kind() else {
                return Err(CheckError::new(CheckErrorKind::NotConstructor(ty), span).into());
            };
            c.push_back(EqConstraint::new(*param, arg.ty, arg.span));
            ty = *ret;
            typed_args.push(arg);
        }

        if ty.is_fn() {
            return Err(CheckError::new(CheckErrorKind::Kind(ty), span).into());
        }

        let (subs, _) = self.unify(c, [])?;

        for pat in &mut typed_args {
            subs.as_slice().substitute_pat(pat);
        }
        subs.as_slice().walk_ty(&mut ty);

        let kind = PatKind::Constructor {
            name,
            args: typed_args.into_boxed_slice(),
        };

        Ok(Pat::new(kind, span, ty))
    }

    fn check_class_signatures(
        &mut self,
        name: Ident,
        parents: &[Path],
        set: &[HiConstraint],
        signatures: &[Val],
        ops: &[Operator],
        defaults: &[LetBind<()>],
    ) -> IsaResult<()> {
        let set = self.check_set::<true>(set)?;
        let mut vals = Vec::new();
        for val in signatures {
            vals.push(self.check_val::<true>(val)?);
        }

        let class = Path::from_two(self.ctx.current_module(), name);

        let mut operators = Vec::new();
        for Operator {
            fixity,
            prec,
            params,
            set,
            op,
            ty,
            span,
        } in ops
        {
            let mut set = set.to_vec();
            set.push(HiConstraint::new(
                class.clone(),
                HiTy::new(HiTyKind::This, *span),
                *span,
            ));
            let op =
                self.check_operator::<true>(*fixity, *prec, params, &set, op.ident, ty, *span)?;
            operators.push(op);
        }

        let val_signatures = signatures.iter().zip(vals).map(|(val, (ty, set))| {
            (
                val.name.ident,
                MemberData {
                    has_default: defaults.iter().any(|bind| bind.name == val.name),
                    set,
                    ty,
                    span: val.span,
                },
            )
        });

        let op_signatures = ops.iter().zip(operators).map(|(op, (ty, set))| {
            (
                op.op.ident,
                MemberData {
                    has_default: defaults.iter().any(|bind| bind.name == op.op),
                    set,
                    ty,
                    span: op.span,
                },
            )
        });

        self.ctx
            .current_mut()
            .unwrap()
            .get_class_data_mut(name)
            .unwrap()
            .extend_signature(val_signatures.chain(op_signatures), Box::from(parents), set);

        Ok(())
    }

    fn check_class(
        &mut self,
        hiset: Box<[HiConstraint]>,
        name: Ident,
        parents: Box<[Path]>,
        signatures: Box<[Val]>,
        ops: Box<[Operator]>,
        defaults: Box<[LetBind<()>]>,
        span: Span,
    ) -> IsaResult<Stmt<Ty>> {
        let set = self.check_set::<true>(&hiset)?;
        self.ctx.assume_constraints(&set);

        let var = self.gen_type_var();
        let class = Path::from_two(self.ctx.current_module(), name);
        self.ctx
            .assume_constraints(&Set::from(ClassConstraint::new(class.clone(), var, span)));
        let defaults = self.check_instance_impls(&class, defaults, SelfSub::new(var))?;

        let kind = StmtKind::Class {
            set: hiset,
            name,
            parents,
            signatures,
            ops,
            defaults: defaults.into_boxed_slice(),
        };

        Ok(Stmt::new(kind, span))
    }

    fn check_instance_impls(
        &mut self,
        class: &Path,
        impls: impl IntoIterator<Item = LetBind<()>>,
        subs: SelfSub,
    ) -> IsaResult<Vec<LetBind<Ty>>> {
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
                    .get(&bind.name.ident)
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

                subs.walk_ty(&mut ty);
                let name = bind.name;
                let operator = bind.operator;
                let (_, expr, params, _) =
                    self.check_let_bind_with_val(bind, ty, member_set, ty_span)?;
                Ok(LetBind::new(operator, name, params, expr))
            })
            .collect::<IsaResult<_>>()?;
        Ok(impls)
    }

    fn check_instance(
        &mut self,
        hiparams: Box<[HiTy]>,
        hiset: Box<[HiConstraint]>,
        class: Path,
        instance: HiTy,
        impls: Box<[LetBind<()>]>,
        span: Span,
    ) -> IsaResult<Stmt<Ty>> {
        let class_data = self.ctx.get_class(&class)?;

        let (quant, _) = self.check_quant(&hiparams);
        let set = self.check_set::<false>(&hiset)?;

        let ty = self.check_valid_type::<false>(&instance)?;
        let scheme = if quant.is_empty() {
            ty
        } else {
            Ty::intern(TyKind::Scheme { quant, ty })
        };
        for parent in class_data.parents() {
            if self.ctx.implementation(scheme, parent).is_err() {
                let fst = DiagnosticLabel::new(
                    format!("type `{scheme}` doesn't implement `{parent}`"),
                    span,
                );
                let snd = DiagnosticLabel::new("constraint declared here", parent.span());
                let note = format!(
                    "for `{scheme}` to instantiate `{class}`, it needs to first instantiate `{parent}`"
                );

                return Err(IsaError::new("class mismatch", fst, vec![snd]).with_note(note));
            }
        }

        if let Some((
            not_implemented,
            MemberData {
                span: member_span, ..
            },
        )) = class_data.signatures().iter().find(|(name, data)| {
            !data.has_default && !impls.iter().any(|bind| bind.name.ident.eq(name))
        }) {
            let fst = DiagnosticLabel::new(
                format!("member `{not_implemented}` of `{class}` not implemented"),
                span,
            );
            let snd = DiagnosticLabel::new("declared here", *member_span);

            return Err(IsaError::new("member not implemented", fst, vec![snd]));
        }

        self.ctx.set_constraints(&class, scheme, set.clone());
        self.ctx.assume_constraints(&set);
        let impls = self.check_instance_impls(&class, impls, SelfSub::new(ty))?;

        let kind = StmtKind::Instance {
            params: hiparams,
            set: hiset,
            class,
            instance,
            impls: impls.into(),
        };

        Ok(Stmt::new(kind, span))
    }

    fn check_list_pat(&mut self, list: ListPat<()>, span: Span) -> IsaResult<Pat<Ty>> {
        match list {
            ListPat::Nil => {
                let ty = Ty::list(self.gen_type_var());
                Ok(Pat::new(PatKind::List(ListPat::Nil), span, ty))
            }
            ListPat::Single(pat) => {
                let pat = self.check_pat(*pat)?;
                let ty = Ty::list(pat.ty);
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
                let mut ty = Ty::list(pat.ty);
                let c = EqConstraint::new(ty, pat1.ty, span);
                let (subs, _) = self.unify(c, [])?;
                subs.as_slice().walk_ty(&mut ty);
                let kind = PatKind::List(ListPat::Cons(Box::new(pat), Box::new(pat1)));

                Ok(Pat::new(kind, span, ty))
            }
        }
    }

    fn check_pat(&mut self, Pat { kind, span, .. }: Pat<()>) -> IsaResult<Pat<Ty>> {
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
                    c.push_back(EqConstraint::new(pat.ty, var, pat.span));
                    patterns.push(pat);
                }

                let (subs, _) = self.unify(c, []).map_err(|err| {
                    IsaError::from(err).with_note("or sub-patterns should have same type")
                })?;

                for pat in &mut patterns {
                    subs.as_slice().substitute_pat(pat);
                }
                subs.as_slice().walk_ty(&mut var);

                Ok(Pat::new(
                    PatKind::Or(patterns.into_boxed_slice()),
                    span,
                    var,
                ))
            }
            PatKind::List(list) => self.check_list_pat(list, span),
            PatKind::Int(i) => Ok(Pat::new(PatKind::Int(i), span, Ty::int())),
            PatKind::Real(r) => Ok(Pat::new(PatKind::Real(r), span, Ty::real())),
            PatKind::Bool(b) => Ok(Pat::new(PatKind::Bool(b), span, Ty::bool())),
            PatKind::Char(c) => Ok(Pat::new(PatKind::Char(c), span, Ty::char())),
            PatKind::Tuple(pats) => {
                if pats.is_empty() {
                    return Ok(Pat::new(PatKind::Tuple(Box::new([])), span, Ty::unit()));
                }

                let mut types = Vec::new();
                let mut typed_pats = Vec::new();

                for pat in pats {
                    let pat = self.check_pat(pat)?;
                    types.push(pat.ty);
                    typed_pats.push(pat);
                }

                let kind = PatKind::Tuple(typed_pats.into_boxed_slice());
                let ty = Ty::tuple(types);

                Ok(Pat::new(kind, span, ty))
            }
            PatKind::Constructor { name, args } => self.check_constructor_pat(name, args, span),

            PatKind::Ident(_) => {
                unreachable!("Parser never returns Ident pattern")
            }

            PatKind::IntRange(range) => Ok(Pat::new(PatKind::IntRange(range), span, Ty::int())),

            PatKind::RealRange(range) => Ok(Pat::new(PatKind::RealRange(range), span, Ty::real())),

            PatKind::CharRange(range) => Ok(Pat::new(PatKind::CharRange(range), span, Ty::char())),
        }
    }

    fn check_match_arm(
        &mut self,
        pat: Pat<()>,
        expr: Expr<()>,
    ) -> IsaResult<(Pat<Ty>, Expr<Ty>, Set)> {
        self.ctx.push_scope();

        let mut pat = self.check_pat(pat)?;

        let count = self.subs_count();

        let (expr, set) = self.check_expr(expr)?;

        self.subs_from(count).substitute_pat(&mut pat);

        self.ctx.pop_scope();

        Ok((pat, expr, set))
    }

    fn check_match(
        &mut self,
        expr: Expr<()>,
        arms: Box<[MatchArm<()>]>,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        let (mut expr, mut set) = self.check_expr(expr)?;

        let mut var = self.gen_type_var();
        let mut typed_arms = Vec::new();

        let mut c = EqConstraintSet::new();

        for arm in arms {
            let (pat, aexpr, arm_set) = self.check_match_arm(arm.pat, arm.expr)?;
            set.extend(arm_set);
            c.push_back(EqConstraint::new(var, aexpr.ty, aexpr.span));
            c.push_back(EqConstraint::new(expr.ty, pat.ty, pat.span));
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

        subs.as_slice().substitute_expr(&mut expr);
        subs.as_slice().walk_ty(&mut var);
        for arm in &mut typed_arms {
            subs.as_slice().substitute_match_arm(arm);
        }

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
        match *path.as_slice() {
            [id] => {
                let VarData {
                    ty, mut constrs, ..
                } = ctx.get_var(id)?.clone();
                let (ty, subs) = ty.instantiate(generator);
                subs.as_slice().substitute_class_set(&mut constrs);

                Ok((Path::from_one(id), ty, constrs))
            }

            [first, id] => {
                if let Ok(ty) = ctx.get_constructor(&path) {
                    let (ty, _) = (*ty).instantiate(generator);
                    return Ok((path, ty, Set::new()));
                }

                if let Ok((ty, set)) = ctx.get_class(&Path::from_one(first)).and_then(|data| {
                    Self::check_class_member(ctx, Path::from_one(first), data, id, generator, span)
                }) {
                    return Ok((path, ty, set));
                }

                let module = ctx.get_module(first)?;

                let VarData {
                    ty, mut constrs, ..
                } = module.get_var(id)?.clone();

                let (ty, subs) = ty.instantiate(generator);
                subs.as_slice().substitute_class_set(&mut constrs);

                Ok((Path::from_one(id), ty, constrs))
            }

            [fst, snd, trd] => {
                if let Ok(ty) = ctx.get_constructor(&path) {
                    let (ty, _) = (*ty).instantiate(generator);
                    return Ok((path, ty, Set::new()));
                }

                let class_path = Path::from_two(fst, snd);

                let data = ctx.get_class(&class_path)?;

                let (ty, set) =
                    Self::check_class_member(ctx, class_path, data, trd, generator, span)?;

                Ok((path, ty, set))
            }

            _ => unreachable!(),
        }
    }

    fn check_operator_expr(&mut self, op: Ident, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        let data = self
            .ctx
            .get_infix(op)
            .or_else(|_| self.ctx.get_prefix(op))?;
        let from_class = data.class_member();
        let mut set = data.set().clone();
        for c in set.iter_mut() {
            c.span = span;
        }

        let (mut ty, subs) = self.instantiate(*data.ty());
        subs.as_slice().substitute_class_set(&mut set);
        if from_class {
            let subs = SelfSub::new(self.gen_type_var());
            subs.walk_ty(&mut ty);
            subs.substitute_class_set(&mut set);
        }

        let kind = ExprKind::Operator(op);

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_infix(
        &mut self,
        op: Ident,
        lhs: Expr<()>,
        rhs: Expr<()>,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        let (lhs, lhs_set) = self.check_expr(lhs)?;
        let (rhs, rhs_set) = self.check_expr(rhs)?;

        let data = self.ctx.get_infix(op)?;
        let from_class = data.class_member();
        let mut set = data.set().clone();
        for c in set.iter_mut() {
            c.span = span;
        }
        let (mut ty, subs) = self.instantiate(*data.ty());
        subs.as_slice().substitute_class_set(&mut set);
        if from_class {
            let subs = SelfSub::new(self.gen_type_var());
            subs.walk_ty(&mut ty);
            subs.substitute_class_set(&mut set);
        }
        set.extend(lhs_set);
        set.extend(rhs_set);
        let TyKind::Fn { param: lhs_ty, ret } = ty.kind() else {
            return Err(CheckError::new(CheckErrorKind::NotConstructor(ty), span).into());
        };
        let TyKind::Fn { param: rhs_ty, ret } = ret.kind() else {
            return Err(CheckError::new(CheckErrorKind::NotConstructor(*ret), span).into());
        };
        let mut ret = *ret;
        let c1 = EqConstraint::new(*lhs_ty, lhs.ty, lhs.span);
        let c2 = EqConstraint::new(*rhs_ty, rhs.ty, rhs.span);
        let (subs, set) = self.unify([c1, c2], set).map_err(|err| {
            let label = DiagnosticLabel::new(format!("operator `{op}` has type `{ty}`"), op.span);
            IsaError::from(err).with_label(label)
        })?;
        subs.as_slice().walk_ty(&mut ret);

        let kind = ExprKind::Infix {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };

        Ok((Expr::new(kind, span, ret), set))
    }

    fn check_un(&mut self, op: Ident, expr: Expr<()>, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        let (expr, expr_set) = self.check_expr(expr)?;
        let data = self.ctx.get_prefix(op)?;
        let from_class = data.class_member();
        let mut set = data.set().clone();
        for c in set.iter_mut() {
            c.span = op.span;
        }
        let (mut op_ty, subs) = self.instantiate(*data.ty());
        subs.as_slice().substitute_class_set(&mut set);
        if from_class {
            let subs = SelfSub::new(self.gen_type_var());
            subs.walk_ty(&mut op_ty);
            subs.substitute_class_set(&mut set);
        }
        set.extend(expr_set);
        let TyKind::Fn { param: ty, ret } = op_ty.kind() else {
            return Err(CheckError::new(CheckErrorKind::NotConstructor(op_ty), span).into());
        };
        let mut ret = *ret;
        let c = EqConstraint::new(*ty, expr.ty, expr.span);
        let (subs, set) = self.unify(c, set)?;
        subs.as_slice().walk_ty(&mut ret);
        let kind = ExprKind::Prefix {
            op,
            expr: Box::new(expr),
        };

        Ok((Expr::new(kind, span, ret), set))
    }

    fn check_list(&mut self, exprs: Box<[Expr<()>]>, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        let mut typed_exprs = Vec::new();
        let id = self.gen_type_var();

        let mut set = Set::new();
        let mut constrs = Vec::new();

        for expr in exprs {
            let (expr, expr_set) = self.check_expr(expr)?;
            set.extend(expr_set);
            constrs.push(EqConstraint::new(id, expr.ty, expr.span));
            typed_exprs.push(expr);
        }

        let (subs, set) = self.unify(constrs, set)?;
        let mut ty = id;
        subs.as_slice().walk_ty(&mut ty);

        let ty = Ty::list(ty);

        let kind = ExprKind::List(typed_exprs.into_boxed_slice());

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_tuple(&mut self, exprs: Box<[Expr<()>]>, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        if exprs.is_empty() {
            return Ok((
                Expr::new(ExprKind::Tuple(Box::new([])), span, Ty::unit()),
                Set::new(),
            ));
        }

        let mut typed_exprs = Vec::new();
        let mut types = Vec::new();
        let mut set = Set::new();

        for expr in exprs {
            let (expr, expr_set) = self.check_expr(expr)?;
            set.extend(expr_set);
            types.push(expr.ty);
            typed_exprs.push(expr);
        }

        let kind = ExprKind::Tuple(typed_exprs.into_boxed_slice());
        let ty = Ty::tuple(types);

        Ok((Expr::new(kind, span, ty), set))
    }

    fn instantiate(&mut self, ty: Ty) -> (Ty, Vec<Subs>) {
        ty.instantiate(&mut self.generator)
    }

    fn check_module_types(&mut self, module: &mut Module<()>) -> IsaResult<()> {
        self.ctx.create_module(module.name);
        let mut declared = FxHashMap::default();

        let mod_rename = ModuleRenamer(module.name);

        for expr in &mut module.stmts {
            self.check_type_declaration(expr, &mut declared, &mod_rename)?;
        }

        Ok(())
    }

    fn substitute_params(&mut self, params: &mut [HiTy]) -> (ParamRenamer, Vec<TyId>) {
        let (rename, params) = params
            .iter_mut()
            .map(|param| {
                let id = self.gen_id();
                let mut new = HiTyKind::Var(id);
                std::mem::swap(&mut param.kind, &mut new);
                let old = new.get_ident().unwrap();
                ((old, id), id)
            })
            .unzip();
        let rename = ParamRenamer(rename);

        (rename, params)
    }

    fn check_type_declaration(
        &mut self,
        stmt: &mut Stmt<()>,
        declared: &mut FxHashMap<Symbol, Span>,
        rename: &impl Rename,
    ) -> IsaResult<()> {
        let (name, span) = match &mut stmt.kind {
            StmtKind::Type {
                name,
                params,
                constructors,
            } => {
                let (subs, params) = self.substitute_params(params);

                for ctor in constructors {
                    subs.rename_ctor(ctor);
                    rename.rename_ctor(ctor);
                }

                self.ctx.insert_ty(*name, Ty::intern_quant(params))?;

                (name.ident, stmt.span)
            }
            StmtKind::Operator(Operator {
                params, set, ty, ..
            })
            | StmtKind::Val(Val {
                params, set, ty, ..
            }) => {
                let (subs, _) = self.substitute_params(params);

                subs.walk_hi_ty(ty);
                subs.rename_constrs(set);

                rename.walk_hi_ty(ty);
                rename.rename_constrs(set);

                return Ok(());
            }
            StmtKind::Alias { name, params, ty } => {
                let (subs, params) = self.substitute_params(params);

                subs.walk_hi_ty(ty);
                rename.walk_hi_ty(ty);

                self.ctx.insert_ty(*name, Ty::intern_quant(params))?;

                (name.ident, stmt.span)
            }
            StmtKind::Class {
                name,
                signatures,
                ops,
                parents,
                ..
            } => {
                for parent in parents {
                    rename.rename_class(parent);
                }
                for sig in signatures {
                    let (subs, _) = self.substitute_params(&mut sig.params);
                    subs.rename_val(sig);
                    rename.walk_hi_ty(&mut sig.ty);
                    rename.rename_constrs(&mut sig.set);
                }
                for op in ops {
                    let (subs, _) = self.substitute_params(&mut op.params);
                    subs.rename_op(op);
                    rename.walk_hi_ty(&mut op.ty);
                    rename.rename_constrs(&mut op.set);
                }

                let class = ClassData::new(stmt.span);
                let _ = self.ctx.insert_class(name.ident, class);

                (name.ident, stmt.span)
            }
            StmtKind::Instance {
                params,
                set,
                instance,
                ..
            } => {
                let (subs, _) = self.substitute_params(params);

                subs.walk_hi_ty(instance);
                subs.rename_constrs(set);

                rename.walk_hi_ty(instance);
                rename.rename_constrs(set);

                return Ok(());
            }

            StmtKind::Let(_) | StmtKind::Semi(_) => return Ok(()),
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
        expr: &Stmt<()>,
    ) -> Option<IsaResult<(Path, AliasData)>> {
        match &expr.kind {
            StmtKind::Alias { name, params, ty } => {
                let module = Ident::new(module.ident, name.span);
                let path = Path::from_two(module, *name);

                Some(self.check_valid_type::<false>(ty).map(|_| {
                    let vars = params
                        .iter()
                        .map(|param| param.kind().as_var().unwrap())
                        .collect();
                    (path, AliasData::new(vars, ty.clone()))
                }))
            }

            _ => None,
        }
    }

    fn check_class_member(
        ctx: &Ctx,
        mut class: Path,
        data: &ClassData,
        member: Ident,
        generator: &mut impl Generator,
        span: Span,
    ) -> CheckResult<(Ty, Set)> {
        class = ctx.resolve_class_name(&class)?;
        let mut constraints = data.constraints().clone();
        for c in constraints.iter_mut() {
            c.span = span;
        }
        let MemberData {
            ty: sig,
            set: mut member_set,
            ..
        } = data
            .signatures()
            .get(&member.ident)
            .cloned()
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(member.ident), span))?;

        for c in member_set.iter_mut() {
            c.span = span;
        }

        let (mut sig, sig_subs) = sig.instantiate(generator);
        let new_var = generator.gen_type_var();
        let self_sub = SelfSub::new(new_var);
        constraints.extend(member_set);

        self_sub.substitute_class_set(&mut constraints);
        self_sub.walk_ty(&mut sig);
        sig_subs.as_slice().substitute_class_set(&mut constraints);
        sig_subs.as_slice().walk_ty(&mut sig);

        constraints.extend(
            data.parents()
                .iter()
                .map(|class| ClassConstraint::new(class.clone(), new_var, span)),
        );
        constraints.push(ClassConstraint::new(class, new_var, span));

        Ok((sig, constraints))
    }

    fn check_for_signatures(&mut self, stmt: &mut Stmt<()>) -> IsaResult<()> {
        match &mut stmt.kind {
            StmtKind::Class {
                name,
                signatures,
                parents,
                set,
                defaults,
                ops,
                ..
            } => self.check_class_signatures(*name, parents, set, signatures, ops, defaults),
            StmtKind::Instance {
                set,
                class,
                params,
                instance,
                ..
            } => {
                let set = self.check_set::<false>(set)?;
                let data = InstanceData::new(set, stmt.span);
                let ty = self.check_valid_type::<false>(instance)?;
                let (quant, _) = self.check_quant(params);
                let instance = if quant.is_empty() {
                    ty
                } else {
                    Ty::intern(TyKind::Scheme { quant, ty })
                };
                self.ctx.insert_instance(instance, class, data)?;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn resolve_imports(&mut self, modules: &mut [Module<()>]) -> Vec<CheckError> {
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

    fn resolve_infix_in_stmt(&self, stmt: &mut StmtKind<()>) -> IsaResult<()> {
        match stmt {
            StmtKind::Let(LetBind { expr, .. }) | StmtKind::Semi(expr) => self.resolve_infix(expr),
            StmtKind::Instance { impls, .. }
            | StmtKind::Class {
                defaults: impls, ..
            } => {
                for bind in impls {
                    self.resolve_infix(&mut bind.expr)?;
                }
                Ok(())
            }

            StmtKind::Operator(Operator { .. })
            | StmtKind::Val(_)
            | StmtKind::Type { .. }
            | StmtKind::Alias { .. } => unreachable!(),
        }
    }

    fn resolve_infix(&self, expr: &mut Expr<()>) -> IsaResult<()> {
        let span = expr.span;
        match &mut expr.kind {
            ExprKind::Int(_)
            | ExprKind::Real(_)
            | ExprKind::String(_)
            | ExprKind::Bool(_)
            | ExprKind::Char(_)
            | ExprKind::Path(_)
            | ExprKind::Operator(_) => Ok(()),

            ExprKind::List(exprs) | ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.resolve_infix(expr)?;
                }
                Ok(())
            }

            ExprKind::Let { bind, body } => {
                self.resolve_infix(&mut bind.expr)?;
                self.resolve_infix(body)
            }

            ExprKind::Infix { op, lhs, rhs } => {
                let data = self.ctx.get_infix(*op)?;

                // Because we assume all operators are left
                // associative during parsing we resolve the lhs first
                self.resolve_infix(lhs)?;

                if let ExprKind::Infix {
                    op: lop,
                    lhs: llhs,
                    rhs: lrhs,
                } = &mut lhs.kind
                {
                    let ldata = self.ctx.get_infix(*lop)?;

                    // If the operator at the left side
                    // doesn't associate with the current one
                    // then the expression is invalid
                    if ldata.prec() == data.prec()
                        && (ldata.fixity() != data.fixity() || ldata.fixity().is_nonfix())
                    {
                        let fst = DiagnosticLabel::new("invalid infix expression", span);
                        let snd =
                            DiagnosticLabel::new(format!("{lop} is non associative"), lop.span);
                        return Err(IsaError::new("invalid expression", fst, vec![snd]));
                    }

                    // If the operator at the left side
                    // has lower precedence than the current one
                    // OR if it is right associative AND the precedence
                    // is equal, then we rotate the tree
                    // (right rotation in a binary tree)
                    if ldata.prec() < data.prec()
                        || (ldata.prec() == data.prec() && ldata.fixity().is_right())
                    {
                        let new_lhs = std::mem::take(lrhs);
                        let new_rhs = std::mem::take(rhs);

                        let span = new_lhs.span.join(new_rhs.span);
                        let kind = ExprKind::Infix {
                            op:  *op,
                            lhs: new_lhs,
                            rhs: new_rhs,
                        };
                        *rhs = Box::new(Expr::untyped(kind, span));
                        *op = *lop;
                        *lhs = std::mem::take(llhs);
                    }
                }

                self.resolve_infix(rhs)?;

                Ok(())
            }

            ExprKind::Paren(expr) | ExprKind::Prefix { expr, .. } | ExprKind::Fn { expr, .. } => {
                self.resolve_infix(expr)
            }

            ExprKind::Match { expr, arms } => {
                for arm in arms {
                    self.resolve_infix(&mut arm.expr)?;
                }
                self.resolve_infix(expr)
            }

            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.resolve_infix(cond)?;
                self.resolve_infix(then)?;
                self.resolve_infix(otherwise)
            }

            ExprKind::Call { callee, arg } => {
                self.resolve_infix(callee)?;
                self.resolve_infix(arg)
            }
        }
    }

    pub fn check_many_modules(
        &mut self,
        mut modules: Vec<Module<()>>,
    ) -> IsaResult<Vec<Module<Ty>>> {
        for module in &mut modules {
            self.check_module_types(module)?;
        }

        self.resolve_imports(&mut modules);

        let renamer = NameResolver(&self.ctx);

        let mut aliases = Vec::new();
        for module in &mut modules {
            for stmt in &mut module.stmts {
                renamer.rename_stmt(stmt);
                if let Some(alias) = self.check_alias_declaration(module.name, stmt) {
                    aliases.push(alias?);
                }
            }
        }
        AliasData::resolve(&mut aliases);
        for (path, alias) in &aliases {
            if let Some(span) = alias.ty().contains_name(path) {
                let fst = DiagnosticLabel::new("cannot recursively define a type alias", span);
                let snd = DiagnosticLabel::new("references self in definition", path.span());
                return Err(IsaError::new("recursive type alias", fst, vec![snd]));
            }
        }
        let mut decl = Vec::new();

        for module in &mut modules {
            self.ctx.set_current_module(module.name);

            for stmt in &mut module.stmts {
                if !aliases.is_empty() {
                    aliases.rename_stmt(stmt);
                }
                // We check type class signatures before
                // other because we don't extract it
                self.check_for_signatures(stmt)?;
            }

            let stmts = module
                .stmts
                .extract_if(.., |e| e.kind.is_type_or_val_or_op())
                .map(|stmt| self.check_stmt(stmt))
                .collect::<IsaResult<Vec<_>>>()?;

            decl.push(stmts);
        }

        let mut errs = self.resolve_imports(&mut modules);
        if let Some(err) = errs.pop() {
            return Err(IsaError::from(err));
        }

        for module in &mut modules {
            for stmt in &mut module.stmts {
                self.resolve_infix_in_stmt(&mut stmt.kind)?;
            }
        }

        let modules = modules
            .into_iter()
            .zip(decl)
            .map(|(module, mut decl)| {
                let mut module = self.check_module(module)?;
                decl.extend(module.stmts);
                module.stmts = decl;
                Ok(module)
            })
            .collect::<IsaResult<_>>()?;

        Ok(modules)
    }

    fn check_module(&mut self, module: Module<()>) -> IsaResult<Module<Ty>> {
        self.ctx.push_scope();

        self.ctx.set_current_module(module.name);

        let stmts = module
            .stmts
            .into_iter()
            .map(|stmt| {
                let stmt = self.check_stmt(stmt)?;
                self.subs.clear();
                Ok(stmt)
            })
            .collect::<IsaResult<_>>()?;

        let scope = self.ctx.pop_scope().unwrap();
        self.ctx.extend_module(module.name.ident, scope);
        let typed = Module::new(
            module.no_prelude,
            module.name,
            module.imports,
            stmts,
            module.span,
        );

        Ok(typed)
    }

    fn check_stmt(&mut self, stmt: Stmt<()>) -> IsaResult<Stmt<Ty>> {
        let span = stmt.span;
        match stmt.kind {
            StmtKind::Semi(expr) => {
                let (expr, _) = self.check_expr(expr)?;
                Ok(Stmt::new(StmtKind::Semi(expr), span))
            }

            StmtKind::Type {
                name,
                params,
                constructors,
            } => self.check_type_definition(name, params, constructors, span),

            StmtKind::Alias { name, params, ty } => {
                Ok(Stmt::new(StmtKind::Alias { name, params, ty }, span))
            }

            StmtKind::Val(val) => self.check_val_stmt(val, span),

            StmtKind::Let(bind) => self.check_let_stmt(bind, span),

            StmtKind::Class {
                set,
                name,
                parents,
                signatures,
                defaults,
                ops,
            } => self.check_class(set, name, parents, signatures, ops, defaults, span),

            StmtKind::Instance {
                params,
                set,
                class,
                instance,
                impls,
            } => self.check_instance(params, set, class, instance, impls, span),

            StmtKind::Operator(op) => {
                self.check_operator_stmt(&op)?;
                let kind = StmtKind::Operator(op);

                Ok(Stmt::new(kind, span))
            }
        }
    }

    fn check_expr(&mut self, expr: Expr<()>) -> IsaResult<(Expr<Ty>, Set)> {
        let span = expr.span;
        match expr.kind {
            ExprKind::Int(i) => Ok((Expr::new(ExprKind::Int(i), span, Ty::int()), Set::new())),

            ExprKind::Real(r) => Ok((Expr::new(ExprKind::Real(r), span, Ty::real()), Set::new())),

            ExprKind::Bool(b) => Ok((Expr::new(ExprKind::Bool(b), span, Ty::bool()), Set::new())),

            ExprKind::Char(c) => Ok((Expr::new(ExprKind::Char(c), span, Ty::char()), Set::new())),

            ExprKind::String(s) => {
                let ty = Ty::list(Ty::char());
                Ok((Expr::new(ExprKind::String(s), span, ty), Set::new()))
            }

            ExprKind::Operator(op) => self.check_operator_expr(op, span),

            ExprKind::Path(path) => {
                let (path, ty, set) = Self::check_path(&self.ctx, &mut self.generator, path, span)?;
                Ok((Expr::new(ExprKind::Path(path), span, ty), set))
            }

            ExprKind::Paren(expr) => self.check_expr(*expr),

            ExprKind::Tuple(exprs) => self.check_tuple(exprs, span),

            ExprKind::List(exprs) => self.check_list(exprs, span),

            ExprKind::Infix { op, lhs, rhs } => self.check_infix(op, *lhs, *rhs, span),

            ExprKind::Prefix { op, expr } => self.check_un(op, *expr, span),

            ExprKind::If {
                cond,
                then,
                otherwise,
            } => self.check_if(*cond, *then, *otherwise, span),

            ExprKind::Fn { param, expr } => self.check_fn(param, *expr, span),

            ExprKind::Call { callee, arg } => self.check_call(*callee, *arg, span),

            ExprKind::Let { bind, body } => self.check_let(*bind, *body, span),

            ExprKind::Match { expr, arms } => self.check_match(*expr, arms, span),
        }
    }
}

struct NameResolver<'ctx>(&'ctx Ctx);

impl Rename for NameResolver<'_> {
    fn rename_hi_ty(&self, ty: &mut HiTy) {
        if let HiTyKind::Named(name) = &mut ty.kind
            && let Ok(resolved) = self.0.resolve_type_name(name)
        {
            *name = resolved;
        }
    }

    fn rename_class(&self, name: &mut Path) {
        if let Ok(resolved) = self.0.resolve_class_name(name) {
            *name = resolved;
        }
    }
}

#[derive(Debug, Clone)]
pub struct AliasData {
    params: Box<[TyId]>,
    ty:     HiTy,
}

impl AliasData {
    #[must_use]
    pub const fn new(params: Box<[TyId]>, ty: HiTy) -> Self {
        Self { params, ty }
    }

    #[must_use]
    pub fn params(&self) -> &[TyId] {
        &self.params
    }

    #[must_use]
    pub const fn ty(&self) -> &HiTy {
        &self.ty
    }

    pub fn resolve(aliases: &mut [(Path, Self)]) {
        let mut changed = true;
        while changed {
            let cloned = aliases.to_vec();
            for data in &cloned {
                for (_, alias) in aliases.iter_mut().filter(|(name, _)| name != &data.0) {
                    data.walk_hi_ty(&mut alias.ty);
                }
            }
            changed = aliases
                .iter()
                .zip(cloned)
                .any(|(new, old)| new.1.ty.kind() != old.1.ty.kind());
        }
    }
}

struct AliasRenamer<'a> {
    alias: &'a AliasData,
    args:  &'a [HiTy],
}

impl<'a> AliasRenamer<'a> {
    const fn new(alias: &'a AliasData, args: &'a [HiTy]) -> Self {
        Self { alias, args }
    }
}

impl Rename for AliasRenamer<'_> {
    fn rename_hi_ty(&self, ty: &mut HiTy) {
        if let Some(new) = self
            .alias
            .params()
            .iter()
            .copied()
            .position(|v| ty.kind().as_var().is_some_and(|ty| ty == v))
            .map(|pos| self.args[pos].kind())
        {
            ty.kind = new.clone();
        }
    }
}

impl Rename for (Path, AliasData) {
    fn rename_hi_ty(&self, old: &mut HiTy) {
        if let HiTyKind::Parametric { ty, args } = old.kind()
            && let HiTyKind::Named(name) = ty.kind()
            && name == &self.0
        {
            let mut new = self.1.ty().clone();
            AliasRenamer::new(&self.1, args).walk_hi_ty(&mut new);
            *old = new;
        }
    }
}

impl Rename for Vec<(Path, AliasData)> {
    fn rename_hi_ty(&self, old: &mut HiTy) {
        if let HiTyKind::Parametric { ty, args } = old.kind()
            && let HiTyKind::Named(name) = ty.kind()
            && let Some((_, alias)) = self.iter().find(|(syn, _)| name == syn)
        {
            let mut new = alias.ty().clone();
            AliasRenamer::new(alias, args).walk_hi_ty(&mut new);
            *old = new;
        } else if let HiTyKind::Named(name) = old.kind()
            && let Some((_, alias)) = self.iter().find(|(syn, _)| name == syn)
        {
            let mut new = alias.ty().clone();
            AliasRenamer::new(alias, &[]).walk_hi_ty(&mut new);
            *old = new;
        }
    }
}
