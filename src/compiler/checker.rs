use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::ast::{
    Constructor, Expr, ExprKind, Fixity, LetBind, ListPat, MatchArm, Module, Operator, Param, Pat,
    PatKind, Path, Stmt, StmtKind, Val,
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
use super::types::{Ty, TyId};
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

    #[must_use]
    pub fn take_ctx(self) -> Ctx {
        self.ctx
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

    fn check_valid_signature(&self, ty: &Ty) -> IsaResult<()> {
        match ty {
            Ty::Generic { args, .. } | Ty::Tuple(args) => args
                .iter()
                .try_for_each(|ty| self.check_valid_signature(ty)),
            Ty::Fn { param, ret } => {
                self.check_valid_signature(param)?;
                self.check_valid_signature(ret)
            }
            Ty::Scheme { ty, .. } => self.check_valid_signature(ty),
            Ty::Named { name, args } => {
                self.ctx.get_ty_data(name)?;
                args.iter()
                    .try_for_each(|ty| self.check_valid_signature(ty))
            }

            Ty::This(_) | Ty::Int | Ty::Bool | Ty::Char | Ty::Real | Ty::Var(_) => Ok(()),
        }
    }

    fn check_valid_type(&self, ty: &Ty, span: Span) -> IsaResult<()> {
        match ty {
            Ty::Generic { args, .. } | Ty::Tuple(args) => args
                .iter()
                .try_for_each(|ty| self.check_valid_type(ty, span)),
            Ty::Fn { param, ret } => {
                self.check_valid_type(param, span)?;
                self.check_valid_type(ret, span)
            }
            Ty::Scheme { ty, .. } => self.check_valid_type(ty, span),
            Ty::Named { name, args } => {
                self.ctx.get_ty_data(name)?;
                args.iter()
                    .try_for_each(|ty| self.check_valid_type(ty, span))
            }

            Ty::This(_) => {
                let fst =
                    DiagnosticLabel::new("`Self` type not allowed outside class definition", span);
                Err(IsaError::new("invalid `Self`", fst, Vec::new()))
            }

            Ty::Int | Ty::Bool | Ty::Char | Ty::Real | Ty::Var(_) => Ok(()),
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
        param: Param<()>,
        expr: Expr<()>,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        self.ctx.push_scope();

        let mut pat = self.check_pat(param.pat)?;
        let pos = self.subs_count();

        let (expr, set) = self.check_expr(expr)?;
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
        callee: Expr<()>,
        arg: Expr<()>,
        span: Span,
    ) -> IsaResult<(Expr<Ty>, Set)> {
        let (mut callee, set) = self.check_expr(callee)?;
        let (mut arg, arg_set) = self.check_expr(arg)?;

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
        bind: LetBind<()>,
        val_decl: Ty,
        mut val_set: Set,
        ty_span: Span,
    ) -> IsaResult<(Ty, Expr<Ty>, Box<[Param<Ty>]>, Set)> {
        self.ctx.push_scope();

        let (val_decl, val_subs) = self.instantiate(val_decl);
        val_set.substitute_many(&val_subs);

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

        self.ctx.assume_constraints(&val_set);

        let (mut expr, set) = if typed_params.is_empty() {
            self.check_expr(bind.expr)?
        } else {
            let pos = self.subs_count();
            let (mut expr, set) = self.check_expr(bind.expr)?;

            let subs = self.subs_from(pos);
            for p in &mut typed_params {
                p.pat.ty.substitute_many(subs);
            }

            expr.ty = Ty::function(typed_params.iter().map(|p| p.pat.ty.clone()), expr.ty);
            (expr, set)
        };

        self.ctx.pop_scope();

        let ty = expr.ty.clone();

        let constr = EqConstraint::new(val_decl.clone(), ty, expr.span);

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
            expr.ty.substitute_many(&subs);
            let ty = self.ctx.generalize(expr.ty.clone());
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

        expr.ty.substitute_many(&subs);
        for p in &mut typed_params {
            p.pat.ty.substitute_many(&subs);
        }

        let ty = self.ctx.generalize(expr.ty.clone());

        Ok((ty, expr, typed_params, val_set))
    }

    fn check_let_bind(
        &mut self,
        bind: LetBind<()>,
    ) -> IsaResult<(Ty, Expr<Ty>, Box<[Param<Ty>]>, Set)> {
        if bind.operator {
            let op = self
                .ctx
                .get_infix(bind.name)
                .or_else(|_| self.ctx.get_prefix(bind.name))?
                .clone();

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
            let var = Ty::Var(var_id);
            self.insert_let(bind.name, var, []);

            let (mut expr, set) = self.check_expr(bind.expr)?;

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
        let ty = body.ty.clone();
        let set = set.concat(body_set);

        let bind = LetBind::new(false, name, params, expr);

        let kind = ExprKind::Let {
            bind: Box::new(bind),
            body: Box::new(body),
        };

        Ok((Expr::new(kind, span, ty), set))
    }

    fn check_constructor(
        &self,
        constructor: Constructor<()>,
        quant: Rc<[TyId]>,
        mut ret: Ty,
    ) -> IsaResult<Constructor<Ty>> {
        for param in constructor.params.iter().rev() {
            ret = Ty::Fn {
                param: Rc::new(param.clone()),
                ret:   Rc::new(ret),
            };
        }
        self.check_valid_type(&ret, constructor.span)?;
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
        params: Box<[Ty]>,
        constructors: Box<[Constructor<()>]>,
        span: Span,
    ) -> IsaResult<Stmt<Ty>> {
        let quant = params
            .iter()
            .map(|p| p.as_var().unwrap())
            .collect::<Rc<_>>();

        let module = Ident::new(self.ctx.current_module().ident, name.span);
        let ty = Ty::Named {
            name: Path::from_two(module, name),
            args: params.clone().into(),
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
            params,
            constructors,
        };

        Ok(Stmt::new(kind, span))
    }

    fn check_operator<const IS_CLASS: bool>(
        &mut self,
        fixity: Fixity,
        prec: u8,
        params: &[Ty],
        set: &Set,
        op: Symbol,
        ty: &Ty,
        span: Span,
    ) -> IsaResult<()> {
        let quant = params
            .iter()
            .map(|p| p.as_var().unwrap())
            .collect::<Rc<_>>();

        if IS_CLASS {
            self.check_valid_signature(ty)?;
        } else {
            self.check_valid_type(ty, span)?;
        }
        let arity = ty.function_arity();
        let ty = if quant.is_empty() {
            ty.clone()
        } else {
            Ty::Scheme {
                quant,
                ty: Rc::new(ty.clone()),
            }
        };

        let data = OperatorData::new(fixity, prec, ty, set.clone(), span);
        let min = fixity.minimum_arity();
        if arity < min {
            let fst = DiagnosticLabel::new("invalid operator type", span);
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
                .map_or(Ok(()), fixity_error)
        } else {
            self.ctx.insert_infix(op, data).map_or(Ok(()), fixity_error)
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
    }

    fn check_val<const IS_CLASS: bool>(&self, val: &mut Val) -> IsaResult<()> {
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

        if IS_CLASS {
            self.check_valid_signature(&val.ty)
        } else {
            self.check_valid_type(&val.ty, val.span)
        }
    }

    fn check_val_stmt(&mut self, mut val: Val, span: Span) -> IsaResult<Stmt<Ty>> {
        self.check_val::<false>(&mut val)?;

        self.ctx.current_mut().unwrap().insert_val(
            val.name.ident,
            VarData::new(val.ty.clone(), val.set.clone(), val.span),
        );

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
        parents: &[Path],
        set: &Set,
        signatures: &mut [Val],
        ops: &mut [Operator],
        defaults: &[LetBind<()>],
    ) -> IsaResult<()> {
        for val in signatures.iter_mut() {
            self.check_val::<true>(val)?;
        }

        let class = Path::from_two(self.ctx.current_module(), name);

        for Operator {
            fixity,
            prec,
            params,
            set,
            op,
            ty,
            span,
        } in ops.iter_mut()
        {
            let var = self.gen_id();
            let mut params = params.to_vec();
            params.push(Ty::Var(var));
            set.push(ClassConstraint::new(class, Ty::Var(var), *span));
            let mut ty = ty.clone();
            ty.substitute_self(&Ty::Var(var));
            self.check_operator::<true>(*fixity, *prec, &params, set, op.ident, &ty, *span)?;
            set.pop();
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

        let op_signatures = ops.iter().map(|op| {
            (
                op.op,
                MemberData {
                    has_default: defaults.iter().any(|bind| bind.name == op.op),
                    set:         op.set.clone(),
                    ty:          op.ty.clone(),
                    span:        op.span,
                },
            )
        });

        self.ctx
            .current_mut()
            .unwrap()
            .get_class_data_mut(name)
            .unwrap()
            .extend_signature(
                val_signatures.chain(op_signatures),
                Box::from(parents),
                set.clone(),
            );

        Ok(())
    }

    fn check_class(
        &mut self,
        set: Set,
        name: Ident,
        parents: Box<[Path]>,
        signatures: Box<[Val]>,
        ops: Box<[Operator]>,
        defaults: Box<[LetBind<()>]>,
        span: Span,
    ) -> IsaResult<Stmt<Ty>> {
        self.ctx.assume_constraints(&set);

        let var = self.gen_id();
        let class = Path::from_two(self.ctx.current_module(), name);
        self.ctx
            .assume_constraints(&Set::from(ClassConstraint::new(class, Ty::Var(var), span)));
        let defaults = self.check_instance_impls(&class, defaults, &Ty::Var(var))?;

        let kind = StmtKind::Class {
            set,
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
        subs: &Ty,
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
                ty.substitute_self(subs);
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
        params: Box<[Ty]>,
        set: Set,
        class: Path,
        instance: Ty,
        impls: Box<[LetBind<()>]>,
        span: Span,
    ) -> IsaResult<Stmt<Ty>> {
        let class_data = self.ctx.get_class(&class)?;

        let quant = params
            .iter()
            .map(|p| p.as_var().unwrap())
            .collect::<Rc<_>>();

        let scheme = if quant.is_empty() {
            instance.clone()
        } else {
            Ty::Scheme {
                quant,
                ty: Rc::new(instance.clone()),
            }
        };
        for parent in class_data.parents() {
            if self.ctx.implementation(&scheme, parent).is_err() {
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

        self.ctx.set_constraints(&class, scheme, set.clone());
        self.ctx.assume_constraints(&set);
        let impls = self.check_instance_impls(&class, impls, &instance)?;

        let kind = StmtKind::Instance {
            params,
            set,
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
            PatKind::Real(r) => Ok(Pat::new(PatKind::Real(r), span, Ty::Real)),
            PatKind::Bool(b) => Ok(Pat::new(PatKind::Bool(b), span, Ty::Bool)),
            PatKind::Char(c) => Ok(Pat::new(PatKind::Char(c), span, Ty::Char)),
            PatKind::Tuple(pats) => {
                if pats.is_empty() {
                    return Ok(Pat::new(
                        PatKind::Tuple(Box::new([])),
                        span,
                        self.ctx.unit(),
                    ));
                }

                let mut types = Vec::new();
                let mut typed_pats = Vec::new();

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

            PatKind::RealRange(range) => Ok(Pat::new(PatKind::RealRange(range), span, Ty::Real)),

            PatKind::CharRange(range) => Ok(Pat::new(PatKind::CharRange(range), span, Ty::Char)),
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

        pat.ty.substitute_many(self.subs_from(count));

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
        match *path.as_slice() {
            [id] => {
                let VarData {
                    ty, mut constrs, ..
                } = ctx.get_var(id)?.clone();
                let (ty, subs) = ty.instantiate(generator);
                constrs.substitute_many(&subs);

                Ok((Path::from_one(id), ty, constrs))
            }

            [first, id] => {
                if let Ok(ty) = ctx.get_constructor(&path) {
                    let (ty, _) = ty.clone().instantiate(generator);
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
                constrs.substitute_many(&subs);

                Ok((Path::from_one(id), ty, constrs))
            }

            [fst, snd, trd] => {
                if let Ok(ty) = ctx.get_constructor(&path) {
                    let (ty, _) = ty.clone().instantiate(generator);
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
        let mut set = data.set().clone();
        for c in &mut set.constrs {
            *c.span_mut() = span;
        }
        let (ty, subs) = self.instantiate(data.ty().clone());
        set.substitute_many(&subs);

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
        let kind = ExprKind::Prefix {
            op,
            expr: Box::new(expr),
        };

        Ok((Expr::new(kind, span, ret), set))
    }

    fn check_list(&mut self, exprs: Box<[Expr<()>]>, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        let mut typed_exprs = Vec::new();
        let id = self.gen_id();

        let mut set = Set::new();
        let mut constrs = Vec::new();

        for expr in exprs {
            let (expr, expr_set) = self.check_expr(expr)?;
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

    fn check_tuple(&mut self, exprs: Box<[Expr<()>]>, span: Span) -> IsaResult<(Expr<Ty>, Set)> {
        if exprs.is_empty() {
            return Ok((
                Expr::new(ExprKind::Tuple(Box::new([])), span, self.ctx.unit()),
                Set::new(),
            ));
        }

        let mut typed_exprs = Vec::new();
        let mut types = Vec::new();
        let mut set = Set::new();

        for expr in exprs {
            let (expr, expr_set) = self.check_expr(expr)?;
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

    fn check_module_types(&mut self, module: &mut Module<()>) -> IsaResult<()> {
        self.ctx.create_module(module.name);
        let mut declared = FxHashMap::default();
        for expr in &mut module.stmts {
            self.check_type_declaration(expr, &mut declared)?;
        }

        Ok(())
    }

    fn substitute_params(&mut self, params: &mut [Ty]) -> (Vec<(Ident, TyId)>, Vec<TyId>) {
        params
            .iter_mut()
            .map(|param| {
                let id = self.gen_id();
                let mut new = Ty::Var(id);
                std::mem::swap(param, &mut new);
                let old = new.get_ident().unwrap();
                ((old, id), id)
            })
            .unzip()
    }

    fn check_type_declaration(
        &mut self,
        stmt: &mut Stmt<()>,
        declared: &mut FxHashMap<Ident, Span>,
    ) -> IsaResult<()> {
        let (name, span) = match &mut stmt.kind {
            StmtKind::Type {
                name,
                params,
                constructors,
            } => {
                let (subs, params) = self.substitute_params(params);

                for ctor in constructors {
                    ctor.substitute_param(&subs);
                }

                self.ctx.insert_ty(*name, params.into())?;

                (*name, stmt.span)
            }
            StmtKind::Val(Val {
                params, set, ty, ..
            }) => {
                let (subs, _) = self.substitute_params(params);

                ty.substitute_param(&subs);
                set.substitute_param(&subs);

                return Ok(());
            }
            StmtKind::Alias { name, params, ty } => {
                let (subs, params) = self.substitute_params(params);

                ty.substitute_param(&subs);

                self.ctx.insert_ty(*name, params.into())?;

                (*name, stmt.span)
            }
            StmtKind::Class {
                name,
                signatures,
                ops,
                ..
            } => {
                for sig in signatures {
                    let (subs, _) = self.substitute_params(&mut sig.params);
                    sig.substitute_param(&subs);
                }
                for op in ops {
                    let (subs, _) = self.substitute_params(&mut op.params);
                    op.substitute_param(&subs);
                }

                let class = ClassData::new(stmt.span);
                let _ = self.ctx.insert_class(name.ident, class);

                (*name, stmt.span)
            }
            StmtKind::Operator(Operator {
                params, set, ty, ..
            }) => {
                let (subs, _) = self.substitute_params(params);

                set.substitute_param(&subs);
                ty.substitute_param(&subs);

                return Ok(());
            }
            StmtKind::Instance {
                params,
                set,
                instance,
                ..
            } => {
                let (subs, _) = self.substitute_params(params);

                set.substitute_param(&subs);
                instance.substitute_param(&subs);

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

                Some(self.check_valid_type(ty, expr.span).map(|()| {
                    let vars = params.iter().map(|param| param.as_var().unwrap()).collect();
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
        constraints.extend(member_set);

        constraints.substitute_self(&Ty::Var(new_var));
        sig.substitute_self(&Ty::Var(new_var));
        constraints.substitute_many(&sig_subs);
        sig.substitute_many(&sig_subs);

        constraints.extend(
            data.parents()
                .iter()
                .map(|class| ClassConstraint::new(*class, Ty::Var(new_var), span)),
        );
        constraints.push(ClassConstraint::new(class, Ty::Var(new_var), span));

        Ok((sig, constraints))
    }

    fn check_for_signatures(&mut self, expr: &mut Stmt<()>) -> IsaResult<()> {
        match &mut expr.kind {
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
                let data = InstanceData::new(set.clone(), expr.span);
                self.check_valid_type(instance, expr.span)?;
                let quant = params
                    .iter()
                    .map(|p| p.as_var().unwrap())
                    .collect::<Rc<_>>();
                let instance = if quant.is_empty() {
                    instance.clone()
                } else {
                    Ty::Scheme {
                        quant,
                        ty: Rc::new(instance.clone()),
                    }
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

                        let span = new_lhs.span.union(new_rhs.span);
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

    fn resolve_signature_names(
        &self,
        set: &mut Set,
        subs: &mut impl Fn(&Ty) -> Option<Ty>,
    ) -> IsaResult<()> {
        for (class, ty) in set.constrs.iter_mut().map(ClassConstraint::get_mut) {
            *class = self.ctx.resolve_class_name(class)?;
            ty.substitute(subs);
        }
        Ok(())
    }

    fn resolve_names(
        &self,
        stmt: &mut StmtKind<()>,
        subs: &mut impl Fn(&Ty) -> Option<Ty>,
    ) -> IsaResult<()> {
        match stmt {
            StmtKind::Semi(_) | StmtKind::Let(_) => (),

            StmtKind::Val(Val { set, ty, .. }) | StmtKind::Operator(Operator { set, ty, .. }) => {
                ty.substitute(subs);
                self.resolve_signature_names(set, subs)?;
            }

            StmtKind::Class {
                set,
                parents,
                signatures,
                ops,
                ..
            } => {
                self.resolve_signature_names(set, subs)?;
                for class in parents {
                    *class = self.ctx.resolve_class_name(class)?;
                }
                for Val { set, ty, .. } in signatures {
                    ty.substitute(subs);
                    self.resolve_signature_names(set, subs)?;
                }
                for Operator { set, ty, .. } in ops {
                    ty.substitute(subs);
                    self.resolve_signature_names(set, subs)?;
                }
            }

            StmtKind::Instance {
                set,
                class,
                instance,
                ..
            } => {
                instance.substitute(subs);
                self.resolve_signature_names(set, subs)?;
                *class = self.ctx.resolve_class_name(class)?;
            }

            StmtKind::Type { constructors, .. } => {
                for c in constructors {
                    c.substitute(subs);
                }
            }

            StmtKind::Alias { ty, .. } => {
                ty.substitute(subs);
            }
        }

        Ok(())
    }

    pub fn check_many_modules(
        &mut self,
        mut modules: Vec<Module<()>>,
    ) -> IsaResult<Vec<Module<Ty>>> {
        for module in &mut modules {
            self.check_module_types(module)?;
        }

        self.resolve_imports(&mut modules);

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
                self.resolve_names(&mut stmt.kind, &mut subs)?;
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

        let mut subs = |ty: &Ty| match ty {
            Ty::Named { name, args } => aliases
                .iter()
                .find_map(|(syn, data)| (name == syn).then(|| data.subs(args))),
            _ => None,
        };

        let mut decl = Vec::new();

        for module in &mut modules {
            self.ctx.set_current_module(module.name);

            for stmt in &mut module.stmts {
                if !aliases.is_empty() {
                    stmt.substitute(&mut subs);
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
            ExprKind::Int(i) => Ok((Expr::new(ExprKind::Int(i), span, Ty::Int), Set::new())),

            ExprKind::Real(r) => Ok((Expr::new(ExprKind::Real(r), span, Ty::Real), Set::new())),

            ExprKind::Bool(b) => Ok((Expr::new(ExprKind::Bool(b), span, Ty::Bool), Set::new())),

            ExprKind::Char(c) => Ok((Expr::new(ExprKind::Char(c), span, Ty::Char), Set::new())),

            ExprKind::String(s) => {
                let ty = Ty::list(Ty::Char);
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
