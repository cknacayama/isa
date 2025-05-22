use std::ops::BitOr;

use super::ast::{Expr, ExprKind, LetBind, ListPat, MatchArm, Param, Pat, PatKind};
use super::ctx::{Ctx, VarData};
use super::infer::{ClassConstraint, ClassConstraintSet, EqConstraint, EqConstraintSet};
use super::types::{Ty, TyId, TyKind, TySlice};

#[inline]
fn sfold(iter: impl Iterator<Item = bool>) -> bool {
    iter.reduce(BitOr::bitor).unwrap_or(false)
}

pub trait Substitute {
    fn substitute_ty(&self, ty: &mut Ty) -> bool;

    #[inline]
    fn substitute_slice(&self, slice: &mut TySlice) -> bool {
        let mut maybe = slice.to_vec();

        let ret = sfold(maybe.iter_mut().map(|ty| self.walk_ty(ty)));

        if ret {
            *slice = Ty::intern_slice(maybe);
        }

        ret
    }

    fn walk_ty(&self, ty: &mut Ty) -> bool {
        let children = match *ty.kind() {
            TyKind::Tuple(mut ty_slice) => {
                let res = self.substitute_slice(&mut ty_slice);
                if res {
                    *ty = Ty::intern(TyKind::Tuple(ty_slice));
                }
                res
            }
            TyKind::Fn { mut param, mut ret } => {
                let res = self.walk_ty(&mut param) | self.walk_ty(&mut ret);

                if res {
                    *ty = Ty::intern(TyKind::Fn { param, ret });
                }

                res
            }
            TyKind::Scheme {
                quant,
                ty: mut inner,
            } => {
                let res = self.walk_ty(&mut inner);
                if res {
                    *ty = Ty::intern(TyKind::Scheme { quant, ty: inner });
                }
                res
            }
            TyKind::Named { name, mut args } => {
                let res = self.substitute_slice(&mut args);
                if res {
                    *ty = Ty::intern(TyKind::Named { name, args });
                }
                res
            }
            TyKind::Generic { var, mut args } => {
                let res = self.substitute_slice(&mut args);
                if res {
                    *ty = Ty::intern(TyKind::Generic { var, args });
                }
                res
            }
            TyKind::This(mut ty_slice) => {
                let res = self.substitute_slice(&mut ty_slice);
                if res {
                    *ty = Ty::intern(TyKind::This(ty_slice));
                }
                res
            }

            TyKind::Int | TyKind::Bool | TyKind::Char | TyKind::Real | TyKind::Var(_) => false,
        };

        self.substitute_ty(ty) | children
    }

    fn substitute_match_arm(&self, arm: &mut MatchArm<Ty>) -> bool {
        self.substitute_pat(&mut arm.pat) | self.substitute_expr(&mut arm.expr)
    }

    fn substitute_expr(&self, expr: &mut Expr<Ty>) -> bool {
        let children = match &mut expr.kind {
            ExprKind::Let { bind, body } => self.substitute_bind(bind) | self.substitute_expr(body),
            ExprKind::Fn { param, expr } => {
                self.substitute_param(param) | self.substitute_expr(expr)
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.substitute_expr(cond)
                    | self.substitute_expr(then)
                    | self.substitute_expr(otherwise)
            }

            ExprKind::Call { callee, arg } => {
                self.substitute_expr(callee) | self.substitute_expr(arg)
            }
            ExprKind::Match { expr, arms } => {
                self.substitute_expr(expr)
                    | sfold(arms.iter_mut().map(|arm| self.substitute_match_arm(arm)))
            }

            ExprKind::List(exprs) | ExprKind::Tuple(exprs) => {
                sfold(exprs.iter_mut().map(|expr| self.substitute_expr(expr)))
            }
            ExprKind::Infix { lhs, rhs, .. } => {
                self.substitute_expr(lhs) | self.substitute_expr(rhs)
            }
            ExprKind::Prefix { expr, .. } | ExprKind::Paren(expr) => self.substitute_expr(expr),

            ExprKind::Operator(_)
            | ExprKind::Int(_)
            | ExprKind::Real(_)
            | ExprKind::String(_)
            | ExprKind::Bool(_)
            | ExprKind::Char(_)
            | ExprKind::Path(_) => false,
        };

        self.walk_ty(&mut expr.ty) | children
    }

    fn substitute_list(&self, list: &mut ListPat<Ty>) -> bool {
        match list {
            ListPat::Nil => false,
            ListPat::Single(pat) => self.substitute_pat(pat),
            ListPat::Cons(pat, rest) => self.substitute_pat(pat) | self.substitute_pat(rest),
        }
    }

    fn substitute_param(&self, param: &mut Param<Ty>) -> bool {
        self.substitute_pat(&mut param.pat)
    }

    fn substitute_pat(&self, pat: &mut Pat<Ty>) -> bool {
        let children = match &mut pat.kind {
            PatKind::Tuple(args) | PatKind::Or(args) | PatKind::Constructor { args, .. } => {
                sfold(args.iter_mut().map(|pat| self.substitute_pat(pat)))
            }

            PatKind::List(list) => self.substitute_list(list),

            PatKind::Wild
            | PatKind::Int(_)
            | PatKind::Bool(_)
            | PatKind::Ident(_)
            | PatKind::Real(_)
            | PatKind::Char(_)
            | PatKind::IntRange(_)
            | PatKind::CharRange(_)
            | PatKind::RealRange(_) => false,
        };

        self.walk_ty(&mut pat.ty) | children
    }

    fn substitute_bind(&self, bind: &mut LetBind<Ty>) -> bool {
        sfold(
            bind.params
                .iter_mut()
                .map(|param| self.substitute_param(param)),
        ) | self.substitute_expr(&mut bind.expr)
    }

    fn substitute_class_constr(&self, constr: &mut ClassConstraint) -> bool {
        self.walk_ty(&mut constr.ty)
    }

    fn substitute_eq_constr(&self, constr: &mut EqConstraint) -> bool {
        self.walk_ty(&mut constr.lhs) | self.walk_ty(&mut constr.rhs)
    }

    fn substitute_class_set(&self, set: &mut ClassConstraintSet) -> bool {
        sfold(
            set.iter_mut()
                .map(|constr| self.substitute_class_constr(constr)),
        )
    }

    fn substitute_eq_set(&self, set: &mut EqConstraintSet) -> bool {
        sfold(
            set.iter_mut()
                .map(|constr| self.substitute_eq_constr(constr)),
        )
    }

    fn substitute_var_data(&self, var: &mut VarData) -> bool {
        self.walk_ty(&mut var.ty) | self.substitute_class_set(&mut var.constrs)
    }

    fn substitute_ctx(&self, ctx: &mut Ctx) -> bool {
        let mut res = false;
        // We can skip the first scope
        // because you do not access type
        // variables from these binds
        // due to instantiation
        for env in &mut ctx.env_mut()[1..] {
            res |= sfold(env.values_mut().map(|var| self.substitute_var_data(var)));
        }
        res
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Subs {
    old:  TyId,
    subs: Ty,
}

impl Subs {
    #[must_use]
    pub const fn new(old: TyId, new: Ty) -> Self {
        Self { old, subs: new }
    }

    #[must_use]
    pub const fn old(&self) -> TyId {
        self.old
    }

    #[must_use]
    pub const fn subs(&self) -> Ty {
        self.subs
    }
}

impl Substitute for Subs {
    fn substitute_ty(&self, ty: &mut Ty) -> bool {
        match *ty.kind() {
            TyKind::Var(id) if id == self.old => {
                *ty = self.subs;
                true
            }
            TyKind::Generic { var, args } if var == self.old => match *self.subs.kind() {
                TyKind::Var(var) => {
                    *ty = Ty::intern(TyKind::Generic { var, args });
                    true
                }
                TyKind::Named { name, args: named } => {
                    let mut named = named.to_vec();
                    named.extend_from_slice(&args);
                    *ty = Ty::intern(TyKind::Named {
                        name,
                        args: Ty::intern_slice(named),
                    });
                    true
                }
                TyKind::Generic { var, args: generic } => {
                    let mut generic = generic.to_vec();
                    generic.extend_from_slice(&args);
                    *ty = Ty::intern(TyKind::Generic {
                        var,
                        args: Ty::intern_slice(generic),
                    });
                    true
                }
                _ => false,
            },
            _ => false,
        }
    }
}

impl Substitute for [Subs] {
    fn substitute_ty(&self, ty: &mut Ty) -> bool {
        sfold(self.iter().map(|s| s.walk_ty(ty)))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SelfSub(Ty);

impl SelfSub {
    #[must_use] pub const fn new(ty: Ty) -> Self {
        Self(ty)
    }
}

impl Substitute for SelfSub {
    fn substitute_ty(&self, ty: &mut Ty) -> bool {
        match *ty.kind() {
            TyKind::This(args) if args.is_empty() => {
                *ty = self.0;
                true
            }
            TyKind::This(args) => match *self.0.kind() {
                TyKind::Var(var) => {
                    *ty = Ty::intern(TyKind::Generic { var, args });
                    true
                }

                TyKind::Named { name, args: named } => {
                    let mut named = named.to_vec();
                    named.extend_from_slice(&args);
                    *ty = Ty::intern(TyKind::Named {
                        name,
                        args: Ty::intern_slice(named),
                    });
                    true
                }
                TyKind::Generic { var, args: generic } => {
                    let mut generic = generic.to_vec();
                    generic.extend_from_slice(&args);
                    *ty = Ty::intern(TyKind::Generic {
                        var,
                        args: Ty::intern_slice(generic),
                    });
                    true
                }
                _ => false,
            },
            _ => false,
        }
    }
}
