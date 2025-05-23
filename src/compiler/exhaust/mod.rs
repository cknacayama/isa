pub mod ctor;
pub mod pat;

use std::num::NonZeroUsize;

use ctor::{Ctor, CtorSet, IntRange, MaybeInfinite, RealRange};
use pat::{PatMatrix, PatMatrixRow, PatOrWild, PatVector, Pattern, WitnessPat};

use super::ast::{
    Expr, ExprKind, ListPat, MatchArm, Operator, Pat, PatKind, RangePat, Stmt, StmtKind,
};
use super::ctx::Ctx as TypeCtx;
use super::error::MatchNonExhaustive;
use super::types::{Ty, TyKind, TySlice};
use crate::global::{Symbol, ty_path};

#[derive(Debug)]
pub struct Ctx<'a> {
    ctx: &'a TypeCtx,
}

impl<'a> Ctx<'a> {
    fn ctors_for_ty(&self, ty: Ty) -> CtorSet {
        match ty.kind() {
            TyKind::Tuple(_) => CtorSet::Single,
            TyKind::Int => CtorSet::Integers(IntRange::infinite()),
            TyKind::Bool => CtorSet::Bool,
            TyKind::Char => CtorSet::Integers(IntRange::character()),
            TyKind::Scheme { ty, .. } => self.ctors_for_ty(*ty),
            TyKind::Named { name, .. } => {
                let variants = self.ctx.get_constructors_for_ty(*name).len();
                let variants = NonZeroUsize::new(variants).unwrap();
                CtorSet::Type { variants }
            }
            TyKind::Real | TyKind::Fn { .. } | TyKind::Var(_) | TyKind::Generic { .. } => {
                CtorSet::Unlistable
            }
            TyKind::This(_) => unreachable!(),
        }
    }

    fn ctor_subtypes(&self, ty: Ty, ctor: &Ctor) -> TySlice {
        match ctor {
            Ctor::Type(idx) => self.ctx.get_constructor_subtypes(ty, *idx),
            Ctor::Single => self.ctx.get_constructor_subtypes(ty, 0),
            _ => Ty::empty_slice(),
        }
    }

    fn split_column_ctors(
        &self,
        ty: Ty,
        ctors: impl Iterator<Item = &'a Ctor> + Clone,
    ) -> (Vec<Ctor>, Vec<Ctor>) {
        if ctors.clone().any(|c| matches!(c, Ctor::Or)) {
            return (vec![Ctor::Or], vec![]);
        }

        let ctors_for_ty = self.ctors_for_ty(ty);

        let (present, missing) = ctors_for_ty.split(ctors);

        let all_missing = present.is_empty();

        let mut split_ctors = present;

        if !missing.is_empty() {
            split_ctors.push(Ctor::Missing);
        }

        let mut missing_ctors = missing;

        if !missing_ctors.is_empty() && all_missing {
            missing_ctors = vec![Ctor::Wildcard];
        } else if missing_ctors.iter().any(Ctor::is_non_exhaustive) {
            missing_ctors = vec![Ctor::NonExhaustive];
        }

        (split_ctors, missing_ctors)
    }
}

impl Pattern {
    fn from_ast_pat(pat: &Pat<Ty>, ctx: &TypeCtx) -> Self {
        match &pat.kind {
            PatKind::List(list) => {
                let list_ty = ctx.get_constructors_for_ty(ty_path!(list::List));
                let nil = Symbol::intern("Nil");
                let nil_idx = list_ty.iter().position(|c| c.name().ident == nil).unwrap();
                match list {
                    ListPat::Nil => Self::new(Ctor::Type(nil_idx), Vec::new()),
                    ListPat::Single(pat) => {
                        let pat = Self::from_ast_pat(pat, ctx);
                        let cons = Symbol::intern("Cons");
                        let cons_idx = list_ty.iter().position(|c| c.name().ident == cons).unwrap();
                        let fields =
                            vec![(0, pat), (1, Self::new(Ctor::Type(nil_idx), Vec::new()))];
                        Self::new(Ctor::Type(cons_idx), fields)
                    }
                    ListPat::Cons(pat, pat1) => {
                        let pat = Self::from_ast_pat(pat, ctx);
                        let pat1 = Self::from_ast_pat(pat1, ctx);
                        let cons = Symbol::intern("Cons");
                        let cons_idx = list_ty.iter().position(|c| c.name().ident == cons).unwrap();
                        let fields = vec![(0, pat), (1, pat1)];
                        Self::new(Ctor::Type(cons_idx), fields)
                    }
                }
            }
            PatKind::Wild | PatKind::Ident(_) => Self::new(Ctor::Wildcard, Vec::new()),
            PatKind::Or(pats) => {
                let fields = pats
                    .iter()
                    .map(|pat| Self::from_ast_pat(pat, ctx))
                    .enumerate()
                    .collect();
                Self::new(Ctor::Or, fields)
            }
            PatKind::Tuple(pats) => {
                let fields = pats
                    .iter()
                    .map(|pat| Self::from_ast_pat(pat, ctx))
                    .enumerate()
                    .collect();
                Self::new(Ctor::Single, fields)
            }
            PatKind::Int(i) => Self::new(
                Ctor::IntRange(IntRange::from_singleton(MaybeInfinite::Finite(*i))),
                Vec::new(),
            ),
            PatKind::Real(i) => {
                Self::new(Ctor::RealRange(RealRange::inclusive(*i, *i)), Vec::new())
            }
            PatKind::Char(c) => Self::new(
                Ctor::IntRange(IntRange::from_singleton(MaybeInfinite::Finite(i64::from(
                    *c,
                )))),
                Vec::new(),
            ),
            PatKind::Bool(b) => Self::new(Ctor::Bool(*b), Vec::new()),
            PatKind::Constructor { name, args } => {
                let fields = args
                    .iter()
                    .map(|pat| Self::from_ast_pat(pat, ctx))
                    .enumerate()
                    .collect();
                let TyKind::Named { name: ty_name, .. } = pat.ty.kind() else {
                    unreachable!()
                };
                let name = name.base_name();
                let idx = ctx
                    .get_constructors_for_ty(*ty_name)
                    .iter()
                    .position(|c| name == c.name())
                    .unwrap();
                Self::new(Ctor::Type(idx), fields)
            }
            PatKind::IntRange(int_range_pat) => Self::new(
                Ctor::IntRange(IntRange::from_int_range_pat(*int_range_pat)),
                Vec::new(),
            ),
            PatKind::RealRange(range) => Self::new(
                Ctor::RealRange(RealRange::from_range_pat(*range)),
                Vec::new(),
            ),
            PatKind::CharRange(char_range_pat) => Self::new(
                Ctor::IntRange(IntRange::from_char_range_pat(*char_range_pat)),
                Vec::new(),
            ),
        }
    }
}

impl RealRange {
    const fn from_range_pat(range: RangePat<f64>) -> Self {
        match range {
            RangePat::From(lo) => Self::exclusive(lo, f64::INFINITY),
            RangePat::To(hi) => Self::exclusive(f64::NEG_INFINITY, hi),
            RangePat::ToInclusive(hi) => Self::inclusive(f64::NEG_INFINITY, hi),
            RangePat::Exclusive(lo, hi) => Self::exclusive(lo, hi),
            RangePat::Inclusive(lo, hi) => Self::inclusive(lo, hi),
        }
    }
}

impl IntRange {
    fn from_char_range_pat(range: RangePat<u8>) -> Self {
        match range {
            RangePat::From(i) => Self {
                lo: MaybeInfinite::Finite(i64::from(i)),
                hi: MaybeInfinite::Finite(i64::from(u8::MAX)),
            },
            RangePat::To(i) => Self {
                lo: MaybeInfinite::Finite(0),
                hi: MaybeInfinite::Finite(i64::from(i)),
            },
            RangePat::ToInclusive(i) => Self {
                lo: MaybeInfinite::Finite(0),
                hi: MaybeInfinite::Finite(i64::from(i)).plus_one(),
            },
            RangePat::Exclusive(lo, hi) => Self {
                lo: MaybeInfinite::Finite(i64::from(lo)),
                hi: MaybeInfinite::Finite(i64::from(hi)),
            },
            RangePat::Inclusive(lo, hi) => Self {
                lo: MaybeInfinite::Finite(i64::from(lo)),
                hi: MaybeInfinite::Finite(i64::from(hi)).plus_one(),
            },
        }
    }

    fn from_int_range_pat(range: RangePat<i64>) -> Self {
        match range {
            RangePat::From(i) => Self {
                lo: MaybeInfinite::Finite(i),
                hi: MaybeInfinite::PosInfinity,
            },
            RangePat::To(i) => Self {
                lo: MaybeInfinite::NegInfinity,
                hi: MaybeInfinite::Finite(i),
            },
            RangePat::ToInclusive(i) => Self {
                lo: MaybeInfinite::NegInfinity,
                hi: MaybeInfinite::Finite(i).plus_one(),
            },
            RangePat::Exclusive(lo, hi) => Self {
                lo: MaybeInfinite::Finite(lo),
                hi: MaybeInfinite::Finite(hi),
            },
            RangePat::Inclusive(lo, hi) => Self {
                lo: MaybeInfinite::Finite(lo),
                hi: MaybeInfinite::Finite(hi).plus_one(),
            },
        }
    }
}

impl TypeCtx {
    fn check_single_match_stmt(&self, stmt: &Stmt<Ty>, errors: &mut Vec<MatchNonExhaustive>) {
        match &stmt.kind {
            StmtKind::Semi(expr) => {
                self.check_single_match_expr(expr, errors);
            }
            StmtKind::Instance { impls, .. }
            | StmtKind::Class {
                defaults: impls, ..
            } => {
                for bind in impls {
                    self.check_single_match_expr(&bind.expr, errors);
                }
            }
            StmtKind::Let(bind) => {
                for p in &bind.params {
                    let ty = p.pat.ty;
                    let witnesses = check_match_pats(std::iter::once(&p.pat), ty, self);
                    if !witnesses.is_empty() {
                        errors.push(MatchNonExhaustive::new(witnesses, p.pat.span));
                    }
                }
                self.check_single_match_expr(&bind.expr, errors);
            }

            StmtKind::Val(_)
            | StmtKind::Alias { .. }
            | StmtKind::Type { .. }
            | StmtKind::Operator(Operator { .. }) => (),
        }
    }

    fn check_single_match_expr(&self, expr: &Expr<Ty>, errors: &mut Vec<MatchNonExhaustive>) {
        let span = expr.span;
        match &expr.kind {
            ExprKind::Infix { lhs, rhs, .. } => {
                self.check_single_match_expr(lhs, errors);
                self.check_single_match_expr(rhs, errors);
            }
            ExprKind::Paren(expr) | ExprKind::Prefix { expr, .. } => {
                self.check_single_match_expr(expr, errors);
            }
            ExprKind::Fn { param, expr } => {
                let ty = param.pat.ty;
                let witnesses = check_match_pats(std::iter::once(&param.pat), ty, self);
                if !witnesses.is_empty() {
                    errors.push(MatchNonExhaustive::new(witnesses, param.pat.span));
                }
                self.check_single_match_expr(expr, errors);
            }

            ExprKind::Let { bind, body, .. } => {
                for p in &bind.params {
                    let ty = p.pat.ty;
                    let witnesses = check_match_pats(std::iter::once(&p.pat), ty, self);
                    if !witnesses.is_empty() {
                        errors.push(MatchNonExhaustive::new(witnesses, p.pat.span));
                    }
                }
                self.check_single_match_expr(&bind.expr, errors);
                self.check_single_match_expr(body, errors);
            }
            ExprKind::Match { expr, arms } => {
                self.check_single_match_expr(expr, errors);

                let ty = expr.ty;
                let typed_pats = arms.iter().map(MatchArm::pat);
                let witnesses = check_match_pats(typed_pats, ty, self);
                if !witnesses.is_empty() {
                    errors.push(MatchNonExhaustive::new(witnesses, span));
                }

                for arm in arms.iter().map(MatchArm::expr) {
                    self.check_single_match_expr(arm, errors);
                }
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.check_single_match_expr(cond, errors);
                self.check_single_match_expr(then, errors);
                self.check_single_match_expr(otherwise, errors);
            }
            ExprKind::Call { callee, arg } => {
                self.check_single_match_expr(callee, errors);
                self.check_single_match_expr(arg, errors);
            }
            ExprKind::List(exprs) | ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.check_single_match_expr(expr, errors);
                }
            }

            ExprKind::Operator(_)
            | ExprKind::Int(_)
            | ExprKind::Real(_)
            | ExprKind::String(_)
            | ExprKind::Bool(_)
            | ExprKind::Char(_)
            | ExprKind::Path(_) => (),
        }
    }
}

pub fn check_matches(stmts: &[Stmt<Ty>], ctx: &TypeCtx) -> Result<(), Vec<MatchNonExhaustive>> {
    let mut errors = Vec::new();

    for stmt in stmts {
        ctx.check_single_match_stmt(stmt, &mut errors);
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn check_match_pats<'a>(
    typed_pats: impl Iterator<Item = &'a Pat<Ty>>,
    ty: Ty,
    ctx: &TypeCtx,
) -> Vec<WitnessPat> {
    let pats = typed_pats
        .map(|p| Pattern::from_ast_pat(p, ctx))
        .collect::<Vec<_>>();

    let mut matrix = PatMatrix::default();
    matrix.types.push(ty);

    for (i, p) in pats
        .iter()
        .map(|p| match p.ctor() {
            Ctor::Wildcard => PatOrWild::Wild,
            _ => PatOrWild::Pat(p),
        })
        .enumerate()
    {
        let row = PatMatrixRow::new(PatVector::new(vec![p]), i, false);
        matrix.push(row);
    }

    let ctx = Ctx { ctx };

    matrix.compute_exhaustiveness(&ctx).single_column()
}
