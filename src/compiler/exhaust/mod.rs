pub mod ctor;
pub mod pat;

use std::num::NonZeroUsize;

use ctor::{Ctor, CtorSet, IntRange, MaybeInfinite};
use pat::{Pat, PatMatrix, PatMatrixRow, PatOrWild, PatVector, WitnessPat};

use super::ast::typed::{TypedExpr, TypedPat, TypedPatKind};
use super::ast::{ExprKind, IntRangePat, MatchArm};
use super::ctx::TypeCtx;
use super::error::MatchNonExhaustive;
use super::types::Ty;

#[derive(Debug)]
pub struct Ctx<'a> {
    ctx: &'a TypeCtx,
}

impl<'a> Ctx<'a> {
    fn new(ctx: &'a TypeCtx) -> Self {
        Self { ctx }
    }

    fn ctors_for_ty(&self, ty: &Ty) -> Option<CtorSet> {
        match ty {
            Ty::Unit => Some(CtorSet::Type {
                variants: NonZeroUsize::new(1).unwrap(),
            }),
            Ty::Int => Some(CtorSet::Integers),
            Ty::Bool => Some(CtorSet::Bool),
            Ty::Scheme { ty, .. } => self.ctors_for_ty(ty),
            Ty::Named { .. } => {
                let variants = self.ctx.get_constructors(ty).len();
                let variants = NonZeroUsize::new(variants)?;
                Some(CtorSet::Type { variants })
            }
            Ty::Var(_) => Some(CtorSet::Unlistable),
            Ty::Fn { .. } => None,
        }
    }

    fn ctor_arity(&self, ty: &Ty, ctor: &Ctor) -> usize {
        self.ctor_subtypes(ty, ctor).len()
    }

    fn ctor_subtypes(&self, ty: &Ty, ctor: &Ctor) -> Box<[Ty]> {
        match ctor {
            Ctor::Type(idx) => self.ctx.get_constructor_subtypes(ty, *idx),
            _ => Box::default(),
        }
    }

    fn split_column_ctors(
        &self,
        ty: &Ty,
        ctors: impl Iterator<Item = &'a Ctor> + Clone,
    ) -> (Vec<Ctor>, Vec<Ctor>) {
        if ctors.clone().any(|c| matches!(c, Ctor::Or)) {
            return (vec![Ctor::Or], vec![]);
        }

        let ctors_for_ty = self.ctors_for_ty(ty).unwrap();

        let (present, missing) = ctors_for_ty.split(ctors);

        let all_missing = present.is_empty();

        let mut split_ctors = present;

        if !missing.is_empty() {
            split_ctors.push(Ctor::Missing);
        }

        let mut missing_ctors = missing;

        if !missing_ctors.is_empty() && all_missing {
            missing_ctors = vec![Ctor::Wildcard];
        } else if missing_ctors.iter().any(ctor::Ctor::is_non_exhaustive) {
            missing_ctors = vec![Ctor::NonExhaustive];
        }

        (split_ctors, missing_ctors)
    }
}

impl Pat {
    fn from_ast_pat(pat: &TypedPat, ctx: &TypeCtx) -> Self {
        match &pat.kind {
            TypedPatKind::Wild | TypedPatKind::Module(_) | TypedPatKind::Ident(_) => {
                Self::new(Ctor::Wildcard, Vec::new())
            }
            TypedPatKind::Or(pats) => {
                let fields = pats
                    .iter()
                    .map(|pat| Self::from_ast_pat(pat, ctx))
                    .enumerate()
                    .collect();
                Self::new(Ctor::Or, fields)
            }
            TypedPatKind::Unit => todo!(),
            TypedPatKind::Int(i) => Self::new(
                Ctor::IntRange(IntRange::from_singleton(MaybeInfinite::Finite(*i))),
                Vec::new(),
            ),
            TypedPatKind::Bool(b) => Self::new(Ctor::Bool(*b), Vec::new()),
            TypedPatKind::Constructor { name, args } => {
                let fields = args
                    .iter()
                    .map(|pat| Self::from_ast_pat(pat, ctx))
                    .enumerate()
                    .collect();
                let idx = ctx
                    .get_constructors(&pat.ty)
                    .iter()
                    .position(|c| c.name == name.ident())
                    .unwrap();
                Self::new(Ctor::Type(idx), fields)
            }
            TypedPatKind::IntRange(int_range_pat) => Self::new(
                Ctor::IntRange(IntRange::from_int_range_pat(*int_range_pat)),
                Vec::new(),
            ),
        }
    }
}

impl IntRange {
    fn from_int_range_pat(range: IntRangePat) -> Self {
        match range {
            IntRangePat::From(i) => Self {
                lo: MaybeInfinite::Finite(i),
                hi: MaybeInfinite::PosInfinity,
            },
            IntRangePat::To(i) => Self {
                lo: MaybeInfinite::NegInfinity,
                hi: MaybeInfinite::Finite(i),
            },
            IntRangePat::ToInclusive(i) => Self {
                lo: MaybeInfinite::NegInfinity,
                hi: MaybeInfinite::Finite(i).plus_one().unwrap(),
            },
            IntRangePat::Exclusive(lo, hi) => Self {
                lo: MaybeInfinite::Finite(lo),
                hi: MaybeInfinite::Finite(hi),
            },
            IntRangePat::Inclusive(lo, hi) => Self {
                lo: MaybeInfinite::Finite(lo),
                hi: MaybeInfinite::Finite(hi).plus_one().unwrap(),
            },
        }
    }
}

impl TypeCtx {
    fn check_single_match(&self, expr: &TypedExpr) -> Result<(), MatchNonExhaustive> {
        let span = expr.span;
        match &expr.kind {
            ExprKind::Bin { lhs, rhs, .. } => {
                self.check_single_match(lhs)?;
                self.check_single_match(rhs)?;
            }
            ExprKind::Fn { expr, .. }
            | ExprKind::Let {
                expr, body: None, ..
            }
            | ExprKind::Un { expr, .. }
            | ExprKind::Semi(expr) => {
                self.check_single_match(expr)?;
            }
            ExprKind::Match { expr, arms } => {
                self.check_single_match(expr)?;

                let ty = expr.ty.clone();
                let typed_pats = arms.iter().map(MatchArm::pat);
                let witnesses = check_match_pats(typed_pats, ty, self);
                if !witnesses.is_empty() {
                    return Err(MatchNonExhaustive::new(witnesses, span));
                }

                for arm in arms.iter().map(MatchArm::expr) {
                    self.check_single_match(arm)?;
                }
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.check_single_match(cond)?;
                self.check_single_match(then)?;
                self.check_single_match(otherwise)?;
            }
            ExprKind::Call { callee, arg } => {
                self.check_single_match(callee)?;
                self.check_single_match(arg)?;
            }

            _ => (),
        }

        Ok(())
    }
}

pub fn check_matches(exprs: &[TypedExpr], ctx: &TypeCtx) -> Result<(), MatchNonExhaustive> {
    for expr in exprs {
        ctx.check_single_match(expr)?;
    }
    Ok(())
}

fn check_match_pats<'a>(
    typed_pats: impl Iterator<Item = &'a TypedPat>,
    ty: Ty,
    ctx: &TypeCtx,
) -> Vec<WitnessPat> {
    let pats = typed_pats
        .map(|p| Pat::from_ast_pat(p, ctx))
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

    let ctx = Ctx::new(ctx);

    matrix.compute_exhaustiveness(&ctx).single_column()
}
