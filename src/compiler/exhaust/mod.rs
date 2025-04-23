pub mod ctor;
pub mod pat;

use std::num::NonZeroUsize;

use ctor::{Ctor, CtorSet, IntRange, MaybeInfinite};
use pat::{PatMatrix, PatMatrixRow, PatOrWild, PatVector, Pattern, WitnessPat};

use super::ast::{Expr, ExprKind, LetBind, ListPat, MatchArm, Pat, PatKind, RangePat, mod_path};
use super::ctx::Ctx as TypeCtx;
use super::error::MatchNonExhaustive;
use super::token::Ident;
use super::types::Ty;
use crate::global::symbol;
use crate::span::Span;

#[derive(Debug)]
pub struct Ctx<'a> {
    ctx: &'a TypeCtx,
}

impl<'a> Ctx<'a> {
    const fn new(ctx: &'a TypeCtx) -> Self {
        Self { ctx }
    }

    fn ctors_for_ty(&self, ty: &Ty) -> CtorSet {
        match ty {
            Ty::Tuple(_) | Ty::Unit => CtorSet::Single,
            Ty::Int => CtorSet::Integers(IntRange::infinite()),
            Ty::Bool => CtorSet::Bool,
            Ty::Char => CtorSet::Integers(IntRange::character()),
            Ty::Scheme { ty, .. } => self.ctors_for_ty(ty),
            Ty::Named { name, .. } => {
                let variants = self.ctx.get_constructors_for_ty(name).len();
                let variants = NonZeroUsize::new(variants).unwrap();
                CtorSet::Type { variants }
            }
            Ty::Fn { .. } | Ty::Var(_) | Ty::Generic { .. } => CtorSet::Unlistable,
        }
    }

    fn ctor_arity(&self, ty: &Ty, ctor: &Ctor) -> usize {
        self.ctor_subtypes(ty, ctor).len()
    }

    fn ctor_subtypes(&self, ty: &Ty, ctor: &Ctor) -> Box<[Ty]> {
        match ctor {
            Ctor::Type(idx) => self.ctx.get_constructor_subtypes(ty, *idx),
            Ctor::Single => self.ctx.get_constructor_subtypes(ty, 0),
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
                let list_ty = ctx.get_constructors_for_ty(&mod_path!(list::List));
                let nil = symbol!("Nil");
                let nil_idx = list_ty.iter().position(|c| c.name.ident == nil).unwrap();
                match list {
                    ListPat::Nil => Self::new(Ctor::Type(nil_idx), Vec::new()),
                    ListPat::Single(pat) => {
                        let pat = Self::from_ast_pat(pat, ctx);
                        let cons = symbol!("Cons");
                        let cons_idx = list_ty.iter().position(|c| c.name.ident == cons).unwrap();
                        let fields =
                            vec![(0, pat), (1, Self::new(Ctor::Type(nil_idx), Vec::new()))];
                        Self::new(Ctor::Type(cons_idx), fields)
                    }
                    ListPat::Cons(pat, pat1) => {
                        let pat = Self::from_ast_pat(pat, ctx);
                        let pat1 = Self::from_ast_pat(pat1, ctx);
                        let cons = symbol!("Cons");
                        let cons_idx = list_ty.iter().position(|c| c.name.ident == cons).unwrap();
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
                let Ty::Named {
                    name: ref ty_name, ..
                } = pat.ty
                else {
                    unreachable!()
                };
                let name = name.base_name();
                let idx = ctx
                    .get_constructors_for_ty(ty_name)
                    .iter()
                    .position(|c| name == c.name)
                    .unwrap();
                Self::new(Ctor::Type(idx), fields)
            }
            PatKind::IntRange(int_range_pat) => Self::new(
                Ctor::IntRange(IntRange::from_int_range_pat(*int_range_pat)),
                Vec::new(),
            ),
            PatKind::CharRange(char_range_pat) => Self::new(
                Ctor::IntRange(IntRange::from_char_range_pat(*char_range_pat)),
                Vec::new(),
            ),
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
    fn check_single_match(&self, expr: &Expr<Ty>) -> Result<(), MatchNonExhaustive> {
        let span = expr.span;
        match &expr.kind {
            ExprKind::Bin { lhs, rhs, .. } => {
                self.check_single_match(lhs)?;
                self.check_single_match(rhs)?;
            }
            ExprKind::Fn { expr, .. }
            | ExprKind::Un { expr, .. }
            | ExprKind::Semi(expr)
            | ExprKind::Let {
                bind: LetBind { expr, .. },
                body: None,
                ..
            } => {
                self.check_single_match(expr)?;
            }
            ExprKind::Let {
                bind: LetBind { expr, .. },
                body: Some(body),
                ..
            } => {
                self.check_single_match(expr)?;
                self.check_single_match(body)?;
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
            ExprKind::Instance { impls, .. }
            | ExprKind::Class {
                defaults: impls, ..
            } => {
                for bind in impls {
                    self.check_single_match(&bind.expr)?;
                }
            }
            ExprKind::List(exprs) | ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.check_single_match(expr)?;
                }
            }

            ExprKind::Int(_)
            | ExprKind::Bool(_)
            | ExprKind::Char(_)
            | ExprKind::Path(_)
            | ExprKind::Val(_)
            | ExprKind::Alias { .. }
            | ExprKind::Type { .. }
            | ExprKind::Operator { .. } => (),
        }

        Ok(())
    }
}

pub fn check_matches(exprs: &[Expr<Ty>], ctx: &TypeCtx) -> Result<(), MatchNonExhaustive> {
    for expr in exprs {
        ctx.check_single_match(expr)?;
    }
    Ok(())
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

    let ctx = Ctx::new(ctx);

    matrix.compute_exhaustiveness(&ctx).single_column()
}
