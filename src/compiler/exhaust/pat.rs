use std::rc::Rc;

use super::Ctx;
use super::ctor::Ctor;
use crate::compiler::ctx::{CtxFmt, TypeCtx};
use crate::compiler::types::Ty;

#[derive(Debug, Clone)]
pub struct WitnessPat {
    ctor:   Ctor,
    fields: Vec<WitnessPat>,
    ty:     Rc<Ty>,
}

impl CtxFmt for &WitnessPat {
    type Ctx = TypeCtx;

    fn ctx_fmt(&self, f: &mut impl std::fmt::Write, ctx: &Self::Ctx) -> std::fmt::Result {
        self.ctor.fmt_fields(f, &self.ty, self.iter_fields(), ctx)
    }
}

impl WitnessPat {
    fn new(ctor: Ctor, fields: Vec<Self>, ty: Rc<Ty>) -> Self {
        Self { ctor, fields, ty }
    }

    fn wildcard(ty: Rc<Ty>) -> Self {
        Self::new(Ctor::Wildcard, Vec::new(), ty)
    }

    fn wild_from_ctor(ctor: Ctor, ty: Rc<Ty>, cx: &mut Ctx) -> Self {
        if matches!(ctor, Ctor::Wildcard) {
            return Self::wildcard(ty);
        }

        let fields = cx
            .ctor_subtypes(&ty, &ctor)
            .into_iter()
            .map(Self::wildcard)
            .collect();

        Self::new(ctor, fields, ty)
    }

    fn iter_fields(&self) -> impl Iterator<Item = &Self> {
        self.fields.iter()
    }
}

#[derive(Debug, Clone)]
pub struct WitnessVector(Vec<WitnessPat>);

impl WitnessVector {
    fn single_pattern(self) -> WitnessPat {
        assert_eq!(self.0.len(), 1);
        self.0.into_iter().next().unwrap()
    }

    fn push_pattern(&mut self, pat: WitnessPat) {
        self.0.push(pat);
    }

    fn apply_constructor(&mut self, ctor: Ctor, ty: Rc<Ty>, ctx: &mut Ctx) {
        let len = self.0.len();
        let arity = ctx.ctor_arity(&ty, &ctor);
        let fields = self.0.drain((len - arity)..).rev().collect();
        self.0.push(WitnessPat::new(ctor, fields, ty));
    }
}

#[derive(Debug, Clone)]
pub struct WitnessMatrix(Vec<WitnessVector>);

impl WitnessMatrix {
    fn empty() -> Self {
        Self(Vec::new())
    }

    fn unit_witness() -> Self {
        Self(vec![WitnessVector(Vec::new())])
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(super) fn single_column(self) -> Vec<WitnessPat> {
        self.0
            .into_iter()
            .map(WitnessVector::single_pattern)
            .collect()
    }

    fn push_pattern(&mut self, pat: &WitnessPat) {
        for witness in &mut self.0 {
            witness.push_pattern(pat.clone());
        }
    }

    fn apply_constructor(
        &mut self,
        ty: &Rc<Ty>,
        missing_ctors: &[Ctor],
        ctor: &Ctor,
        ctx: &mut Ctx,
    ) {
        if self.is_empty() || matches!(ctor, Ctor::Or) {
            return;
        }

        if matches!(ctor, Ctor::Missing) {
            let mut ret = Self::empty();

            for ctor in missing_ctors {
                let pat = WitnessPat::wild_from_ctor(*ctor, ty.clone(), ctx);

                let mut wit_matrix = self.clone();

                wit_matrix.push_pattern(&pat);

                ret.extend(wit_matrix);
            }

            *self = ret;
        } else {
            for mut witness in std::mem::take(&mut self.0) {
                witness.apply_constructor(*ctor, ty.clone(), ctx);
                self.0.push(witness);
            }
        }
    }

    fn extend(&mut self, other: Self) {
        self.0.extend(other.0);
    }
}

#[derive(Debug, Clone)]
pub struct Pat {
    ctor:   Ctor,
    fields: Vec<(usize, Pat)>,
}

impl Pat {
    #[must_use]
    pub(super) fn new(ctor: Ctor, fields: Vec<(usize, Self)>) -> Self {
        Self { ctor, fields }
    }

    #[must_use]
    pub(super) fn specialize(&self, ctor_arity: usize) -> Vec<PatOrWild> {
        let mut fields = (0..ctor_arity).map(|_| PatOrWild::Wild).collect::<Vec<_>>();

        for (i, pat) in &self.fields {
            fields[*i] = PatOrWild::Pat(pat);
        }

        fields
    }

    pub(super) fn ctor(&self) -> &Ctor {
        &self.ctor
    }

    fn is_or_pat(&self) -> bool {
        self.ctor().is_or()
    }

    fn iter_fields(&self) -> impl Iterator<Item = (usize, &Self)> {
        self.fields.iter().map(|(i, pat)| (*i, pat))
    }
}

#[derive(Debug, Clone, Copy)]
pub enum PatOrWild<'a> {
    Wild,
    Pat(&'a Pat),
}

impl<'a> PatOrWild<'a> {
    fn specialize(self, ctor_arity: usize) -> Vec<Self> {
        match self {
            Self::Wild => (0..ctor_arity).map(|_| PatOrWild::Wild).collect(),
            Self::Pat(pat) => pat.specialize(ctor_arity),
        }
    }

    fn expand_or_pat(self) -> Vec<Self> {
        match self {
            PatOrWild::Pat(pat) if pat.is_or_pat() => pat
                .iter_fields()
                .map(|(_, pat)| PatOrWild::Pat(pat))
                .collect(),
            _ => vec![self],
        }
    }

    fn ctor(self) -> &'a Ctor {
        match self {
            Self::Wild => &Ctor::Wildcard,
            Self::Pat(pat) => pat.ctor(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PatVector<'a> {
    pats: Vec<PatOrWild<'a>>,
}

impl<'a> PatVector<'a> {
    pub(super) fn new(pats: Vec<PatOrWild<'a>>) -> Self {
        Self { pats }
    }

    #[must_use]
    pub(super) fn specialize(&self, ctor_arity: usize) -> Self {
        let head = self.head();

        let mut pats = head.specialize(ctor_arity);
        pats.extend_from_slice(&self.pats[1..]);

        Self { pats }
    }

    fn expand_or_pat(&self) -> impl Iterator<Item = PatVector<'a>> {
        self.head().expand_or_pat().into_iter().map(move |pat| {
            let mut new = self.clone();
            new.pats[0] = pat;
            new
        })
    }

    fn head(&self) -> PatOrWild<'a> {
        self.pats[0]
    }
}

#[derive(Debug, Clone)]
pub(super) struct PatMatrixRow<'a> {
    pats:       PatVector<'a>,
    parent_row: usize,
    useful:     bool,
}

impl<'a> PatMatrixRow<'a> {
    pub fn new(pats: PatVector<'a>, parent_row: usize, useful: bool) -> Self {
        Self {
            pats,
            parent_row,
            useful,
        }
    }

    fn head(&self) -> PatOrWild<'a> {
        self.pats.head()
    }

    fn expand_or_pat(&self, parent_row: usize) -> impl Iterator<Item = Self> {
        self.pats.expand_or_pat().map(move |pats| Self {
            pats,
            parent_row,
            useful: false,
        })
    }

    fn specialize(&self, ctor_arity: usize, parent_row: usize) -> Self {
        Self {
            pats: self.pats.specialize(ctor_arity),
            parent_row,
            useful: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct PatMatrix<'a> {
    rows:                     Vec<PatMatrixRow<'a>>,
    pub(super) types:         Vec<Rc<Ty>>,
    wildcard_row_is_relevant: bool,
}

impl Default for PatMatrix<'_> {
    fn default() -> Self {
        Self {
            rows:                     Vec::default(),
            types:                    Vec::default(),
            wildcard_row_is_relevant: true,
        }
    }
}

impl<'a> PatMatrix<'a> {
    fn specialize(&self, ctor: &Ctor, ctx: &mut Ctx, ctor_is_relevant: bool) -> Self {
        if ctor.is_or() {
            let mut matrix = Self {
                rows:                     Vec::new(),
                types:                    self.types.clone(),
                wildcard_row_is_relevant: self.wildcard_row_is_relevant,
            };

            for (i, row) in self.rows.iter().enumerate() {
                for new_row in row.expand_or_pat(i) {
                    matrix.push(new_row);
                }
            }
            matrix
        } else {
            let subtypes = ctx.ctor_subtypes(&self.types[0], ctor);
            let arity = subtypes.len();
            let types = subtypes
                .iter()
                .cloned()
                .chain(self.types[1..].iter().cloned())
                .collect();
            let mut matrix = Self {
                rows: Vec::new(),
                types,
                wildcard_row_is_relevant: self.wildcard_row_is_relevant && ctor_is_relevant,
            };
            for (i, row) in self.rows.iter().enumerate() {
                if ctor.is_covered_by(row.head().ctor()) {
                    let new_row = row.specialize(arity, i);
                    matrix.push(new_row);
                }
            }
            matrix
        }
    }

    fn rows(
        &self,
    ) -> impl Clone + DoubleEndedIterator<Item = &PatMatrixRow<'a>> + ExactSizeIterator {
        self.rows.iter()
    }

    fn rows_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &mut PatMatrixRow<'a>> + ExactSizeIterator {
        self.rows.iter_mut()
    }

    fn heads(&self) -> impl Iterator<Item = PatOrWild<'a>> + Clone {
        self.rows().map(PatMatrixRow::head)
    }

    pub(super) fn push(&mut self, row: PatMatrixRow<'a>) {
        self.rows.push(row);
    }

    fn head_type(&self) -> Option<&Rc<Ty>> {
        self.types.first()
    }

    fn unspecialize(&mut self, specialized: &Self) {
        for child_row in specialized.rows() {
            let parent_row_id = child_row.parent_row;
            let parent_row = &mut self.rows[parent_row_id];
            parent_row.useful |= child_row.useful;
        }
    }

    pub(super) fn compute_exhaustiveness(&mut self, ctx: &mut Ctx) -> WitnessMatrix {
        let Some(ty) = self.head_type().cloned() else {
            let mut useful = true; // Whether the next row is useful.

            for row in self.rows_mut() {
                row.useful = useful;
                useful = false;
            }

            return if useful && self.wildcard_row_is_relevant {
                WitnessMatrix::unit_witness()
            } else {
                WitnessMatrix::empty()
            };
        };

        let ctors = self.heads().map(PatOrWild::ctor);
        let (split_ctors, missing_ctors) = ctx.split_column_ctors(&ty, ctors);

        let mut ret = WitnessMatrix::empty();
        for ctor in split_ctors {
            let ctor_is_relevant = matches!(ctor, Ctor::Missing) || missing_ctors.is_empty();
            let mut spec_matrix = self.specialize(&ctor, ctx, ctor_is_relevant);
            let mut witnesses = spec_matrix.compute_exhaustiveness(ctx);
            witnesses.apply_constructor(&ty, &missing_ctors, &ctor, ctx);
            ret.extend(witnesses);
            self.unspecialize(&spec_matrix);
        }

        ret
    }
}
