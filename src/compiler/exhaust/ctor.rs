use std::fmt;
use std::num::NonZeroUsize;

use crate::compiler::ctx::{CtxFmt, TypeCtx};
use crate::compiler::types::Ty;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ctor {
    Single,
    Type(usize),
    Bool(bool),
    IntRange(IntRange),
    Missing,
    Or,
    Wildcard,
    NonExhaustive,
}

impl Ctor {
    pub(super) fn is_covered_by(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Wildcard) | (Self::Single, Self::Single) => true,
            (Self::Type(self_id), Self::Type(other_id)) => self_id == other_id,
            (Self::Bool(self_b), Self::Bool(other_b)) => self_b == other_b,
            (Self::IntRange(self_range), Self::IntRange(other_range)) => {
                self_range.is_subrange(other_range)
            }
            _ => false,
        }
    }

    pub(super) const fn is_or(&self) -> bool {
        matches!(self, Self::Or)
    }

    const fn as_type(&self) -> Option<usize> {
        if let Self::Type(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    const fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    const fn as_int_range(&self) -> Option<&IntRange> {
        if let Self::IntRange(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub(super) fn fmt_fields(
        &self,
        f: &mut impl fmt::Write,
        ty: &Ty,
        fields: impl ExactSizeIterator<Item = impl CtxFmt<Ctx = TypeCtx>>,
        ctx: &TypeCtx,
    ) -> fmt::Result {
        let mut first = true;
        let mut start_or_continue = |s| {
            if first {
                first = false;
                ""
            } else {
                s
            }
        };

        match self {
            Self::Single => {
                write!(f, "(")?;
                for p in fields {
                    write!(f, "{}", start_or_continue(", "))?;
                    p.ctx_simple_fmt(f, ctx)?;
                }
                write!(f, ")")?;
            }
            Self::Type(idx) => {
                ctx.write_variant_name(f, ty, *idx)?;
                if fields.len() > 0 {
                    for p in fields {
                        write!(f, " ")?;
                        p.ctx_simple_fmt(f, ctx)?;
                    }
                }
            }
            Self::Bool(b) => write!(f, "{b}")?,
            Self::IntRange(IntRange { lo, hi }) if ty.is_char() => write!(
                f,
                "{:?}..{:?}",
                lo.as_finite()
                    .map(|i| <i64 as TryInto<u8>>::try_into(i).unwrap() as char)
                    .unwrap(),
                hi.as_finite()
                    .map(|i| <i64 as TryInto<u8>>::try_into(i).unwrap() as char)
                    .unwrap(),
            )?,
            Self::IntRange(range) => write!(f, "{range}")?,
            Self::Or => {
                for pat in fields {
                    write!(f, "{}", start_or_continue(" | "))?;
                    pat.ctx_fmt(f, ctx)?;
                }
            }
            _ => write!(f, "_")?,
        }
        Ok(())
    }

    /// Returns `true` if the ctor is [`NonExhaustive`].
    ///
    /// [`NonExhaustive`]: Ctor::NonExhaustive
    #[must_use]
    pub const fn is_non_exhaustive(&self) -> bool {
        matches!(self, Self::NonExhaustive)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MaybeInfinite {
    NegInfinity,
    Finite(i64),
    PosInfinity,
}

impl MaybeInfinite {
    #[must_use]
    pub(super) fn plus_one(self) -> Self {
        match self {
            Self::Finite(n) => n.checked_add(1).map_or(Self::PosInfinity, Self::Finite),
            x => x,
        }
    }

    const fn as_finite(&self) -> Option<i64> {
        if let Self::Finite(v) = self {
            Some(*v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntRange {
    pub lo: MaybeInfinite,
    pub hi: MaybeInfinite,
}

impl IntRange {
    fn is_subrange(&self, other: &Self) -> bool {
        other.lo <= self.lo && self.hi <= other.hi
    }

    pub(super) const fn infinite() -> Self {
        Self {
            lo: MaybeInfinite::NegInfinity,
            hi: MaybeInfinite::PosInfinity,
        }
    }

    pub(super) const fn character() -> Self {
        Self {
            lo: MaybeInfinite::Finite(0),
            hi: MaybeInfinite::Finite(u8::MAX as i64),
        }
    }

    pub(super) fn from_singleton(x: MaybeInfinite) -> Self {
        Self {
            lo: x,
            hi: x.plus_one(),
        }
    }

    fn intersection(&self, other: &Self) -> Option<Self> {
        if self.lo < other.hi && other.lo < self.hi {
            Some(Self {
                lo: std::cmp::max(self.lo, other.lo),
                hi: std::cmp::min(self.hi, other.hi),
            })
        } else {
            None
        }
    }

    fn split(
        &self,
        column_ranges: impl Iterator<Item = Self>,
    ) -> impl Iterator<Item = (bool, Self)> {
        let mut boundaries: Vec<(MaybeInfinite, isize)> = column_ranges
            .filter_map(|r| self.intersection(&r))
            .flat_map(|r| [(r.lo, 1), (r.hi, -1)])
            .collect();

        boundaries.sort_unstable();

        let mut paren_counter = 0isize;

        let mut prev_bdy = self.lo;

        boundaries
            .into_iter()
            .chain(std::iter::once((self.hi, 0)))
            .map(move |(bdy, delta)| {
                let ret = (prev_bdy, paren_counter, bdy);
                prev_bdy = bdy;
                paren_counter += delta;
                ret
            })
            .filter(|&(prev_bdy, _, bdy)| prev_bdy != bdy)
            .map(move |(prev_bdy, paren_count, bdy)| {
                let presence = paren_count > 0;

                let range = Self {
                    lo: prev_bdy,
                    hi: bdy,
                };

                (presence, range)
            })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtorSet {
    Single,
    Type { variants: NonZeroUsize },
    Integers(IntRange),
    Bool,
    Unlistable,
}

impl CtorSet {
    pub(super) fn split<'a>(
        &self,
        ctors: impl Iterator<Item = &'a Ctor>,
    ) -> (Vec<Ctor>, Vec<Ctor>) {
        let mut present = Vec::new();
        let mut missing = Vec::new();
        let mut seen = Vec::new();

        for ctor in ctors.copied() {
            match ctor {
                Ctor::Wildcard => {} // discard wildcards
                _ => seen.push(ctor),
            }
        }

        match self {
            Self::Single => {
                if seen.is_empty() {
                    missing.push(Ctor::Single);
                } else {
                    present.push(Ctor::Single);
                }
            }
            Self::Type { variants } => {
                let variants = variants.get();
                let mut seen_set = vec![false; variants];

                for idx in seen.iter().filter_map(Ctor::as_type) {
                    seen_set[idx] = true;
                }

                for (idx, seen) in seen_set.iter().copied().enumerate() {
                    let ctor = Ctor::Type(idx);

                    if seen {
                        present.push(ctor);
                    } else {
                        missing.push(ctor);
                    }
                }
            }
            Self::Integers(range) => {
                let seen_ranges = seen.iter().filter_map(Ctor::as_int_range).copied();

                for (seen, splitted_range) in range.split(seen_ranges) {
                    if seen {
                        present.push(Ctor::IntRange(splitted_range));
                    } else {
                        missing.push(Ctor::IntRange(splitted_range));
                    }
                }
            }
            Self::Bool => {
                let mut seen_false = false;
                let mut seen_true = false;
                for b in seen.iter().filter_map(Ctor::as_bool) {
                    if b {
                        seen_true = true;
                    } else {
                        seen_false = true;
                    }
                }
                if seen_false {
                    present.push(Ctor::Bool(false));
                } else {
                    missing.push(Ctor::Bool(false));
                }
                if seen_true {
                    present.push(Ctor::Bool(true));
                } else {
                    missing.push(Ctor::Bool(true));
                }
            }
            Self::Unlistable => {
                present.extend(seen);
                missing.push(Ctor::NonExhaustive);
            }
        }

        (present, missing)
    }
}

impl fmt::Display for IntRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(lo) = self.lo.as_finite() {
            write!(f, "{lo}")?;
        }
        write!(f, "..")?;
        if let Some(hi) = self.hi.as_finite() {
            write!(f, "{hi}")?;
        }

        Ok(())
    }
}
