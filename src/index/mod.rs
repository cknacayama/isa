pub mod slice;
pub mod vec;

use std::fmt::Debug;
use std::hash::Hash;
use std::ops;
use std::slice::SliceIndex;

pub use slice::IndexSlice;
pub use vec::IndexVec;

pub trait Idx: Copy + 'static + Eq + PartialEq + Debug + Hash {
    fn new(idx: usize) -> Self;

    fn index(self) -> usize;

    fn increment_by(&mut self, amount: usize) {
        *self = self.plus(amount);
    }

    #[must_use]
    fn plus(self, amount: usize) -> Self {
        Self::new(self.index() + amount)
    }
}

pub trait IntoSliceIdx<I, T: ?Sized> {
    type Output: SliceIndex<T>;
    fn into_slice_idx(self) -> Self::Output;
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for I {
    type Output = usize;

    fn into_slice_idx(self) -> Self::Output {
        self.index()
    }
}

impl<I, T> IntoSliceIdx<I, [T]> for ops::RangeFull {
    type Output = Self;

    fn into_slice_idx(self) -> Self::Output {
        self
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::Range<I> {
    type Output = ops::Range<usize>;

    fn into_slice_idx(self) -> Self::Output {
        ops::Range {
            start: self.start.index(),
            end:   self.end.index(),
        }
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::RangeFrom<I> {
    type Output = ops::RangeFrom<usize>;

    fn into_slice_idx(self) -> Self::Output {
        ops::RangeFrom {
            start: self.start.index(),
        }
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::RangeTo<I> {
    type Output = ops::RangeTo<usize>;

    fn into_slice_idx(self) -> Self::Output {
        ..self.end.index()
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::RangeInclusive<I> {
    type Output = ops::RangeInclusive<usize>;

    fn into_slice_idx(self) -> Self::Output {
        ops::RangeInclusive::new(self.start().index(), self.end().index())
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::RangeToInclusive<I> {
    type Output = ops::RangeToInclusive<usize>;

    fn into_slice_idx(self) -> Self::Output {
        ..=self.end.index()
    }
}
