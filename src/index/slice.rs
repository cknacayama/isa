use std::fmt;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};
use std::slice::{self, SliceIndex};

use super::{Idx, IndexVec, IntoSliceIdx};

#[derive(PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct IndexSlice<I: Idx, T> {
    _marker: PhantomData<fn(&I)>,
    pub raw: [T],
}

impl<I: Idx, T> IndexSlice<I, T> {
    #[must_use]
    pub const fn empty<'a>() -> &'a Self {
        Self::from_raw(&[])
    }

    #[allow(unsafe_code)]
    pub const fn from_raw(raw: &[T]) -> &Self {
        let ptr: *const [T] = raw;
        // SAFETY: `IndexSlice` is `repr(transparent)` over a normal slice
        unsafe { &*(ptr as *const Self) }
    }

    #[allow(unsafe_code)]
    pub fn from_raw_mut(raw: &mut [T]) -> &mut Self {
        let ptr: *mut [T] = raw;
        // SAFETY: `IndexSlice` is `repr(transparent)` over a normal slice
        unsafe { &mut *(ptr as *mut Self) }
    }

    pub const fn len(&self) -> usize {
        self.raw.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    pub fn next_index(&self) -> I {
        I::new(self.len())
    }

    pub fn iter(&self) -> slice::Iter<'_, T> {
        self.raw.iter()
    }

    pub fn iter_enumerated(&self) -> impl DoubleEndedIterator<Item = (I, &T)> + ExactSizeIterator {
        let _ = I::new(self.len());
        self.raw.iter().enumerate().map(|(n, t)| (I::new(n), t))
    }

    pub fn indices(
        &self,
    ) -> impl DoubleEndedIterator<Item = I> + ExactSizeIterator + Clone + 'static {
        let _ = I::new(self.len());
        (0..self.len()).map(|n| I::new(n))
    }

    pub fn iter_mut(&mut self) -> slice::IterMut<'_, T> {
        self.raw.iter_mut()
    }

    pub fn iter_enumerated_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = (I, &mut T)> + ExactSizeIterator {
        let _ = I::new(self.len());
        self.raw.iter_mut().enumerate().map(|(n, t)| (I::new(n), t))
    }

    pub fn last_index(&self) -> Option<I> {
        self.len().checked_sub(1).map(I::new)
    }

    pub fn swap(&mut self, a: I, b: I) {
        self.raw.swap(a.index(), b.index());
    }

    pub fn get<R: IntoSliceIdx<I, [T]>>(
        &self,
        index: R,
    ) -> Option<&<R::Output as SliceIndex<[T]>>::Output> {
        self.raw.get(index.into_slice_idx())
    }

    pub fn get_mut<R: IntoSliceIdx<I, [T]>>(
        &mut self,
        index: R,
    ) -> Option<&mut <R::Output as SliceIndex<[T]>>::Output> {
        self.raw.get_mut(index.into_slice_idx())
    }
}

impl<I: Idx, T: fmt::Debug> fmt::Debug for IndexSlice<I, T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.raw, fmt)
    }
}

impl<I: Idx, T, R: IntoSliceIdx<I, [T]>> Index<R> for IndexSlice<I, T> {
    type Output = <R::Output as SliceIndex<[T]>>::Output;

    fn index(&self, index: R) -> &Self::Output {
        &self.raw[index.into_slice_idx()]
    }
}

impl<I: Idx, T, R: IntoSliceIdx<I, [T]>> IndexMut<R> for IndexSlice<I, T> {
    fn index_mut(&mut self, index: R) -> &mut Self::Output {
        &mut self.raw[index.into_slice_idx()]
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a IndexSlice<I, T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> slice::Iter<'a, T> {
        self.raw.iter()
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a mut IndexSlice<I, T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.raw.iter_mut()
    }
}

impl<I: Idx, T: Clone> ToOwned for IndexSlice<I, T> {
    type Owned = IndexVec<I, T>;

    fn to_owned(&self) -> IndexVec<I, T> {
        IndexVec::from_raw(self.raw.to_owned())
    }

    fn clone_into(&self, target: &mut IndexVec<I, T>) {
        self.raw.clone_into(&mut target.raw);
    }
}

impl<I: Idx, T> Default for &IndexSlice<I, T> {
    fn default() -> Self {
        IndexSlice::from_raw(Default::default())
    }
}

impl<I: Idx, T> Default for &mut IndexSlice<I, T> {
    fn default() -> Self {
        IndexSlice::from_raw_mut(Default::default())
    }
}
