use std::error::Error;
use std::fmt::{Debug, Display};

use crate::global::Span;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpanData {
    file_id: usize,
    lo:      usize,
    hi:      usize,
}

impl SpanData {
    #[must_use]
    pub const fn new(file_id: usize, lo: usize, hi: usize) -> Self {
        Self { file_id, lo, hi }
    }

    #[inline]
    #[must_use]
    pub const fn join(&self, other: &Self) -> Self {
        const fn min(lhs: usize, rhs: usize) -> usize {
            if rhs < lhs { rhs } else { lhs }
        }
        const fn max(lhs: usize, rhs: usize) -> usize {
            if rhs < lhs { lhs } else { rhs }
        }

        Self {
            file_id: self.file_id,
            lo:      min(self.lo, other.lo),
            hi:      max(self.hi, other.hi),
        }
    }

    #[must_use]
    pub const fn lo(&self) -> usize {
        self.lo
    }

    #[must_use]
    pub const fn hi(&self) -> usize {
        self.hi
    }

    #[must_use]
    pub const fn file_id(&self) -> usize {
        self.file_id
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Spand<T> {
    pub data: T,
    pub span: Span,
}

impl<T: Eq> Eq for Spand<T> {
}

impl<T: PartialEq> PartialEq for Spand<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: Display> Display for Spand<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

impl<T: Error> Error for Spand<T> {
}

impl<T> Spand<T> {
    pub const fn new(data: T, span: Span) -> Self {
        Self { data, span }
    }

    pub const fn data(&self) -> &T {
        &self.data
    }

    pub fn map<F, U>(self, f: F) -> Spand<U>
    where
        F: FnOnce(T) -> U,
    {
        Spand::new(f(self.data), self.span)
    }
}

impl<T> From<Spand<T>> for Vec<Spand<T>> {
    fn from(value: Spand<T>) -> Self {
        vec![value]
    }
}
