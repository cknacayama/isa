use std::error::Error;
use std::fmt::{Debug, Display};

use crate::global::Span;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpanData {
    file_id: usize,
    start:   usize,
    end:     usize,
}

impl SpanData {
    #[must_use]
    pub const fn new(file_id: usize, start: usize, end: usize) -> Self {
        Self {
            file_id,
            start,
            end,
        }
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
            start:   min(self.start, other.start),
            end:     max(self.end, other.end),
        }
    }

    #[must_use]
    pub const fn start(&self) -> usize {
        self.start
    }

    #[must_use]
    pub const fn end(&self) -> usize {
        self.end
    }

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
