use std::error::Error;
use std::fmt::{Debug, Display};

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

    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            file_id: self.file_id,
            start:   std::cmp::min(self.start, other.start),
            end:     std::cmp::max(self.end, other.end),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span(u32);

impl Default for Span {
    fn default() -> Self {
        Self::zero()
    }
}

impl Span {
    #[must_use]
    pub const fn new(idx: u32) -> Self {
        Self(idx)
    }

    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub const fn zero() -> Self {
        Self(0)
    }
}

impl Display for SpanData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

#[derive(Clone, Copy)]
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

impl<T: Debug> Debug for Spand<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
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
