use std::error::Error;
use std::fmt::{Debug, Display};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpanData {
    start: usize,
    end:   usize,
}

impl SpanData {
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Option<Self> {
        if start > end {
            None
        } else {
            Some(Self { start, end })
        }
    }

    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        Self {
            start: std::cmp::min(self.start, other.start),
            end:   std::cmp::max(self.end, other.end),
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
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span(u32);

impl Span {
    /// # Panics
    ///
    /// Panics if idx excedes `u32::MAX`
    #[must_use]
    pub fn new(idx: usize) -> Self {
        Self(idx.try_into().expect("Should have at max u32::MAX spans"))
    }

    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl Display for SpanData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Spanned<T> {
    pub data: T,
    pub span: Span,
}

impl<T: Debug> Debug for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

impl<T: Error> Error for Spanned<T> {
}

impl<T> Spanned<T> {
    pub const fn new(data: T, span: Span) -> Self {
        Self { data, span }
    }

    pub const fn data(&self) -> &T {
        &self.data
    }

    pub fn map<F, U>(self, f: F) -> Spanned<U>
    where
        F: FnOnce(T) -> U,
    {
        Spanned::new(f(self.data), self.span)
    }

    pub fn from<U>(other: Spanned<U>) -> Self
    where
        T: From<U>,
    {
        other.map(From::from)
    }
}
