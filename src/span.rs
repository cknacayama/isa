use std::error::Error;
use std::fmt::{Debug, Display};
use std::ops::Index;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    start: u32,
    end:   u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loc {
    line: u32,
    col:  u32,
}

impl Index<Span> for str {
    type Output = Self;

    fn index(&self, index: Span) -> &Self::Output {
        &self[(index.start as usize)..(index.end as usize)]
    }
}

impl Span {
    #[must_use]
    pub const fn new(start: u32, end: u32) -> Option<Self> {
        if start <= end {
            Some(Self { start, end })
        } else {
            None
        }
    }

    #[must_use]
    pub fn union(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end:   self.end.max(other.end),
        }
    }

    #[must_use]
    pub fn start_loc(self, input: &str) -> (Loc, &str) {
        let mut line = 1;
        let mut col = 1;

        for c in input.chars().take(self.start as usize) {
            match c {
                '\n' => {
                    line += 1;
                    col = 1;
                }
                _ => col += 1,
            }
        }

        (Loc { line, col }, &input[self])
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
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

    pub fn from_data(data: T) -> Self {
        Self {
            data,
            span: Span::default(),
        }
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

    pub const fn span(&self) -> Span {
        self.span
    }
}
