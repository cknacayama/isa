use std::fmt::{Debug, Display};
use thiserror::Error;

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

impl Span {
    pub fn new(start: u32, end: u32) -> Option<Self> {
        if start <= end {
            Some(Self { start, end })
        } else {
            None
        }
    }

    pub fn union(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end:   self.end.max(other.end),
        }
    }

    pub fn start_loc(self, input: &str) -> Loc {
        let mut line = 1;
        let mut col = 1;

        for c in input.chars().take(self.start as usize) {
            match c {
                '\n' => {
                    line += 1;
                    col = 1
                }
                _ => col += 1,
            }
        }

        Loc { line, col }
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

#[derive(Clone, Copy, PartialEq, Eq, Error)]
pub struct Spanned<T> {
    pub data: T,
    pub span: Span,
}

impl<T> Debug for Spanned<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

impl<T> Spanned<T> {
    pub fn new(data: T, span: Span) -> Self {
        Self { data, span }
    }

    pub fn data(&self) -> &T {
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
