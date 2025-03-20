use std::{
    fmt::{Debug, Display},
    ops::Index,
};

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
    pub fn new(start: u32, end: u32) -> Option<Self> {
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
        let mut start = 1;
        let mut end = 1;
        let mut passed = false;
        let mut ended = false;

        for (i, c) in input.char_indices() {
            if i > self.end as usize {
                ended = true;
            } else if i > self.start as usize {
                passed = true;
            }
            match c {
                '\n' if !passed => {
                    line += 1;
                    col = 1;
                    start = i;
                }
                '\n' if ended => {
                    break;
                }
                _ if !passed => col += 1,
                _ => end = i,
            }
        }

        (Loc { line, col }, &input[start..end])
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

impl<T> Debug for Spanned<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

impl<T> Display for Spanned<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

impl<T> std::error::Error for Spanned<T> where T: std::error::Error
{
}

impl<T> Spanned<T> {
    pub fn new(data: T, span: Span) -> Self {
        Self { data, span }
    }

    pub fn from_data(data: T) -> Self {
        Self {
            data,
            span: Span::default(),
        }
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

    pub fn span(&self) -> Span {
        self.span
    }
}
