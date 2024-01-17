use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Loc {
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    pub start: Loc,
    pub end: Loc,
}

pub trait Spanned {
    fn span(&self) -> Span;
}

impl PartialOrd for Loc {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Loc {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.line == other.line {
            self.col.cmp(&other.col)
        } else {
            self.line.cmp(&other.line)
        }
    }
}

impl Spanned for Span {
    #[inline]
    fn span(&self) -> Span {
        *self
    }
}

impl Span {
    #[inline]
    pub fn new(start: Loc, end: Loc) -> Self {
        Self { start, end }
    }

    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            start: std::cmp::min(self.start, other.start),
            end: std::cmp::max(self.end, other.end),
        }
    }
}

impl Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.line == 0 {
            return write!(f, "eof");
        }

        write!(f, "{}:{}", self.line, self.col)
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({})..({})", self.start, self.end)
    }
}
