use std::fmt::{self, Display, Write};

pub mod driver;

pub(crate) mod compiler;
pub(crate) mod global;
pub(crate) mod intern;
pub(crate) mod report;
pub(crate) mod span;

pub(crate) fn comma_fmt<'a, T: 'a, W: Write>(
    w: &mut W,
    data: impl IntoIterator<Item = &'a T>,
    display: impl FnMut(&T, &mut W) -> fmt::Result,
) -> fmt::Result {
    separated_fmt(w, data, ", ", display)
}

pub(crate) fn separated_fmt<'a, T: 'a, W: Write>(
    w: &mut W,
    data: impl IntoIterator<Item = &'a T>,
    sep: impl Display,
    mut display: impl FnMut(&T, &mut W) -> fmt::Result,
) -> fmt::Result {
    let mut first = true;
    for data in data {
        if first {
            first = false;
        } else {
            write!(w, "{sep}")?;
        }
        display(data, w)?;
    }
    Ok(())
}
