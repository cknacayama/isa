use std::collections::HashSet;
use std::fmt::{self, Debug};
use std::hash::{BuildHasher, Hash, Hasher};
use std::ops::Deref;
use std::ptr;

use private::PrivateZst;

mod private {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct PrivateZst;
}

pub struct Interned<'a, T: ?Sized>(&'a T, PrivateZst);

impl<'a, T: ?Sized> Interned<'a, T> {
    #[inline]
    pub const fn new_unchecked(t: &'a T) -> Self {
        Self(t, PrivateZst)
    }

    #[inline]
    #[must_use]
    pub const fn interned(&self) -> &'a T {
        self.0
    }
}

impl<T: ?Sized> Clone for Interned<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for Interned<'_, T> {}

impl<T: ?Sized> Deref for Interned<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.0
    }
}

impl<T: ?Sized> PartialEq for Interned<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

impl<T: ?Sized> Eq for Interned<'_, T> {}

impl<T: ?Sized + Hash> Hash for Interned<'_, T> {
    fn hash<H: Hasher>(&self, s: &mut H) {
        ptr::hash(self.0, s);
    }
}

impl<T: ?Sized + Debug> Debug for Interned<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

pub trait Interner<'a, T: ?Sized> {
    type Data;
    fn intern(&mut self, data: Self::Data) -> Interned<'a, T>;
}

impl<T, H> Interner<'static, [T]> for HashSet<&'static [T], H>
where
    T: Eq + Hash,
    H: BuildHasher,
{
    type Data = Vec<T>;

    fn intern(&mut self, data: Self::Data) -> Interned<'static, [T]> {
        if let Some(interned) = self.get(data.as_slice()) {
            return Interned::new_unchecked(*interned);
        }

        let interned = Box::leak(data.into_boxed_slice());
        self.insert(interned);
        Interned::new_unchecked(interned)
    }
}
