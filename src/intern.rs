use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
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
    pub const fn interned(&self) -> &'a T {
        self.0
    }
}

impl<'a, T: ?Sized> Clone for Interned<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T: ?Sized> Copy for Interned<'a, T> {
}

impl<'a, T: ?Sized> Deref for Interned<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.0
    }
}

impl<'a, T: ?Sized> PartialEq for Interned<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

impl<'a, T: ?Sized> Eq for Interned<'a, T> {
}

impl<'a, T: ?Sized> Hash for Interned<'a, T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, s: &mut H) {
        ptr::hash(self.0, s)
    }
}

impl<T: ?Sized + Debug> Debug for Interned<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct InternedIdx<'a, I, T: ?Sized>(I, PhantomData<&'a T>, PrivateZst);

impl<'a, I: Copy, T: ?Sized> InternedIdx<'a, I, T> {
    #[inline]
    pub const fn new_unchecked(idx: I) -> Self {
        Self(idx, PhantomData, PrivateZst)
    }

    #[inline]
    pub const fn index(&self) -> I {
        self.0
    }
}

impl<'a, I: Copy, T: ?Sized> Clone for InternedIdx<'a, I, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, I: Copy, T: ?Sized> Copy for InternedIdx<'a, I, T> {
}

pub trait Interner<'a, T: ?Sized> {
    type Data;
    fn intern(&mut self, data: Self::Data) -> Interned<'a, T>;
}

pub trait IdxInterner<'a, I, T: ?Sized> {
    type Data;

    fn intern_idx(&mut self, data: Self::Data) -> InternedIdx<'a, I, T>;
    fn get(&self, idx: InternedIdx<'a, I, T>) -> &'a T;
}
