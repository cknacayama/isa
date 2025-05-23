use super::ast::Path;
use super::ctx::Generator;
use super::subs::{Subs, Substitute};
use crate::global::ty_path;
pub use crate::global::{Ty, TyPath, TyQuant, TySlice};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyId(u32);

impl TyId {
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyKind {
    Int,
    Bool,
    Char,
    Real,
    Var(TyId),
    Tuple(TySlice),
    Fn { param: Ty, ret: Ty },
    Scheme { quant: TyQuant, ty: Ty },
    Named { name: TyPath, args: TySlice },
    Generic { var: TyId, args: TySlice },
    This(TySlice),
}

impl TyKind {
    #[must_use]
    pub const fn as_var(&self) -> Option<TyId> {
        if let Self::Var(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    #[must_use]
    pub fn occurs(&self, var: TyId) -> bool {
        match self {
            Self::Fn { param, ret } => param.occurs(var) || ret.occurs(var),
            Self::Var(n) => *n == var,
            Self::Scheme { ty, .. } => ty.occurs(var),
            Self::This(args) | Self::Tuple(args) | Self::Named { args, .. } => {
                args.iter().any(|t| t.occurs(var))
            }
            Self::Generic { var: n, args } => *n == var || args.iter().any(|t| t.occurs(var)),

            Self::Int | Self::Char | Self::Bool | Self::Real => false,
        }
    }
}

impl Ty {
    #[must_use]
    pub fn occurs(self, var: TyId) -> bool {
        self.kind().occurs(var)
    }

    pub fn instantiate(self, generator: &mut impl Generator) -> (Self, Vec<Subs>) {
        let TyKind::Scheme { quant, ty } = self.kind() else {
            return (self, Vec::new());
        };
        let mut ty = *ty;

        let subs: Vec<_> = quant
            .iter()
            .map(|q| Subs::new(*q, generator.gen_type_var()))
            .collect();

        subs.as_slice().substitute_ty(&mut ty);

        (ty, subs)
    }

    #[must_use]
    pub fn zip_args(self, rhs: Self) -> Option<Vec<(Self, Self)>> {
        match (self.kind(), rhs.kind()) {
            (TyKind::Named { name: n1, args: a1 }, TyKind::Named { name: n2, args: a2 })
                if n1 == n2 && a1.len() == a2.len() =>
            {
                Some(a1.iter().copied().zip(a2.iter().copied()).collect())
            }
            (TyKind::Generic { args: a1, .. }, TyKind::Generic { args: a2, .. })
            | (TyKind::Tuple(a1), TyKind::Tuple(a2))
                if a1.len() == a2.len() =>
            {
                Some(a1.iter().copied().zip(a2.iter().copied()).collect())
            }
            (TyKind::Fn { param: p1, ret: r1 }, TyKind::Fn { param: p2, ret: r2 }) => {
                Some(vec![(*p1, *p2), (*r1, *r2)])
            }
            (TyKind::Scheme { quant: q1, ty: t1 }, TyKind::Scheme { quant: q2, ty: t2 })
                if q1.len() == q2.len() =>
            {
                t1.zip_args(*t2)
            }

            (TyKind::Var(_), TyKind::Var(_)) => Some(Vec::new()),

            (lhs, rhs) if lhs == rhs => Some(Vec::new()),

            _ => None,
        }
    }

    #[must_use]
    pub fn equivalent(self, rhs: Self) -> bool {
        match (self.kind(), rhs.kind()) {
            (TyKind::Named { name: n1, args: a1 }, TyKind::Named { name: n2, args: a2 }) => {
                n1 == n2
                    && a1.len() == a2.len()
                    && a1.iter().zip(a2.iter()).all(|(t1, &t2)| t1.equivalent(t2))
            }

            (TyKind::Generic { args: a1, .. }, TyKind::Generic { args: a2, .. })
            | (TyKind::Tuple(a1), TyKind::Tuple(a2)) => {
                a1.len() == a2.len() && a1.iter().zip(a2.iter()).all(|(t1, &t2)| t1.equivalent(t2))
            }

            (TyKind::Fn { param: p1, ret: r1 }, TyKind::Fn { param: p2, ret: r2 }) => {
                p1.equivalent(*p2) && r1.equivalent(*r2)
            }

            (TyKind::Scheme { quant: q1, ty: t1 }, TyKind::Scheme { quant: q2, ty: t2 }) => {
                q1.len() == q2.len() && t1.equivalent(*t2)
            }

            (TyKind::Var(_), TyKind::Var(_)) => true,

            (lhs, rhs) => lhs == rhs,
        }
    }

    pub fn function<I>(params: I, ret: Self) -> Self
    where
        I: IntoIterator<Item = Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        params
            .into_iter()
            .rev()
            .fold(ret, |ret, param| Self::intern(TyKind::Fn { param, ret }))
    }

    #[must_use]
    pub fn name_from_path(path: &Path) -> TyPath {
        Self::intern_path(path.as_slice().iter().map(|id| id.ident).collect())
    }

    #[must_use]
    pub fn unit() -> Self {
        Self::intern(TyKind::Tuple(Self::empty_slice()))
    }

    #[must_use]
    pub fn list(ty: Self) -> Self {
        Self::intern(TyKind::Named {
            name: ty_path!(list::List),
            args: Self::intern_slice(vec![ty]),
        })
    }

    #[must_use]
    pub fn tuple(args: Vec<Self>) -> Self {
        let args = Self::intern_slice(args);
        Self::intern(TyKind::Tuple(args))
    }

    #[must_use]
    pub fn function_arity(self) -> usize {
        match self.kind() {
            TyKind::Fn { ret, .. } => 1 + ret.function_arity(),
            TyKind::Scheme { ty, .. } => ty.function_arity(),
            _ => 0,
        }
    }

    #[must_use]
    pub const fn is_fn(self) -> bool {
        matches!(self.kind(), TyKind::Fn { .. })
    }

    #[must_use]
    pub const fn is_char(self) -> bool {
        matches!(self.kind(), TyKind::Char)
    }

    #[must_use]
    pub fn is_simple_fmt(self) -> bool {
        match self.kind() {
            TyKind::Int
            | TyKind::Bool
            | TyKind::Char
            | TyKind::Real
            | TyKind::Var(_)
            | TyKind::Tuple(_) => true,

            TyKind::This(args) | TyKind::Generic { args, .. } | TyKind::Named { args, .. } => {
                args.is_empty()
            }

            _ => false,
        }
    }

    #[must_use]
    pub const fn get_scheme_ty(self) -> Option<Self> {
        if let TyKind::Scheme { ty, .. } = self.kind() {
            Some(*ty)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_var(self) -> Option<TyId> {
        self.kind().as_var()
    }

    fn free_type_variables_inner(self, free: &mut Vec<TyId>) {
        match self.kind() {
            TyKind::Int | TyKind::Bool | TyKind::Char | TyKind::Real => (),
            TyKind::Var(id) if free.contains(id) => (),

            TyKind::Var(id) => {
                free.push(*id);
            }

            TyKind::Fn { param, ret } => {
                param.free_type_variables_inner(free);
                ret.free_type_variables_inner(free);
            }

            TyKind::Scheme { quant, ty } => {
                ty.free_type_variables_inner(free);
                while let Some(pos) = free.iter().position(|f| quant.contains(f)) {
                    free.swap_remove(pos);
                }
            }

            TyKind::This(args) | TyKind::Named { args, .. } | TyKind::Tuple(args) => {
                for arg in args.iter() {
                    arg.free_type_variables_inner(free);
                }
            }

            TyKind::Generic { var, args } => {
                for arg in args.iter() {
                    arg.free_type_variables_inner(free);
                }
                if !free.contains(var) {
                    free.push(*var);
                }
            }
        }
    }

    #[must_use]
    pub fn free_type_variables(self) -> Vec<TyId> {
        let mut free = Vec::new();
        self.free_type_variables_inner(&mut free);
        free
    }

    pub fn param_iter(self) -> impl Iterator<Item = Self> {
        ParamIter(self)
    }

    #[must_use]
    pub const fn is_scheme(self) -> bool {
        matches!(self.kind(), TyKind::Scheme { .. })
    }

    #[must_use]
    pub const fn is_var(self) -> bool {
        matches!(self.kind(), TyKind::Var(..))
    }
}

#[derive(Debug, Clone)]
pub struct ParamIter(Ty);

impl Iterator for ParamIter {
    type Item = Ty;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.kind() {
            TyKind::Fn { param, ret } => {
                self.0 = *ret;
                Some(*param)
            }
            TyKind::Scheme { ty, .. } => {
                self.0 = *ty;
                self.next()
            }
            _ => None,
        }
    }
}
