use std::fmt::{Debug, Display};

use super::infer::{ClassConstraintSet, Substitute};
use super::token::TokenKind;
use super::types::{Ty, TyKind, TySlice};
use crate::global::{Span, Symbol};
use crate::separated_fmt;

#[derive(Clone, Copy, Debug)]
pub struct Ident {
    pub ident: Symbol,
    pub span:  Span,
}

impl Default for Ident {
    fn default() -> Self {
        Self::zero()
    }
}

impl Ident {
    pub const fn new(ident: Symbol, span: Span) -> Self {
        Self { ident, span }
    }

    pub const fn zero() -> Self {
        Self {
            ident: Symbol::zero(),
            span:  Span::zero(),
        }
    }
}

impl Eq for Ident {
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
    }
}

impl std::hash::Hash for Ident {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
    }
}

#[derive(Clone, Copy)]
pub struct Path {
    segments: [Ident; 3],
    len:      u8,
}

impl Debug for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Path")
            .field("segments", &self.as_slice())
            .finish_non_exhaustive()
    }
}

impl std::hash::Hash for Path {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl Eq for Path {
}

impl PartialEq for Path {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Path {
    pub const fn push(&mut self, id: Ident) -> bool {
        if self.len == 3 {
            false
        } else {
            self.segments[self.len as usize] = id;
            self.len += 1;
            true
        }
    }

    pub fn as_slice(&self) -> &[Ident] {
        &self.segments[..self.len as usize]
    }

    pub const fn from_slice(seg: &[Ident]) -> Option<Self> {
        match *seg {
            [fst] => Some(Self::from_one(fst)),
            [fst, snd] => Some(Self::from_two(fst, snd)),
            [fst, snd, trd] => Some(Self::from_three(fst, snd, trd)),
            _ => None,
        }
    }

    pub const fn from_one(ident: Ident) -> Self {
        let zero = Ident::zero();
        Self {
            segments: [ident, zero, zero],
            len:      1,
        }
    }

    pub const fn from_two(fst: Ident, snd: Ident) -> Self {
        let zero = Ident::zero();
        Self {
            segments: [fst, snd, zero],
            len:      2,
        }
    }

    pub const fn from_three(fst: Ident, snd: Ident, trd: Ident) -> Self {
        Self {
            segments: [fst, snd, trd],
            len:      3,
        }
    }

    pub fn span(&self) -> Span {
        self.as_slice()
            .iter()
            .map(|id| id.span)
            .reduce(Span::join)
            .unwrap()
    }

    pub const fn base_name(&self) -> Ident {
        self.segments[(self.len as usize) - 1]
    }

    pub fn is_ident(&self, name: Ident) -> bool {
        self.len == 1 && self.segments[0] == name
    }

    pub const fn as_ident(&self) -> Option<Ident> {
        if self.len == 1 {
            Some(self.segments[0])
        } else {
            None
        }
    }
}

macro_rules! mod_path {
    ($seg:ident) => {{
        use crate::compiler::ast::{Ident, Path};
        use crate::global::{Span, Symbol};
        Path::from_one(Ident {
            ident: Symbol::intern(stringify!($seg)),
            span:  Span::zero(),
        })
    }};
    ($fst:ident::$snd:ident) => {{
        use crate::compiler::ast::{Ident, Path};
        use crate::global::{Span, Symbol};
        Path::from_two(
            Ident {
                ident: Symbol::intern(stringify!($fst)),
                span:  Span::zero(),
            },
            Ident {
                ident: Symbol::intern(stringify!($snd)),
                span:  Span::zero(),
            },
        )
    }};
}
pub(crate) use mod_path;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fixity {
    Nonfix,
    Infixl,
    Infixr,
    Prefix,
}

impl Display for Fixity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Infixl | Self::Infixr | Self::Nonfix => write!(f, "infix"),
            Self::Prefix => write!(f, "prefix"),
        }
    }
}

impl Fixity {
    pub const fn from_tk(tk: TokenKind) -> Option<Self> {
        match tk {
            TokenKind::KwInfix => Some(Self::Nonfix),
            TokenKind::KwInfixl => Some(Self::Infixl),
            TokenKind::KwInfixr => Some(Self::Infixr),
            TokenKind::KwPrefix => Some(Self::Prefix),
            _ => None,
        }
    }

    #[must_use]
    pub const fn is_right(self) -> bool {
        matches!(self, Self::Infixr)
    }

    #[must_use]
    pub const fn is_prefix(self) -> bool {
        matches!(self, Self::Prefix)
    }

    pub const fn minimum_arity(self) -> usize {
        match self {
            Self::Infixl | Self::Infixr | Self::Nonfix => 2,
            Self::Prefix => 1,
        }
    }

    #[must_use]
    pub const fn is_nonfix(self) -> bool {
        matches!(self, Self::Nonfix)
    }
}

impl TokenKind {
    #[must_use]
    pub const fn can_start_expr(&self) -> bool {
        matches!(
            self,
            Self::LParen
                | Self::LBracket
                | Self::Backslash
                | Self::Integer(_)
                | Self::String(_)
                | Self::Ident(_)
                | Self::Char(_)
                | Self::KwTrue
                | Self::KwFalse
                | Self::KwLet
                | Self::KwMatch
                | Self::KwIf
        )
    }

    #[must_use]
    pub const fn can_start_type(&self) -> bool {
        matches!(
            self,
            Self::LParen | Self::Ident(_) | Self::KwInt | Self::KwBool | Self::KwChar
        )
    }

    #[must_use]
    pub const fn can_start_pat(&self) -> bool {
        matches!(
            self,
            Self::LParen
                | Self::LBracket
                | Self::DotDot
                | Self::DotDotEq
                | Self::Underscore
                | Self::Ident(_)
                | Self::Integer(_)
                | Self::Char(_)
                | Self::Operator(_)
                | Self::KwTrue
                | Self::KwFalse
        )
    }

    pub const fn recover_start_point(&self) -> bool {
        matches!(
            self,
            Self::LParen
                | Self::RParen
                | Self::LBracket
                | Self::RBracket
                | Self::Backslash
                | Self::Integer(_)
                | Self::Real(_)
                | Self::Ident(_)
                | Self::String(_)
                | Self::Char(_)
                | Self::KwModule
                | Self::KwTrue
                | Self::KwFalse
                | Self::KwType
                | Self::KwAlias
                | Self::KwLet
                | Self::KwVal
                | Self::KwClass
                | Self::KwInstance
                | Self::KwInfix
                | Self::KwInfixl
                | Self::KwInfixr
                | Self::KwPrefix
                | Self::KwMatch
                | Self::KwIf
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Constructor<T> {
    pub name:   Ident,
    pub params: TySlice,
    pub span:   Span,
    pub ty:     T,
}

impl<T> Display for Constructor<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        self.params.iter().try_for_each(|p| write!(f, " {p}"))
    }
}

#[derive(Debug, Default, Clone)]
pub struct ImportClause(pub Box<[Import]>);

impl IntoIterator for ImportClause {
    type Item = Import;
    type IntoIter = std::vec::IntoIter<Import>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[derive(Debug, Clone)]
pub enum ImportWildcard {
    Nil,
    Wildcard,
    Clause(ImportClause),
}

#[derive(Debug, Clone)]
pub struct Import {
    pub path:     Path,
    pub wildcard: ImportWildcard,
}

#[derive(Debug, Clone)]
pub struct Module<T> {
    pub no_prelude: bool,
    pub name:       Ident,
    pub imports:    ImportClause,
    pub stmts:      Vec<Stmt<T>>,
    pub span:       Span,
}

impl<T> Module<T> {
    #[must_use]
    pub const fn new(
        no_prelude: bool,
        name: Ident,
        imports: ImportClause,
        stmts: Vec<Stmt<T>>,
        span: Span,
    ) -> Self {
        Self {
            no_prelude,
            name,
            imports,
            stmts,
            span,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum RangePat<T> {
    From(T),
    To(T),
    ToInclusive(T),
    Exclusive(T, T),
    Inclusive(T, T),
}

impl<T: Debug> Display for RangePat<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::From(i) => write!(f, "{i:?}.."),
            Self::To(i) => write!(f, "..{i:?}"),
            Self::ToInclusive(i) => write!(f, "..={i:?}"),
            Self::Exclusive(lo, hi) => write!(f, "{lo:?}..{hi:?}"),
            Self::Inclusive(lo, hi) => write!(f, "{lo:?}..={hi:?}"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ListPat<T> {
    Nil,
    Single(Box<Pat<T>>),
    Cons(Box<Pat<T>>, Box<Pat<T>>),
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum PatKind<T> {
    Wild,

    Ident(Ident),

    Or(Box<[Pat<T>]>),

    Tuple(Box<[Pat<T>]>),

    List(ListPat<T>),

    Int(i64),

    Real(f64),

    Char(u8),

    IntRange(RangePat<i64>),

    RealRange(RangePat<f64>),

    CharRange(RangePat<u8>),

    Bool(bool),

    Constructor { name: Path, args: Box<[Pat<T>]> },
}

impl<T> PatKind<T> {
    pub const fn is_rest_pat(&self) -> bool {
        matches!(self, Self::List(_) | Self::Ident(_) | Self::Wild)
    }
}

#[derive(Debug, Clone)]
pub struct Pat<T> {
    pub kind: PatKind<T>,
    pub span: Span,
    pub ty:   T,
}

impl<T> Pat<T> {
    #[must_use]
    pub const fn new(kind: PatKind<T>, span: Span, ty: T) -> Self {
        Self { kind, span, ty }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Expr<T> {
    pub kind: ExprKind<T>,
    pub span: Span,
    pub ty:   T,
}

#[derive(Debug, Clone)]
pub struct Stmt<T> {
    pub kind: StmtKind<T>,
    pub span: Span,
}

impl<T> Stmt<T> {
    pub const fn new(kind: StmtKind<T>, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone)]
pub struct MatchArm<T> {
    pub pat:  Pat<T>,
    pub expr: Expr<T>,
}

impl<T> MatchArm<T> {
    #[must_use]
    pub const fn new(pat: Pat<T>, expr: Expr<T>) -> Self {
        Self { pat, expr }
    }

    pub const fn pat(&self) -> &Pat<T> {
        &self.pat
    }

    pub const fn expr(&self) -> &Expr<T> {
        &self.expr
    }
}

#[derive(Debug, Clone)]
pub struct Param<T> {
    pub pat: Pat<T>,
}

impl<T> Param<T> {
    #[must_use]
    pub const fn new(pat: Pat<T>) -> Self {
        Self { pat }
    }
}

#[derive(Debug, Clone)]
pub struct LetBind<T> {
    pub operator: bool,
    pub name:     Ident,
    pub params:   Box<[Param<T>]>,
    pub expr:     Expr<T>,
}

impl<T> LetBind<T> {
    pub const fn new(operator: bool, name: Ident, params: Box<[Param<T>]>, expr: Expr<T>) -> Self {
        Self {
            operator,
            name,
            params,
            expr,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Val {
    pub params: TySlice,
    pub set:    ClassConstraintSet,
    pub name:   Ident,
    pub ty:     Ty,
    pub span:   Span,
}

#[derive(Debug, Clone)]
pub struct Operator {
    pub fixity:  Fixity,
    pub prec:    u8,
    pub params:  TySlice,
    pub set:     ClassConstraintSet,
    pub op:      Ident,
    pub ty:      Ty,
    pub ty_span: Span,
    pub span:    Span,
}

#[derive(Debug, Clone)]
pub enum StmtKind<T> {
    Semi(Expr<T>),

    Let(LetBind<T>),

    Operator(Operator),

    Val(Val),

    Class {
        set:        ClassConstraintSet,
        name:       Ident,
        parents:    Box<[Path]>,
        signatures: Box<[Val]>,
        ops:        Box<[Operator]>,
        defaults:   Box<[LetBind<T>]>,
    },

    Instance {
        params:   TySlice,
        set:      ClassConstraintSet,
        class:    Path,
        instance: Ty,
        impls:    Box<[LetBind<T>]>,
    },

    Type {
        name:         Ident,
        params:       TySlice,
        constructors: Box<[Constructor<T>]>,
    },

    Alias {
        name:   Ident,
        params: TySlice,
        ty:     Ty,
    },
}

#[derive(Debug, Clone)]
pub enum ExprKind<T> {
    Int(i64),

    Real(f64),

    String(Symbol),

    Bool(bool),

    Char(u8),

    Path(Path),

    Operator(Ident),

    Tuple(Box<[Expr<T>]>),

    List(Box<[Expr<T>]>),

    /// Used for keeping track of intended precedence
    /// when resolving operators
    Paren(Box<Expr<T>>),

    Let {
        bind: Box<LetBind<T>>,
        body: Box<Expr<T>>,
    },

    Infix {
        op:  Ident,
        lhs: Box<Expr<T>>,
        rhs: Box<Expr<T>>,
    },

    Prefix {
        op:   Ident,
        expr: Box<Expr<T>>,
    },

    Fn {
        param: Param<T>,
        expr:  Box<Expr<T>>,
    },

    Match {
        expr: Box<Expr<T>>,
        arms: Box<[MatchArm<T>]>,
    },

    If {
        cond:      Box<Expr<T>>,
        then:      Box<Expr<T>>,
        otherwise: Box<Expr<T>>,
    },

    Call {
        callee: Box<Expr<T>>,
        arg:    Box<Expr<T>>,
    },
}

impl<T> Default for ExprKind<T> {
    fn default() -> Self {
        Self::Bool(false)
    }
}

impl<T> StmtKind<T> {
    #[must_use]
    pub const fn is_type_or_val_or_op(&self) -> bool {
        matches!(
            self,
            Self::Type { .. } | Self::Alias { .. } | Self::Val(_) | Self::Operator(_)
        )
    }
}

impl<T> Expr<T> {
    #[must_use]
    pub const fn new(kind: ExprKind<T>, span: Span, ty: T) -> Self {
        Self { kind, span, ty }
    }
}

impl Substitute for Param<Ty> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.pat.substitute(subs)
    }
}

impl Substitute for Constructor<()> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.params.substitute(subs)
    }
}

impl Substitute for Constructor<Ty> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.ty.substitute(subs) | self.params.substitute(subs)
    }
}

impl Substitute for Val {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.set.substitute(subs) | self.ty.substitute(subs) | self.params.substitute(subs)
    }
}

impl Substitute for Operator {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.set.substitute(subs) | self.ty.substitute(subs) | self.params.substitute(subs)
    }
}

impl Substitute for Stmt<()> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        match &mut self.kind {
            StmtKind::Type { constructors, .. } => constructors.substitute(subs),
            StmtKind::Alias { ty, .. } => ty.substitute(subs),
            StmtKind::Val(val) => val.substitute(subs),
            StmtKind::Class {
                signatures,
                ops,
                set,
                ..
            } => signatures.substitute(subs) | ops.substitute(subs) | set.substitute(subs),
            StmtKind::Instance { instance, set, .. } => {
                instance.substitute(subs) | set.substitute(subs)
            }
            StmtKind::Operator(Operator { ty, set, .. }) => {
                set.substitute(subs) | ty.substitute(subs)
            }
            StmtKind::Let(_) | StmtKind::Semi(_) => false,
        }
    }
}

impl Substitute for LetBind<Ty> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.expr.substitute(subs) | self.params.substitute(subs)
    }
}

impl Substitute for StmtKind<Ty> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        match self {
            Self::Let(bind) => bind.substitute(subs),
            Self::Semi(semi) => semi.substitute(subs),
            Self::Type { constructors, .. } => constructors.substitute(subs),
            Self::Alias { ty, .. } => ty.substitute(subs),
            Self::Val(val) => val.substitute(subs),
            Self::Class {
                set,
                signatures,
                defaults,
                ..
            } => set.substitute(subs) | signatures.substitute(subs) | defaults.substitute(subs),
            Self::Instance {
                params,
                set,
                instance,
                impls,
                ..
            } => {
                set.substitute(subs)
                    | instance.substitute(subs)
                    | params.substitute(subs)
                    | impls.substitute(subs)
            }
            Self::Operator(Operator {
                params, set, ty, ..
            }) => set.substitute(subs) | params.substitute(subs) | ty.substitute(subs),
        }
    }
}

impl Substitute for Stmt<Ty> {
    #[inline]
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.kind.substitute(subs)
    }
}

impl Substitute for MatchArm<Ty> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.pat.substitute(subs) | self.expr.substitute(subs)
    }
}

impl Substitute for Expr<Ty> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        let kind = match &mut self.kind {
            ExprKind::Let { bind, body } => bind.substitute(subs) | body.substitute(subs),
            ExprKind::Fn { param, expr } => param.substitute(subs) | expr.substitute(subs),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => cond.substitute(subs) | then.substitute(subs) | otherwise.substitute(subs),
            ExprKind::Call { callee, arg } => callee.substitute(subs) | arg.substitute(subs),
            ExprKind::Match { expr, arms } => expr.substitute(subs) | arms.substitute(subs),
            ExprKind::List(exprs) | ExprKind::Tuple(exprs) => exprs.substitute(subs),
            ExprKind::Infix { lhs, rhs, .. } => lhs.substitute(subs) | rhs.substitute(subs),
            ExprKind::Prefix { expr, .. } | ExprKind::Paren(expr) => expr.substitute(subs),

            ExprKind::Operator(_)
            | ExprKind::Int(_)
            | ExprKind::Real(_)
            | ExprKind::String(_)
            | ExprKind::Bool(_)
            | ExprKind::Char(_)
            | ExprKind::Path(_) => false,
        };

        kind | self.ty.substitute(subs)
    }
}

impl<T> Substitute for Module<T>
where
    Stmt<T>: Substitute,
{
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.stmts.substitute(subs)
    }
}

impl Substitute for ListPat<Ty> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        match self {
            Self::Nil => false,
            Self::Single(pat) => pat.substitute(subs),
            Self::Cons(pat, pat1) => pat.substitute(subs) | pat1.substitute(subs),
        }
    }
}

impl Substitute for Pat<Ty> {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        let kind = match &mut self.kind {
            PatKind::Tuple(args) | PatKind::Or(args) | PatKind::Constructor { args, .. } => {
                args.substitute(subs)
            }

            PatKind::List(list) => list.substitute(subs),

            PatKind::Wild
            | PatKind::Int(_)
            | PatKind::Bool(_)
            | PatKind::Ident(_)
            | PatKind::Real(_)
            | PatKind::Char(_)
            | PatKind::IntRange(_)
            | PatKind::CharRange(_)
            | PatKind::RealRange(_) => false,
        };

        kind | self.ty.substitute(subs)
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.ident, f)
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        separated_fmt(f, self.as_slice(), "::", |seg, f| write!(f, "{seg}"))
    }
}

impl Expr<()> {
    #[must_use]
    pub const fn untyped(kind: ExprKind<()>, span: Span) -> Self {
        Self::new(kind, span, ())
    }
}

impl Pat<()> {
    #[must_use]
    pub const fn untyped(kind: PatKind<()>, span: Span) -> Self {
        Self::new(kind, span, ())
    }
}
