use std::fmt::{Debug, Display};

use super::infer::Substitute;
use super::token::TokenKind;
use super::types::{Ty, TyId, TyKind};
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
    #[must_use]
    pub const fn new(ident: Symbol, span: Span) -> Self {
        Self { ident, span }
    }

    #[must_use]
    pub const fn zero() -> Self {
        Self {
            ident: Symbol::zero(),
            span:  Span::zero(),
        }
    }
}

impl std::hash::Hash for Ident {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
    }
}

impl Eq for Ident {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Path {
    segments: Vec<Ident>,
}

impl Path {
    pub fn push(&mut self, id: Ident) {
        self.segments.push(id);
    }

    #[must_use]
    pub const fn as_slice(&self) -> &[Ident] {
        self.segments.as_slice()
    }

    #[must_use]
    pub fn from_one(ident: Ident) -> Self {
        Self {
            segments: vec![ident],
        }
    }

    #[must_use]
    pub fn from_two(fst: Ident, snd: Ident) -> Self {
        Self {
            segments: vec![fst, snd],
        }
    }

    pub fn span(&self) -> Span {
        self.segments
            .iter()
            .map(|id| id.span)
            .reduce(Span::join)
            .unwrap()
    }

    #[must_use]
    pub fn base_name(&self) -> Ident {
        *self.segments.last().unwrap()
    }

    #[must_use]
    pub const fn as_ident(&self) -> Option<Ident> {
        match self.as_slice() {
            [id] => Some(*id),
            _ => None,
        }
    }

    #[must_use]
    pub const fn from_vec(segments: Vec<Ident>) -> Self {
        Self { segments }
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
    #[must_use]
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

    #[must_use]
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

    #[must_use]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HiTyKind {
    Int,
    Bool,
    Char,
    Real,
    This,
    Var(TyId),
    Named(Path),
    Tuple(Box<[HiTy]>),
    Fn { param: Box<HiTy>, ret: Box<HiTy> },
    Parametric { ty: Box<HiTy>, args: Box<[HiTy]> },
}

impl HiTyKind {
    #[must_use]
    pub const fn is_this(&self) -> bool {
        matches!(self, Self::This)
    }

    pub fn get_ident(&self) -> Option<Ident> {
        self.as_named().and_then(Path::as_ident)
    }

    #[must_use]
    pub const fn as_named(&self) -> Option<&Path> {
        if let Self::Named(v) = self {
            Some(v)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_var(&self) -> Option<TyId> {
        if let Self::Var(v) = self {
            Some(*v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct HiTy {
    pub kind: HiTyKind,
    pub span: Span,
}

impl PartialEq for HiTy {
    fn eq(&self, other: &Self) -> bool {
        self.kind() == other.kind()
    }
}

impl Eq for HiTy {}

impl HiTy {
    #[must_use]
    pub const fn new(kind: HiTyKind, span: Span) -> Self {
        Self { kind, span }
    }

    #[must_use]
    pub const fn kind(&self) -> &HiTyKind {
        &self.kind
    }

    #[must_use]
    pub fn contains_name(&self, name: &Path) -> Option<Span> {
        match self.kind() {
            HiTyKind::Named(path) if name == path => Some(self.span),
            HiTyKind::Tuple(items) => items.iter().find_map(|ty| ty.contains_name(name)),
            HiTyKind::Fn { param, ret } => param
                .contains_name(name)
                .or_else(|| ret.contains_name(name)),
            HiTyKind::Parametric { ty, args } => ty
                .contains_name(name)
                .or_else(|| args.iter().find_map(|ty| ty.contains_name(name))),

            HiTyKind::Named(_)
            | HiTyKind::Int
            | HiTyKind::Bool
            | HiTyKind::Char
            | HiTyKind::Real
            | HiTyKind::This
            | HiTyKind::Var(_) => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct HiCtor<T> {
    pub name:   Ident,
    pub params: Box<[HiTy]>,
    pub span:   Span,
    pub ty:     T,
}

impl<T> Display for HiCtor<T> {
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
    #[must_use]
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
pub struct HiConstraint {
    pub class: Path,
    pub ty:    HiTy,
    pub span:  Span,
}

impl HiConstraint {
    #[must_use]
    pub const fn new(class: Path, ty: HiTy, span: Span) -> Self {
        Self { class, ty, span }
    }
}

#[derive(Debug, Clone)]
pub struct Val {
    pub params: Box<[HiTy]>,
    pub set:    Box<[HiConstraint]>,
    pub name:   Ident,
    pub ty:     HiTy,
    pub span:   Span,
}

#[derive(Debug, Clone)]
pub struct Operator {
    pub fixity: Fixity,
    pub prec:   u8,
    pub params: Box<[HiTy]>,
    pub set:    Box<[HiConstraint]>,
    pub op:     Ident,
    pub ty:     HiTy,
    pub span:   Span,
}

#[derive(Debug, Clone)]
pub enum StmtKind<T> {
    Semi(Expr<T>),

    Let(LetBind<T>),

    Operator(Operator),

    Val(Val),

    Class {
        set:        Box<[HiConstraint]>,
        name:       Ident,
        parents:    Box<[Path]>,
        signatures: Box<[Val]>,
        ops:        Box<[Operator]>,
        defaults:   Box<[LetBind<T>]>,
    },

    Instance {
        params:   Box<[HiTy]>,
        set:      Box<[HiConstraint]>,
        class:    Path,
        instance: HiTy,
        impls:    Box<[LetBind<T>]>,
    },

    Type {
        name:         Ident,
        params:       Box<[HiTy]>,
        constructors: Box<[HiCtor<T>]>,
    },

    Alias {
        name:   Ident,
        params: Box<[HiTy]>,
        ty:     HiTy,
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

fn rename_slice(ren: &impl Rename, slice: &mut [HiTy]) {
    for ty in slice {
        ren.walk_hi_ty(ty);
    }
}

pub trait Rename: Sized {
    fn rename_hi_ty(&self, ty: &mut HiTy);

    fn rename_class(&self, _class: &mut Path) {}

    fn rename_ctor<T>(&self, ctor: &mut HiCtor<T>) {
        rename_slice(self, &mut ctor.params);
    }

    fn rename_constrs(&self, slice: &mut [HiConstraint]) {
        for c in slice {
            self.walk_hi_ty(&mut c.ty);
            self.rename_class(&mut c.class);
        }
    }

    fn rename_stmt<T>(&self, stmt: &mut Stmt<T>) {
        match &mut stmt.kind {
            StmtKind::Operator(operator) => self.rename_op(operator),
            StmtKind::Val(val) => self.rename_val(val),
            StmtKind::Class {
                set,
                parents,
                signatures,
                ops,
                ..
            } => {
                self.rename_constrs(set);
                for class in parents {
                    self.rename_class(class);
                }
                for sig in signatures {
                    self.rename_val(sig);
                }
                for op in ops {
                    self.rename_op(op);
                }
            }
            StmtKind::Instance {
                params,
                set,
                class,
                instance,
                ..
            } => {
                rename_slice(self, params);
                self.rename_constrs(set);
                self.rename_class(class);
                self.walk_hi_ty(instance);
            }
            StmtKind::Type {
                params,
                constructors,
                ..
            } => {
                rename_slice(self, params);
                for ctor in constructors {
                    self.rename_ctor(ctor);
                }
            }
            StmtKind::Alias { params, ty, .. } => {
                rename_slice(self, params);
                self.walk_hi_ty(ty);
            }

            StmtKind::Semi(_) | StmtKind::Let(_) => {}
        }
    }

    fn rename_op(&self, op: &mut Operator) {
        rename_slice(self, &mut op.params);
        self.rename_constrs(&mut op.set);
        self.walk_hi_ty(&mut op.ty);
    }

    fn rename_val(&self, val: &mut Val) {
        rename_slice(self, &mut val.params);
        self.rename_constrs(&mut val.set);
        self.walk_hi_ty(&mut val.ty);
    }

    fn walk_hi_ty(&self, ty: &mut HiTy) {
        match &mut ty.kind {
            HiTyKind::Tuple(items) => {
                rename_slice(self, items);
            }
            HiTyKind::Fn { param, ret } => {
                self.walk_hi_ty(param);
                self.walk_hi_ty(ret);
            }
            HiTyKind::Parametric { ty, args } => {
                self.walk_hi_ty(ty);
                rename_slice(self, args);
            }

            HiTyKind::Named(_)
            | HiTyKind::Var(_)
            | HiTyKind::Int
            | HiTyKind::Bool
            | HiTyKind::Char
            | HiTyKind::Real
            | HiTyKind::This => {}
        }

        self.rename_hi_ty(ty);
    }
}

impl Rename for TyId {
    fn rename_hi_ty(&self, ty: &mut HiTy) {
        if ty.kind.is_this() {
            ty.kind = HiTyKind::Var(*self);
        }
    }
}

#[derive(Debug)]
pub struct ParamRenamer(pub Vec<(Ident, TyId)>);

impl Rename for ParamRenamer {
    fn rename_hi_ty(&self, ty: &mut HiTy) {
        if let Some(name) = ty.kind().get_ident()
            && let Some(new) = self
                .0
                .iter()
                .find_map(|(p, v)| if *p == name { Some(*v) } else { None })
        {
            ty.kind = HiTyKind::Var(new);
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ModuleRenamer(pub Ident);

impl Rename for ModuleRenamer {
    fn rename_hi_ty(&self, ty: &mut HiTy) {
        if let Some(name) = ty.kind().get_ident() {
            ty.kind = HiTyKind::Named(Path::from_two(self.0, name));
        }
    }

    fn rename_class(&self, class: &mut Path) {
        if let Some(name) = class.as_ident() {
            *class = Path::from_two(self.0, name);
        }
    }
}

impl<F> Rename for F
where
    F: Fn(&HiTyKind) -> Option<HiTyKind>,
{
    fn rename_hi_ty(&self, ty: &mut HiTy) {
        if let Some(new) = self(ty.kind()) {
            ty.kind = new;
        }
    }
}

impl Substitute for Param<Ty> {
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
    {
        self.pat.substitute(subs)
    }
}

impl Substitute for HiCtor<Ty> {
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
    {
        self.ty.substitute(subs)
    }
}

impl Substitute for LetBind<Ty> {
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
    {
        self.expr.substitute(subs) | self.params.substitute(subs)
    }
}

impl Substitute for StmtKind<Ty> {
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
    {
        match self {
            Self::Let(bind) => bind.substitute(subs),
            Self::Semi(semi) => semi.substitute(subs),
            Self::Type { constructors, .. } => constructors.substitute(subs),
            Self::Class { defaults, .. } => defaults.substitute(subs),
            Self::Instance { impls, .. } => impls.substitute(subs),
            Self::Operator(_) | Self::Val(_) | Self::Alias { .. } => false,
        }
    }
}

impl Substitute for Stmt<Ty> {
    #[inline]
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
    {
        self.kind.substitute(subs)
    }
}

impl Substitute for MatchArm<Ty> {
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
    {
        self.pat.substitute(subs) | self.expr.substitute(subs)
    }
}

impl Substitute for Expr<Ty> {
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
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
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
    {
        self.stmts.substitute(subs)
    }
}

impl Substitute for ListPat<Ty> {
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
    {
        match self {
            Self::Nil => false,
            Self::Single(pat) => pat.substitute(subs),
            Self::Cons(pat, pat1) => pat.substitute(subs) | pat1.substitute(subs),
        }
    }
}

impl Substitute for Pat<Ty> {
    fn substitute<S>(&mut self, subs: &S) -> bool
    where
        S: Fn(&TyKind) -> Option<Ty>,
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

impl Display for HiTy {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
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
