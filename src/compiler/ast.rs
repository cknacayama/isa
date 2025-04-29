use std::fmt::{Debug, Display};

use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};

use super::super::span::Span;
use super::infer::{ClassConstraintSet, Substitute};
use super::token::{Ident, TokenKind};
use super::types::Ty;
use crate::global::Symbol;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Path {
    pub segments: SmallVec<[Ident; 2]>,
}

impl Path {
    pub const fn new(segments: SmallVec<[Ident; 2]>) -> Self {
        Self { segments }
    }

    pub fn from_ident(ident: Ident) -> Self {
        Self {
            segments: smallvec![ident],
        }
    }

    pub fn span(&self) -> Span {
        self.segments
            .iter()
            .map(|id| id.span)
            .reduce(Span::union)
            .unwrap()
    }

    pub fn base_name(&self) -> Ident {
        match self.segments.as_slice() {
            [] => unreachable!(),
            [.., segment] => *segment,
        }
    }

    pub fn is_ident(&self, name: Ident) -> bool {
        match self.segments.as_slice() {
            [segment] => *segment == name,
            _ => false,
        }
    }

    pub fn as_ident(&self) -> Option<Ident> {
        match self.segments.as_slice() {
            [segment] => Some(*segment),
            _ => None,
        }
    }
}

macro_rules! mod_path {
    ($($seg:ident)::+) => {{
        use crate::global::symbol;
        use smallvec::smallvec;
        use crate::span::Span;
        use crate::compiler::ast::Path;
        use crate::compiler::token::Ident;
        let segments = smallvec![$(Ident { ident: symbol!(stringify!($seg)), span: Span::default() }),+];
        Path::new(segments)
    }};
}
pub(crate) use mod_path;

#[derive(Debug, Clone, Copy)]
pub struct Operator {
    pub precedence:    u8,
    pub associativity: Associativity,
}

impl Operator {
    pub const fn new(precedence: u8, associativity: Associativity) -> Self {
        Self {
            precedence,
            associativity,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    Non,
    Left,
    Right,
}

impl Associativity {
    #[must_use]
    pub const fn is_right(self) -> bool {
        matches!(self, Self::Right)
    }
}

#[derive(Debug, Clone)]
pub struct OperatorTable {
    infix:  FxHashMap<Symbol, Operator>,
    prefix: FxHashMap<Symbol, Operator>,
}

impl OperatorTable {
    pub fn get_infix(&self, op: Symbol) -> Option<Operator> {
        self.infix.get(&op).copied()
    }

    pub fn get_prefix(&self, op: Symbol) -> Option<Operator> {
        self.prefix.get(&op).copied()
    }
}

impl Default for OperatorTable {
    fn default() -> Self {
        use crate::global::intern_symbol as intern;

        macro_rules! operator {
            ($prec:literal $op:literal) => {
                (intern($op), Operator::new($prec, Associativity::Non))
            };
            (left $prec:literal $op:literal) => {
                (intern($op), Operator::new($prec, Associativity::Left))
            };
            (right $prec:literal $op:literal) => {
                (intern($op), Operator::new($prec, Associativity::Right))
            };
        }

        let mut infix = FxHashMap::default();
        let mut prefix = FxHashMap::default();
        prefix.extend([operator!(right 8 "!"), operator!(right 8 "-")]);
        infix.extend([
            operator!(right 0 "$"),
            operator!(left 1 ">>"),
            operator!(left 1 ">>="),
            operator!(right 2 "||"),
            operator!(right 3 "&&"),
            operator!(left 4 "<*"),
            operator!(left 4 "*>"),
            operator!(left 4 "<*>"),
            operator!(left 4 "<$>"),
            operator!(left 4 "<$"),
            operator!(4 "<"),
            operator!(4 "<="),
            operator!(4 ">"),
            operator!(4 ">="),
            operator!(4 "=="),
            operator!(4 "!="),
            operator!(right 5 "&"),
            operator!(right 5 "++"),
            operator!(left 6 "+"),
            operator!(left 6 "-"),
            operator!(left 7 "*"),
            operator!(left 7 "/"),
            operator!(left 7 "%"),
            operator!(right 8 "."),
        ]);

        Self { infix, prefix }
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
}

#[derive(Debug, Clone)]
pub struct Constructor<T> {
    pub name:   Ident,
    pub params: Box<[Ty]>,
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

#[derive(Clone)]
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

impl<T: Debug> Debug for Module<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Module")
            .field("name", &self.name)
            .field("exprs", &self.stmts)
            .finish_non_exhaustive()
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

#[derive(Clone)]
pub struct Pat<T> {
    pub kind: PatKind<T>,
    pub span: Span,
    pub ty:   T,
}

impl<T: Debug> Debug for Pat<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Pat")
            .field("kind", &self.kind)
            .field("ty", &self.ty)
            .finish_non_exhaustive()
    }
}

impl<T> Pat<T> {
    #[must_use]
    pub const fn new(kind: PatKind<T>, span: Span, ty: T) -> Self {
        Self { kind, span, ty }
    }
}

#[derive(Clone)]
pub struct Expr<T> {
    pub kind: ExprKind<T>,
    pub span: Span,
    pub ty:   T,
}

impl<T: Debug> Debug for Expr<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr")
            .field("kind", &self.kind)
            .field("ty", &self.ty)
            .finish_non_exhaustive()
    }
}

#[derive(Clone)]
pub struct Stmt<T> {
    pub kind: StmtKind<T>,
    pub span: Span,
}

impl<T> Stmt<T> {
    pub const fn new(kind: StmtKind<T>, span: Span) -> Self {
        Self { kind, span }
    }
}

impl<T: Debug> Debug for Stmt<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Stmt")
            .field("kind", &self.kind)
            .finish_non_exhaustive()
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
    pub name:   Ident,
    pub params: Box<[Param<T>]>,
    pub expr:   Expr<T>,
}

impl<T> LetBind<T> {
    pub const fn new(name: Ident, params: Box<[Param<T>]>, expr: Expr<T>) -> Self {
        Self { name, params, expr }
    }
}

#[derive(Debug, Clone)]
pub struct ValDeclaration {
    pub params: Box<[Ty]>,
    pub set:    ClassConstraintSet,
    pub name:   Ident,
    pub ty:     Ty,
    pub span:   Span,
}

#[derive(Debug, Clone)]
pub struct OpDeclaration {
    pub prefix: bool,
    pub op:     Symbol,
    pub ty:     Ty,
}

impl OpDeclaration {
    pub const fn new(prefix: bool, op: Symbol, ty: Ty) -> Self {
        Self { prefix, op, ty }
    }
}

impl Display for OpDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}): {}", self.op, self.ty)
    }
}

#[derive(Debug, Clone)]
pub enum StmtKind<T> {
    Semi(Expr<T>),

    Operator {
        params: Box<[Ty]>,
        set:    ClassConstraintSet,
        ops:    Box<[OpDeclaration]>,
    },

    Val(ValDeclaration),

    Class {
        set:        ClassConstraintSet,
        name:       Ident,
        instance:   Ident,
        signatures: Box<[ValDeclaration]>,
        defaults:   Box<[LetBind<T>]>,
    },

    Instance {
        params:   Box<[Ty]>,
        set:      ClassConstraintSet,
        class:    Path,
        instance: Ty,
        impls:    Box<[LetBind<T>]>,
    },

    Type {
        name:         Ident,
        parameters:   Box<[Ty]>,
        constructors: Box<[Constructor<T>]>,
    },

    Alias {
        name:       Ident,
        parameters: Box<[Ty]>,
        ty:         Ty,
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

    Let {
        bind: Box<LetBind<T>>,
        body: Option<Box<Expr<T>>>,
    },

    Bin {
        op:  Ident,
        lhs: Box<Expr<T>>,
        rhs: Box<Expr<T>>,
    },

    Un {
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

impl<T> StmtKind<T> {
    #[must_use]
    pub const fn is_type_or_val_or_op(&self) -> bool {
        matches!(
            self,
            Self::Type { .. } | Self::Val { .. } | Self::Operator { .. }
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
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.pat.substitute(subs);
    }
}

impl Substitute for Constructor<()> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        for param in &mut self.params {
            param.substitute(subs);
        }
    }
}

impl Substitute for Constructor<Ty> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.ty.substitute(subs);
        for param in &mut self.params {
            param.substitute(subs);
        }
    }
}

impl Substitute for ValDeclaration {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.set.substitute(subs);
        self.ty.substitute(subs);
        for p in &mut self.params {
            p.substitute(subs);
        }
    }
}

impl Substitute for Stmt<()> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match &mut self.kind {
            StmtKind::Type { constructors, .. } => {
                for c in constructors {
                    for t in &mut c.params {
                        t.substitute(subs);
                    }
                }
            }
            StmtKind::Alias { ty, .. } => {
                ty.substitute(subs);
            }
            StmtKind::Val(val) => {
                val.substitute(subs);
            }
            StmtKind::Class { signatures, .. } => {
                for sig in signatures {
                    sig.substitute(subs);
                }
            }
            StmtKind::Instance { instance, .. } => {
                instance.substitute(subs);
            }
            StmtKind::Operator { ops, .. } => {
                for op in ops {
                    op.ty.substitute(subs);
                }
            }
            StmtKind::Semi(_) => (),
        }
    }
}

impl Substitute for LetBind<Ty> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.expr.substitute(subs);
        for p in &mut self.params {
            p.substitute(subs);
        }
    }
}

impl Substitute for StmtKind<Ty> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match self {
            Self::Semi(semi) => {
                semi.substitute(subs);
            }
            Self::Type { constructors, .. } => {
                for c in constructors {
                    for t in &mut c.params {
                        t.substitute(subs);
                    }
                }
            }
            Self::Alias { ty, .. } => {
                ty.substitute(subs);
            }
            Self::Val(val) => {
                val.substitute(subs);
            }
            Self::Class {
                set,
                signatures,
                defaults,
                ..
            } => {
                set.substitute(subs);
                for sig in signatures {
                    sig.substitute(subs);
                }
                for bind in defaults {
                    bind.substitute(subs);
                }
            }
            Self::Instance {
                params,
                set,
                instance,
                impls,
                ..
            } => {
                set.substitute(subs);
                instance.substitute(subs);
                for i in impls {
                    i.substitute(subs);
                }
                for p in params {
                    p.substitute(subs);
                }
            }
            Self::Operator { params, set, ops } => {
                set.substitute(subs);
                for p in params {
                    p.substitute(subs);
                }
                for op in ops {
                    op.ty.substitute(subs);
                }
            }
        }
    }
}

impl Substitute for Stmt<Ty> {
    #[inline]
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.kind.substitute(subs);
    }
}

impl Substitute for Expr<Ty> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match &mut self.kind {
            ExprKind::Let { bind, body } => {
                bind.substitute(subs);
                if let Some(body) = body.as_mut() {
                    body.substitute(subs);
                }
            }
            ExprKind::Fn { param, expr } => {
                param.substitute(subs);
                expr.substitute(subs);
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                cond.substitute(subs);
                then.substitute(subs);
                otherwise.substitute(subs);
            }
            ExprKind::Call { callee, arg } => {
                callee.substitute(subs);
                arg.substitute(subs);
            }
            ExprKind::Match { expr, arms } => {
                expr.substitute(subs);
                for arm in arms {
                    arm.pat.substitute(subs);
                    arm.expr.substitute(subs);
                }
            }
            ExprKind::List(exprs) | ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    expr.substitute(subs);
                }
            }
            ExprKind::Bin { lhs, rhs, .. } => {
                lhs.substitute(subs);
                rhs.substitute(subs);
            }
            ExprKind::Un { expr, .. } => {
                expr.substitute(subs);
            }

            ExprKind::Operator(_)
            | ExprKind::Int(_)
            | ExprKind::Real(_)
            | ExprKind::String(_)
            | ExprKind::Bool(_)
            | ExprKind::Char(_)
            | ExprKind::Path(_) => (),
        }

        self.ty.substitute(subs);
    }
}

impl<T> Substitute for Module<T>
where
    Stmt<T>: Substitute,
{
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        for e in &mut self.stmts {
            e.substitute(subs);
        }
    }
}

impl Substitute for ListPat<Ty> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match self {
            Self::Nil => (),
            Self::Single(pat) => {
                pat.substitute(subs);
            }
            Self::Cons(pat, pat1) => {
                pat.substitute(subs);
                pat1.substitute(subs);
            }
        }
    }
}

impl Substitute for Pat<Ty> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match &mut self.kind {
            PatKind::Tuple(args) | PatKind::Or(args) | PatKind::Constructor { args, .. } => {
                for p in args {
                    p.substitute(subs);
                }
            }

            PatKind::List(list) => {
                list.substitute(subs);
            }

            PatKind::Wild
            | PatKind::Int(_)
            | PatKind::Bool(_)
            | PatKind::Ident(_)
            | PatKind::Real(_)
            | PatKind::Char(_)
            | PatKind::IntRange(_)
            | PatKind::CharRange(_)
            | PatKind::RealRange(_) => (),
        }
        self.ty.substitute(subs);
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.ident, f)
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for segment in &self.segments {
            if first {
                first = false;
            } else {
                write!(f, "::")?;
            }
            write!(f, "{segment}")?;
        }
        Ok(())
    }
}

pub type UntypedModule = Module<()>;
pub type UntypedExpr = Expr<()>;
pub type UntypedLetBind = LetBind<()>;
pub type UntypedPat = Pat<()>;
pub type UntypedStmt = Stmt<()>;
pub type UntypedMatchArm = MatchArm<()>;
pub type UntypedParam = Param<()>;
pub type UntypedConstructor = Constructor<()>;

impl UntypedExpr {
    #[must_use]
    pub const fn untyped(kind: ExprKind<()>, span: Span) -> Self {
        Self::new(kind, span, ())
    }
}

impl UntypedPat {
    #[must_use]
    pub const fn untyped(kind: PatKind<()>, span: Span) -> Self {
        Self::new(kind, span, ())
    }
}
