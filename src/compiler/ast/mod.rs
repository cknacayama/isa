pub mod typed;
pub mod untyped;

use std::fmt::{Debug, Display, Write};

use rustc_hash::FxHashMap;

use super::env::VarData;
use super::token::TokenKind;
use super::types::Ty;
use crate::global::Symbol;
use crate::span::Span;

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
    And,
    Or,
    Pipe,
}

impl BinOp {
    #[must_use]
    pub const fn from_token(tk: TokenKind) -> Option<Self> {
        match tk {
            TokenKind::Plus => Some(Self::Add),
            TokenKind::Minus => Some(Self::Sub),
            TokenKind::Star => Some(Self::Mul),
            TokenKind::Slash => Some(Self::Div),
            TokenKind::Percent => Some(Self::Rem),
            TokenKind::Eq => Some(Self::Eq),
            TokenKind::BangEq => Some(Self::Ne),
            TokenKind::Gt => Some(Self::Gt),
            TokenKind::Ge => Some(Self::Ge),
            TokenKind::Lt => Some(Self::Lt),
            TokenKind::Le => Some(Self::Le),
            TokenKind::KwAnd => Some(Self::And),
            TokenKind::KwOr => Some(Self::Or),
            TokenKind::Pipe => Some(Self::Pipe),

            _ => None,
        }
    }

    /// Returns `true` if the bin op is [`Pipe`].
    ///
    /// [`Pipe`]: BinOp::Pipe
    #[must_use]
    pub const fn is_pipe(&self) -> bool {
        matches!(self, Self::Pipe)
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::Rem => write!(f, "%"),
            Self::Eq => write!(f, "="),
            Self::Ne => write!(f, "!="),
            Self::Gt => write!(f, ">"),
            Self::Ge => write!(f, ">="),
            Self::Lt => write!(f, "<"),
            Self::Le => write!(f, "<="),
            Self::And => write!(f, "and"),
            Self::Or => write!(f, "or"),
            Self::Pipe => write!(f, "|>"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Not,
    Neg,
}

impl UnOp {
    #[must_use]
    pub const fn from_token(tk: TokenKind) -> Option<Self> {
        match tk {
            TokenKind::KwNot => Some(Self::Not),
            TokenKind::Minus => Some(Self::Neg),
            _ => None,
        }
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Not => write!(f, "not"),
            Self::Neg => write!(f, "-"),
        }
    }
}

impl TokenKind {
    #[must_use]
    pub const fn can_start_expr(&self) -> bool {
        matches!(
            self,
            Self::LParen
                | Self::Integer(_)
                | Self::Ident(_)
                | Self::KwTrue
                | Self::KwFalse
                | Self::KwLet
                | Self::KwFn
                | Self::KwNot
                | Self::KwType
                | Self::KwMatch
                | Self::KwIf
        )
    }

    #[must_use]
    pub const fn can_start_type(&self) -> bool {
        matches!(
            self,
            Self::LParen | Self::Ident(_) | Self::KwInt | Self::KwBool
        )
    }

    #[must_use]
    pub const fn can_start_pat(&self) -> bool {
        matches!(
            self,
            Self::LParen
                | Self::DotDot
                | Self::DotDotEq
                | Self::Underscore
                | Self::Ident(_)
                | Self::Integer(_)
                | Self::KwTrue
                | Self::KwFalse
                | Self::KwNot
                | Self::Minus
        )
    }
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub name:   Symbol,
    pub params: Box<[Ty]>,
}

impl Constructor {
    #[must_use]
    pub const fn new(name: Symbol, params: Box<[Ty]>) -> Self {
        Self { name, params }
    }

    #[must_use]
    pub const fn params(&self) -> &[Ty] {
        &self.params
    }
}

impl Display for Constructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        self.params.iter().try_for_each(|p| write!(f, " {p}"))
    }
}

#[derive(Clone)]
pub struct Module<T> {
    pub name:     Option<Symbol>,
    pub declared: FxHashMap<Symbol, VarData>,
    pub exprs:    Box<[Expr<T>]>,
    pub span:     Span,
}

impl<T> Module<T> {
    #[must_use]
    pub const fn new(
        name: Option<Symbol>,
        declared: FxHashMap<Symbol, VarData>,
        exprs: Box<[Expr<T>]>,
        span: Span,
    ) -> Self {
        Self {
            name,
            declared,
            exprs,
            span,
        }
    }
}

impl<T: Debug> Debug for Module<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Module")
            .field("name", &self.name)
            .field("exprs", &self.exprs)
            .finish_non_exhaustive()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleIdent {
    module: Symbol,
    member: Symbol,
}

impl ModuleIdent {
    #[must_use]
    pub const fn new(module: Symbol, member: Symbol) -> Self {
        Self { module, member }
    }

    #[must_use]
    pub const fn module(&self) -> Symbol {
        self.module
    }

    #[must_use]
    pub const fn member(&self) -> Symbol {
        self.member
    }
}

impl Display for ModuleIdent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.module, self.member)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PathIdent {
    Module(ModuleIdent),
    Ident(Symbol),
}

impl PathIdent {
    #[must_use]
    pub fn ident(&self) -> Symbol {
        match self {
            Self::Module(module_ident) => module_ident.member(),
            Self::Ident(symbol) => *symbol,
        }
    }
}

impl Display for PathIdent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Module(module) => write!(f, "{module}"),
            Self::Ident(id) => write!(f, "{id}"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum IntRangePat {
    From(i64),
    To(i64),
    ToInclusive(i64),
    Exclusive(i64, i64),
    Inclusive(i64, i64),
}

impl Display for IntRangePat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::From(i) => write!(f, "{i}.."),
            Self::To(i) => write!(f, "..{i}"),
            Self::ToInclusive(i) => write!(f, "..={i}"),
            Self::Exclusive(lo, hi) => write!(f, "{lo}..{hi}"),
            Self::Inclusive(lo, hi) => write!(f, "{lo}..={hi}"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum PatKind<T> {
    Wild,

    Module(ModuleIdent),

    Ident(Symbol),

    Or(Box<[Pat<T>]>),

    Unit,

    Int(i64),

    IntRange(IntRangePat),

    Bool(bool),

    Constructor {
        name: PathIdent,
        args: Box<[Pat<T>]>,
    },
}

impl<T> PatKind<T> {
    /// Returns `true` if the pat kind is [`Module`].
    ///
    /// [`Module`]: PatKind::Module
    #[must_use]
    pub const fn is_module(&self) -> bool {
        matches!(self, Self::Module(..))
    }

    /// Returns `true` if the pat kind is [`Ident`].
    ///
    /// [`Ident`]: PatKind::Ident
    #[must_use]
    pub const fn is_ident(&self) -> bool {
        matches!(self, Self::Ident(..))
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

    fn format_helper(&self, f: &mut impl Write) -> std::fmt::Result {
        match &self.kind {
            PatKind::Wild => write!(f, "_"),
            PatKind::Module(module) => write!(f, "{module}"),
            PatKind::Ident(id) => write!(f, "{id}"),
            PatKind::Or(typed_pats) => {
                let mut iter = typed_pats.iter();
                let first = iter.next().unwrap();
                write!(f, "(")?;
                first.format_helper(f)?;
                for pat in iter {
                    write!(f, " | ")?;
                    pat.format_helper(f)?;
                }
                write!(f, ")")
            }
            PatKind::Unit => write!(f, "()"),
            PatKind::Int(i) => write!(f, "{i}"),
            PatKind::IntRange(i) => write!(f, "{i}"),
            PatKind::Bool(b) => write!(f, "{b}"),
            PatKind::Constructor { name, args } => {
                write!(f, "({name}")?;
                for pat in args {
                    write!(f, " ")?;
                    pat.format_helper(f)?;
                }
                write!(f, ")")
            }
        }
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

#[derive(Debug, Clone)]
pub struct MatchArm<T> {
    pub(crate) pat:  Pat<T>,
    pub(crate) expr: Expr<T>,
}

impl<T> MatchArm<T> {
    #[must_use]
    pub const fn new(pat: Pat<T>, expr: Expr<T>) -> Self {
        Self { pat, expr }
    }

    pub fn pat(&self) -> &Pat<T> {
        &self.pat
    }

    pub fn expr(&self) -> &Expr<T> {
        &self.expr
    }
}

impl<T: Display> MatchArm<T> {
    fn format_helper(&self, f: &mut impl Write, indentation: usize) -> std::fmt::Result {
        self.pat.format_helper(f)?;
        write!(f, " -> ")?;
        self.expr.format_helper(f, indentation)?;
        writeln!(f, ",")
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Param<T> {
    pub(crate) name: Symbol,
    pub(crate) ty:   T,
    pub(crate) span: Span,
}

impl<T> Param<T> {
    #[must_use]
    pub const fn new(name: Symbol, ty: T, span: Span) -> Self {
        Self { name, ty, span }
    }

    #[must_use]
    pub const fn ty(&self) -> &T {
        &self.ty
    }
}

impl<T: Display> Display for Param<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.ty)
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind<T> {
    Unit,

    Int(i64),

    Bool(bool),

    Ident(Symbol),

    Acess(ModuleIdent),

    Bin {
        op:  BinOp,
        lhs: Box<Expr<T>>,
        rhs: Box<Expr<T>>,
    },

    Un {
        op:   UnOp,
        expr: Box<Expr<T>>,
    },

    Semi(Box<Expr<T>>),

    Let {
        id:     Symbol,
        params: Box<[Param<T>]>,
        expr:   Box<Expr<T>>,
        body:   Option<Box<Expr<T>>>,
    },

    Type {
        id:           Symbol,
        parameters:   Box<[Ty]>,
        constructors: Box<[Constructor]>,
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

impl<T> ExprKind<T> {
    /// Returns `true` if the expr kind is [`Match`].
    ///
    /// [`Match`]: ExprKind::Match
    #[must_use]
    pub fn is_match(&self) -> bool {
        matches!(self, Self::Match { .. })
    }
}

impl<T> Expr<T> {
    #[must_use]
    pub const fn new(kind: ExprKind<T>, span: Span, ty: T) -> Self {
        Self { kind, span, ty }
    }
}

impl<T: Display> Expr<T> {
    #[must_use]
    pub fn format(&self) -> String {
        let mut out = String::new();
        // String formatting is infallible
        let _ = self.format_helper(&mut out, 1);
        out
    }

    fn format_helper(&self, f: &mut impl Write, indentation: usize) -> std::fmt::Result {
        let tab = String::from_utf8(vec![b' '; indentation * 2]).unwrap();
        match &self.kind {
            ExprKind::Semi(expr) => {
                expr.format_helper(f, indentation)?;
                write!(f, ";")
            }
            ExprKind::Unit => write!(f, "()"),
            ExprKind::Int(i) => write!(f, "{i}"),
            ExprKind::Bool(b) => write!(f, "{b}"),
            ExprKind::Ident(id) => write!(f, "{id}"),
            ExprKind::Bin { op, lhs, rhs } => {
                write!(f, "(({op}) ")?;
                lhs.format_helper(f, indentation + 1)?;
                write!(f, " ")?;
                rhs.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            ExprKind::Un { op, expr } => {
                write!(f, "(({op}) ")?;
                expr.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            ExprKind::Let {
                params,
                id,
                expr,
                body,
            } => {
                write!(f, "(let {id} ")?;
                for p in params {
                    write!(f, "{p} ")?;
                }
                write!(f, "= ")?;
                expr.format_helper(f, indentation + 1)?;
                if let Some(body) = body {
                    writeln!(f, " in")?;
                    write!(f, "{tab}")?;
                    body.format_helper(f, indentation + 1)?;
                }
                write!(f, ")")
            }
            ExprKind::Type {
                id,
                parameters: params,
                constructors,
            } => {
                write!(f, "(type {id}")?;
                for p in params {
                    write!(f, " {p}")?;
                }
                writeln!(f, " =")?;
                for c in constructors {
                    writeln!(f, "{tab}| {c}")?;
                }
                write!(f, ")")
            }
            ExprKind::Fn { param, expr } => {
                write!(f, "(fn {param} -> ")?;
                expr.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                write!(f, "(if ")?;
                cond.format_helper(f, indentation + 1)?;
                writeln!(f, " then")?;
                write!(f, "{tab}")?;
                then.format_helper(f, indentation + 1)?;
                writeln!(f, " else")?;
                write!(f, "{tab}")?;
                otherwise.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            ExprKind::Match { expr, arms } => {
                write!(f, "(match ")?;
                expr.format_helper(f, indentation + 1)?;
                writeln!(f, " in")?;
                for arm in arms {
                    write!(f, "{tab}")?;
                    arm.format_helper(f, indentation)?;
                }
                write!(f, ")")
            }
            ExprKind::Call { callee, arg } => {
                write!(f, "(")?;
                callee.format_helper(f, indentation + 1)?;
                write!(f, " ")?;
                arg.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            ExprKind::Acess(module_access) => write!(f, "{module_access}"),
        }
        .and_then(|()| write!(f, ": {}", self.ty))
    }
}
