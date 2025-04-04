pub mod typed;
pub mod untyped;

use std::fmt::{Debug, Display, Write};

use super::infer::Substitute;
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
    /// Returns `true` if the bin op is [`Pipe`].
    ///
    /// [`Pipe`]: BinOp::Pipe
    #[must_use]
    pub const fn is_pipe(self) -> bool {
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
                | Self::Char(_)
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
            Self::LParen | Self::Ident(_) | Self::KwInt | Self::KwBool | Self::KwChar
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
                | Self::Char(_)
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
    pub span:   Span,
}

impl Display for Constructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        self.params.iter().try_for_each(|p| write!(f, " {p}"))
    }
}

#[derive(Clone)]
pub struct Module<T> {
    pub name:  Symbol,
    pub exprs: Vec<Expr<T>>,
    pub span:  Span,
}

impl<T> Module<T> {
    #[must_use]
    pub const fn new(name: Symbol, exprs: Vec<Expr<T>>, span: Span) -> Self {
        Self { name, exprs, span }
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
    pub const fn module(self) -> Symbol {
        self.module
    }

    #[must_use]
    pub const fn member(self) -> Symbol {
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
    pub const fn ident(&self) -> Symbol {
        match self {
            Self::Module(module_ident) => module_ident.member(),
            Self::Ident(symbol) => *symbol,
        }
    }

    #[must_use]
    pub const fn as_ident(&self) -> Option<Symbol> {
        if let Self::Ident(v) = self {
            Some(*v)
        } else {
            None
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
pub enum RangePat<T> {
    From(T),
    To(T),
    ToInclusive(T),
    Exclusive(T, T),
    Inclusive(T, T),
}

impl<T> RangePat<T> {
    pub fn map<U, F>(self, f: F) -> RangePat<U>
    where
        F: Fn(T) -> U,
    {
        match self {
            Self::From(lo) => RangePat::From(f(lo)),
            Self::To(hi) => RangePat::To(f(hi)),
            Self::ToInclusive(hi) => RangePat::ToInclusive(f(hi)),
            Self::Exclusive(lo, hi) => RangePat::Exclusive(f(lo), f(hi)),
            Self::Inclusive(lo, hi) => RangePat::Inclusive(f(lo), f(hi)),
        }
    }
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
pub enum PatKind<T> {
    Wild,

    Ident(Symbol),

    Or(Box<[Pat<T>]>),

    Tuple(Box<[Pat<T>]>),

    Int(i64),

    Char(u8),

    IntRange(RangePat<i64>),

    CharRange(RangePat<u8>),

    Bool(bool),

    Constructor {
        name: PathIdent,
        args: Box<[Pat<T>]>,
    },
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

impl<T: Display> Pat<T> {
    fn format_helper(&self, f: &mut impl Write) -> std::fmt::Result {
        match &self.kind {
            PatKind::Wild => write!(f, "_"),
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
            PatKind::Tuple(pats) => {
                write!(f, "(")?;
                let mut first = true;
                for pat in pats {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    pat.format_helper(f)?;
                }
                write!(f, ")")
            }
            PatKind::Int(i) => write!(f, "{i}"),
            PatKind::Char(c) => write!(f, "{:?}", *c as char),
            PatKind::IntRange(i) => write!(f, "{i}"),
            PatKind::CharRange(range) => write!(f, "{}", range.map(|c| c as char)),
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
        .and_then(|()| write!(f, ": {}", self.ty))
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
    pub name: Symbol,
    pub ty:   T,
    pub span: Span,
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
    Int(i64),

    Bool(bool),

    Char(u8),

    Ident(Symbol),

    Tuple(Box<[Expr<T>]>),

    ModuleIdent(ModuleIdent),

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
        name:      Symbol,
        name_span: Span,
        params:    Box<[Param<T>]>,
        expr:      Box<Expr<T>>,
        body:      Option<Box<Expr<T>>>,
    },

    Val {
        name:       Symbol,
        parameters: Box<[Ty]>,
        ty:         Ty,
        ty_span:    Span,
    },

    Type {
        name:         Symbol,
        parameters:   Box<[Ty]>,
        constructors: Box<[Constructor]>,
    },

    Alias {
        name:       Symbol,
        parameters: Box<[Ty]>,
        ty:         Ty,
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
    #[must_use]
    pub const fn is_type_or_val(&self) -> bool {
        match self {
            Self::Type { .. } | Self::Val { .. } => true,
            Self::Semi(e) => e.kind.is_type_or_val(),
            _ => false,
        }
    }
}

impl<T> Expr<T> {
    #[must_use]
    pub const fn new(kind: ExprKind<T>, span: Span, ty: T) -> Self {
        Self { kind, span, ty }
    }
}

impl<T: Display> Expr<T> {
    #[allow(clippy::too_many_lines)]
    fn format_helper(&self, f: &mut impl Write, indentation: usize) -> std::fmt::Result {
        let tab = String::from_utf8(vec![b' '; indentation * 2]).unwrap();
        match &self.kind {
            ExprKind::Semi(expr) => {
                expr.format_helper(f, indentation)?;
                write!(f, ";")
            }
            ExprKind::Int(i) => write!(f, "{i}"),
            ExprKind::Bool(b) => write!(f, "{b}"),
            ExprKind::Char(c) => write!(f, "\'{}\'", *c as char),
            ExprKind::Ident(id) => write!(f, "{id}"),
            ExprKind::Tuple(exprs) => {
                write!(f, "(")?;
                let mut first = true;
                for e in exprs {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    e.format_helper(f, indentation + 1)?;
                }
                write!(f, ")")
            }
            ExprKind::Bin { op, lhs, rhs } => {
                write!(f, "(")?;
                lhs.format_helper(f, indentation + 1)?;
                write!(f, "{op}")?;
                rhs.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            ExprKind::Un { op, expr } => {
                write!(f, "({op} ")?;
                expr.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            ExprKind::Let {
                params,
                name: id,
                expr,
                body,
                ..
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
            ExprKind::Val {
                name,
                parameters,
                ty,
                ..
            } => {
                write!(f, "(val {name}")?;
                for t in parameters {
                    write!(f, " {t}")?;
                }
                write!(f, ": {ty})")
            }
            ExprKind::Alias {
                name,
                parameters,
                ty,
            } => {
                write!(f, "(alias {name}")?;
                for t in parameters {
                    write!(f, " {t}")?;
                }
                write!(f, "= {ty})")
            }
            ExprKind::Type {
                name: id,
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
            ExprKind::ModuleIdent(module_access) => write!(f, "{module_access}"),
        }
        .and_then(|()| write!(f, ": {}", self.ty))
    }
}

impl<T: Display> Display for Expr<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.format_helper(f, 0)
    }
}

impl Substitute for Param<Ty> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.ty.substitute(subs);
    }
}

impl Substitute for Constructor {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        for param in &mut self.params {
            param.substitute(subs);
        }
    }
}

impl Substitute for Expr<()> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match &mut self.kind {
            ExprKind::Semi(semi) => {
                semi.substitute(subs);
            }
            ExprKind::Type { constructors, .. } => {
                for c in constructors {
                    for t in &mut c.params {
                        t.substitute(subs);
                    }
                }
            }
            ExprKind::Alias { ty, .. } | ExprKind::Val { ty, .. } => {
                ty.substitute(subs);
            }
            _ => (),
        }
    }
}

impl Substitute for Expr<Ty> {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        match &mut self.kind {
            ExprKind::Let {
                params, expr, body, ..
            } => {
                for p in params {
                    p.substitute(subs);
                }
                expr.substitute(subs);
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
            ExprKind::Semi(semi) => {
                semi.substitute(subs);
            }
            ExprKind::Type { constructors, .. } => {
                for c in constructors {
                    for t in &mut c.params {
                        t.substitute(subs);
                    }
                }
            }
            ExprKind::Val { ty, .. } | ExprKind::Alias { ty, .. } => {
                ty.substitute(subs);
            }
            ExprKind::Tuple(exprs) => {
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

            ExprKind::Int(_)
            | ExprKind::Bool(_)
            | ExprKind::Char(_)
            | ExprKind::Ident(_)
            | ExprKind::ModuleIdent(_) => (),
        }

        self.ty.substitute(subs);
    }
}

impl<T> Substitute for Module<T>
where
    Expr<T>: Substitute,
{
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        for e in &mut self.exprs {
            e.substitute(subs);
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

            PatKind::Wild
            | PatKind::Int(_)
            | PatKind::Bool(_)
            | PatKind::Ident(_)
            | PatKind::Char(_)
            | PatKind::IntRange(_)
            | PatKind::CharRange(_) => (),
        }
        self.ty.substitute(subs);
    }
}
