use super::{BinOp, Constructor, UnOp};
use crate::{
    global::Symbol,
    span::{Span, Spanned},
};
use std::fmt::Debug;

#[derive(Clone)]
pub struct Module {
    pub name:  Option<Symbol>,
    pub exprs: Box<[Expr]>,
    pub span:  Span,
}

impl Module {
    #[must_use] pub fn new(name: Option<Symbol>, exprs: Box<[Expr]>, span: Span) -> Self {
        Self { name, exprs, span }
    }
}

impl Debug for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Module")
            .field("name", &self.name)
            .field("exprs", &self.exprs)
            .finish_non_exhaustive()
    }
}

#[derive(Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr")
            .field("kind", &self.kind)
            .finish_non_exhaustive()
    }
}

impl Expr {
    #[must_use]
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }

    #[must_use]
    pub fn bin_expr(op: BinOp, lhs: Expr, rhs: Expr, span: Span) -> Self {
        let op = Self::new(ExprKind::BinOp(op), span);
        let lhs_span = lhs.span;
        let c1 = Self::new(
            ExprKind::Call {
                callee: Box::new(op),
                arg:    Box::new(lhs),
            },
            lhs_span,
        );
        Self::new(
            ExprKind::Call {
                callee: Box::new(c1),
                arg:    Box::new(rhs),
            },
            span,
        )
    }
}

#[derive(Debug, Clone)]
pub enum PatKind {
    Wild,

    Ident(Symbol),

    Or(Box<[Pat]>),

    Unit,

    Int(i64),

    Bool(bool),

    Type { name: Symbol, args: Box<[Pat]> },
}

pub type Pat = Spanned<PatKind>;

#[derive(Debug, Clone)]
pub enum ExprKind {
    Unit,

    Int(i64),

    Bool(bool),

    Ident(Symbol),

    BinOp(BinOp),

    UnOp(UnOp),

    Semi(Box<Expr>),

    Let {
        rec:    bool,
        id:     Symbol,
        params: Box<[Symbol]>,
        expr:   Box<Expr>,
        body:   Option<Box<Expr>>,
    },

    Type {
        id:           Symbol,
        parameters:   Box<[Symbol]>,
        constructors: Box<[Constructor]>,
    },

    Fn {
        param: Symbol,
        expr:  Box<Expr>,
    },

    Match {
        expr: Box<Expr>,
        arms: Box<[(Pat, Expr)]>,
    },

    If {
        cond:      Box<Expr>,
        then:      Box<Expr>,
        otherwise: Box<Expr>,
    },

    Call {
        callee: Box<Expr>,
        arg:    Box<Expr>,
    },
}
