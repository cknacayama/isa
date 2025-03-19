use std::{fmt::Debug, rc::Rc};

use crate::span::{Span, Spanned};

use super::{BinOp, Constructor, UnOp};

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

#[derive(Debug, Clone)]
pub enum PatKind {
    Wild,

    Ident(Rc<str>),

    Or(Box<[Pat]>),

    Unit,

    Int(i64),

    Bool(bool),

    Type { name: Rc<str>, args: Box<[Pat]> },

    Guard { pat: Box<Pat>, guard: Expr },
}

pub type Pat = Spanned<PatKind>;

#[derive(Debug, Clone)]
pub enum ExprKind {
    Unit,

    Int(i64),

    Bool(bool),

    Ident(Rc<str>),

    BinOp(BinOp),

    UnOp(UnOp),

    Semi(Box<Expr>),

    Let {
        rec:  bool,
        id:   Rc<str>,
        expr: Box<Expr>,
        body: Option<Box<Expr>>,
    },

    Type {
        id:           Rc<str>,
        parameters:   Box<[Rc<str>]>,
        constructors: Box<[Constructor]>,
    },

    Fn {
        param: Rc<str>,
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
