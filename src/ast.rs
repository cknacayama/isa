use std::rc::Rc;

use derivative::Derivative;

use crate::{span::*, types::*};

#[derive(Debug, Clone, PartialEq)]
pub enum AstData<'a> {
    UnitExpr,
    BoolExpr(bool),
    IntExpr(u64),
    FloatExpr(f64),
    StringExpr(&'a str),
    CharExpr(char),
    IdentExpr(&'a str),
    ArrayExpr(Vec<Ast<'a>>),
    ProcExpr {
        sig: Rc<ProcSig>,
        params: Vec<&'a str>,
        body: Vec<Ast<'a>>,
    },

    BinExpr {
        op: BinOp,
        lhs: Box<Ast<'a>>,
        rhs: Box<Ast<'a>>,
    },

    UnExpr {
        op: UnOp,
        expr: Box<Ast<'a>>,
    },

    CallExpr {
        callee: Box<Ast<'a>>,
        args: Vec<Ast<'a>>,
    },

    IndexExpr {
        array: Box<Ast<'a>>,
        index: Box<Ast<'a>>,
    },

    ReturnStmt(Box<Ast<'a>>),

    IfStmt {
        cond: Box<Ast<'a>>,
        then: Box<Ast<'a>>,
        else_: Option<Box<Ast<'a>>>,
    },

    WhileStmt {
        cond: Box<Ast<'a>>,
        body: Box<Ast<'a>>,
    },

    BlockStmt(Vec<Ast<'a>>),

    LetDecl {
        name: &'a str,
        ty: Type,
        value: Option<Box<Ast<'a>>>,
    },

    ProcDecl {
        sig: Rc<ProcSig>,
        name: &'a str,
        params: Vec<&'a str>,
        body: Vec<Ast<'a>>,
    },
}

#[derive(Derivative, Clone, PartialEq)]
#[derivative(Debug)]
pub struct Ast<'a> {
    pub data: AstData<'a>,
    pub ty: Type,

    #[derivative(Debug = "ignore")]
    pub span: Span,
}

impl<'a> Ast<'a> {
    pub fn new(data: AstData<'a>, ty: Type, span: Span) -> Self {
        Self { data, ty, span }
    }
}

impl Spanned for Ast<'_> {
    #[inline(always)]
    fn span(&self) -> Span {
        self.span
    }
}
