use crate::{
    error::{Span, Spanned},
    types::{BinOp, Type, UnOp},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Param<'a> {
    pub name: &'a str,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AstData<'a> {
    UnitExpr,
    BoolExpr(bool),
    IntExpr(u64),
    FloatExpr(f64),
    StringExpr(&'a str),
    CharExpr(char),
    IdentExpr(&'a str),

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
        callee: &'a str,
        args: Vec<Ast<'a>>,
    },

    ReturnStmt(Option<Box<Ast<'a>>>),

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
        is_mut: bool,
        value: Option<Box<Ast<'a>>>,
    },

    ProcDecl {
        name: &'a str,
        ret: Type,
        params: Vec<Param<'a>>,
        body: Vec<Ast<'a>>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ast<'a> {
    pub data: AstData<'a>,
    pub ty: Type,
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
