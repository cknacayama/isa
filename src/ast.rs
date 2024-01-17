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

    pub fn is_expr(&self) -> bool {
        use AstData::*;
        matches!(
            self.data,
            UnitExpr
                | BoolExpr(_)
                | IntExpr(_)
                | FloatExpr(_)
                | StringExpr(_)
                | CharExpr(_)
                | IdentExpr(_)
                | BinExpr { .. }
                | UnExpr { .. }
                | CallExpr { .. }
        )
    }

    pub fn is_stmt(&self) -> bool {
        use AstData::*;
        matches!(
            self.data,
            ReturnStmt(_) | IfStmt { .. } | WhileStmt { .. } | BlockStmt(_)
        )
    }

    pub fn is_decl(&self) -> bool {
        use AstData::*;
        matches!(self.data, LetDecl { .. } | ProcDecl { .. })
    }
}

impl Spanned for Ast<'_> {
    #[inline(always)]
    fn span(&self) -> Span {
        self.span
    }
}
