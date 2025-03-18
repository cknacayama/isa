use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

use crate::span::{Span, Spanned};

use super::{token::TokenKind, types::Type};

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
}

impl BinOp {
    #[must_use]
    pub fn from_token(tk: TokenKind<'_>) -> Option<Self> {
        match tk {
            TokenKind::Plus => Some(BinOp::Add),
            TokenKind::Minus => Some(BinOp::Sub),
            TokenKind::Star => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            TokenKind::Percent => Some(BinOp::Rem),
            TokenKind::EqEq => Some(BinOp::Eq),
            TokenKind::BangEq => Some(BinOp::Ne),
            TokenKind::Gt => Some(BinOp::Gt),
            TokenKind::Ge => Some(BinOp::Ge),
            TokenKind::Lt => Some(BinOp::Lt),
            TokenKind::Le => Some(BinOp::Le),
            TokenKind::KwAnd => Some(BinOp::And),
            TokenKind::KwOr => Some(BinOp::Or),

            _ => None,
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
    pub fn from_token(tk: TokenKind<'_>) -> Option<Self> {
        match tk {
            TokenKind::KwNot => Some(UnOp::Not),
            TokenKind::Minus => Some(UnOp::Neg),
            _ => None,
        }
    }
}

#[derive(Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl From<Spanned<ExprKind>> for Expr {
    fn from(value: Spanned<ExprKind>) -> Self {
        Self::new(value.data, value.span)
    }
}

impl Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr")
            .field("kind", &self.kind)
            .finish_non_exhaustive()
    }
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub id:     Rc<str>,
    pub params: Box<[Rc<Type>]>,
}

impl Constructor {
    #[must_use]
    pub fn new(id: Rc<str>, params: Box<[Rc<Type>]>) -> Self {
        Self { id, params }
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

#[derive(Clone)]
pub struct TypedExpr {
    pub kind: TypedExprKind,
    pub span: Span,
    pub ty:   Rc<Type>,
}

impl Debug for TypedExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr")
            .field("kind", &self.kind)
            .field("ty", &self.ty)
            .finish_non_exhaustive()
    }
}

impl TypedExpr {
    #[must_use]
    pub fn new(kind: TypedExprKind, span: Span, ty: Rc<Type>) -> Self {
        Self { kind, span, ty }
    }

    pub fn visit<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Self),
    {
        match &mut self.kind {
            TypedExprKind::Let { expr, body, .. } => {
                expr.visit(f);
                if let Some(body) = body.as_mut() {
                    body.visit(f);
                }
            }
            TypedExprKind::Fn { expr, .. } => {
                expr.visit(f);
            }
            TypedExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                cond.visit(f);
                then.visit(f);
                otherwise.visit(f);
            }
            TypedExprKind::Call { callee, arg } => {
                callee.visit(f);
                arg.visit(f);
            }
            _ => (),
        }
        f(self);
    }
}

#[derive(Debug, Clone)]
pub enum TypedExprKind {
    Unit,

    Int(i64),

    Bool(bool),

    Ident(Rc<str>),

    BinOp(BinOp),

    UnOp(UnOp),

    Semi(Box<TypedExpr>),

    Let {
        rec:  bool,
        id:   Rc<str>,
        expr: Box<TypedExpr>,
        body: Option<Box<TypedExpr>>,
    },

    Type {
        id:           Rc<str>,
        parameters:   Box<[Rc<str>]>,
        constructors: Box<[Constructor]>,
    },

    Fn {
        param: Rc<str>,
        expr:  Box<TypedExpr>,
    },

    If {
        cond:      Box<TypedExpr>,
        then:      Box<TypedExpr>,
        otherwise: Box<TypedExpr>,
    },

    Call {
        callee: Box<TypedExpr>,
        arg:    Box<TypedExpr>,
    },
}

impl TokenKind<'_> {
    #[must_use]
    pub fn can_start_expr(&self) -> bool {
        matches!(
            self,
            TokenKind::LParen
                | TokenKind::Integer(_)
                | TokenKind::Ident(_)
                | TokenKind::KwTrue
                | TokenKind::KwFalse
                | TokenKind::KwLet
                | TokenKind::KwFn
                | TokenKind::KwNot
                | TokenKind::KwType
                | TokenKind::KwMatch
                | TokenKind::KwIf
        )
    }

    #[must_use]
    pub fn can_start_type(&self) -> bool {
        matches!(
            self,
            TokenKind::LParen | TokenKind::Ident(_) | TokenKind::KwInt | TokenKind::KwBool
        )
    }
    #[must_use]
    pub fn can_start_pat(&self) -> bool {
        matches!(
            self,
            TokenKind::LParen
                | TokenKind::Underscore
                | TokenKind::Ident(_)
                | TokenKind::Integer(_)
                | TokenKind::KwTrue
                | TokenKind::KwFalse
                | TokenKind::KwNot
                | TokenKind::Minus
        )
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Rem => write!(f, "%"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Ge => write!(f, ">="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::And => write!(f, "and"),
            BinOp::Or => write!(f, "or"),
        }
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "not"),
            UnOp::Neg => write!(f, "-"),
        }
    }
}

impl Display for Constructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)?;
        self.params.iter().try_for_each(|p| write!(f, " {p}"))
    }
}

impl Display for TypedExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TypedExprKind::Semi(expr) => write!(f, "{expr};"),
            TypedExprKind::Unit => write!(f, "()"),
            TypedExprKind::Int(i) => write!(f, "{i}"),
            TypedExprKind::Bool(b) => write!(f, "{b}"),
            TypedExprKind::Ident(id) => write!(f, "{id}"),
            TypedExprKind::BinOp(op) => write!(f, "{op}"),
            TypedExprKind::UnOp(op) => write!(f, "{op}"),
            TypedExprKind::Let {
                rec,
                id,
                expr,
                body: None,
            } => {
                write!(
                    f,
                    "(let {} {} = {})",
                    if *rec { "rec" } else { "" },
                    id,
                    expr
                )
            }
            TypedExprKind::Let {
                rec,
                id,
                expr,
                body: Some(body),
            } => {
                write!(
                    f,
                    "(let {} {} = {} in {})",
                    if *rec { "rec" } else { "" },
                    id,
                    expr,
                    body
                )
            }
            TypedExprKind::Type {
                id,
                parameters: params,
                constructors,
            } => {
                write!(f, "(type {id}")?;
                for p in params {
                    write!(f, " {p}")?;
                }
                write!(f, " =")?;
                for c in constructors {
                    write!(f, " | {c}")?;
                }
                write!(f, ")")
            }
            TypedExprKind::Fn { param, expr } => {
                write!(f, "(fn {param} -> {expr})")
            }
            TypedExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                write!(f, "(if {cond} then {then} else {otherwise})")
            }
            TypedExprKind::Call { callee, arg } => {
                write!(f, "({callee} {arg})")
            }
        }
        .and_then(|()| write!(f, ": {}", self.ty))
    }
}
