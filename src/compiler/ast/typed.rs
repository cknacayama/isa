use std::fmt::{Debug, Display, Write};
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::{BinOp, Constructor, UnOp};
use crate::compiler::types::Ty;
use crate::global::Symbol;
use crate::span::Span;

#[derive(Clone)]
pub struct TypedModule {
    pub name:     Option<Symbol>,
    pub declared: FxHashMap<Symbol, Rc<Ty>>,
    pub exprs:    Box<[TypedExpr]>,
    pub span:     Span,
}

impl TypedModule {
    #[must_use]
    pub const fn new(
        name: Option<Symbol>,
        declared: FxHashMap<Symbol, Rc<Ty>>,
        exprs: Box<[TypedExpr]>,
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

impl Debug for TypedModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypedModule")
            .field("name", &self.name)
            .field("exprs", &self.exprs)
            .finish_non_exhaustive()
    }
}

#[derive(Debug, Clone)]
pub enum TypedPatKind {
    Wild,

    Ident(Symbol),

    Or(Box<[TypedPat]>),

    Unit,

    Int(i64),

    Bool(bool),

    Type { name: Symbol, args: Box<[TypedPat]> },
}

#[derive(Clone)]
pub struct TypedPat {
    pub kind: TypedPatKind,
    pub span: Span,
    pub ty:   Rc<Ty>,
}

impl Debug for TypedPat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypedPat")
            .field("kind", &self.kind)
            .field("ty", &self.ty)
            .finish_non_exhaustive()
    }
}
impl TypedPat {
    #[must_use]
    pub const fn new(kind: TypedPatKind, span: Span, ty: Rc<Ty>) -> Self {
        Self { kind, span, ty }
    }

    fn format_helper(&self, f: &mut impl Write) -> std::fmt::Result {
        match &self.kind {
            TypedPatKind::Wild => write!(f, "_"),
            TypedPatKind::Ident(id) => write!(f, "{id}"),
            TypedPatKind::Or(typed_pats) => {
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
            TypedPatKind::Unit => write!(f, "()"),
            TypedPatKind::Int(i) => write!(f, "{i}"),
            TypedPatKind::Bool(b) => write!(f, "{b}"),
            TypedPatKind::Type { name, args } => {
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
pub struct TypedExpr {
    pub kind: TypedExprKind,
    pub span: Span,
    pub ty:   Rc<Ty>,
}

impl Debug for TypedExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr")
            .field("kind", &self.kind)
            .field("ty", &self.ty)
            .finish_non_exhaustive()
    }
}

#[derive(Debug, Clone)]
pub struct TypedMatchArm {
    pub pat:  TypedPat,
    pub expr: TypedExpr,
}

impl TypedMatchArm {
    #[must_use]
    pub const fn new(pat: TypedPat, expr: TypedExpr) -> Self {
        Self { pat, expr }
    }

    fn format_helper(&self, f: &mut impl Write, indentation: usize) -> std::fmt::Result {
        self.pat.format_helper(f)?;
        write!(f, " -> ")?;
        self.expr.format_helper(f, indentation)?;
        writeln!(f, ",")
    }
}

#[derive(Debug, Clone)]
pub struct TypedParam {
    pub name: Symbol,
    pub ty:   Rc<Ty>,
}

impl TypedParam {
    #[must_use]
    pub const fn new(name: Symbol, ty: Rc<Ty>) -> Self {
        Self { name, ty }
    }

    #[must_use]
    pub const fn ty(&self) -> &Rc<Ty> {
        &self.ty
    }
}

impl Display for TypedParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.ty)
    }
}

#[derive(Debug, Clone)]
pub enum TypedExprKind {
    Unit,

    Int(i64),

    Bool(bool),

    Ident(Symbol),

    Bin {
        op:  BinOp,
        lhs: Box<TypedExpr>,
        rhs: Box<TypedExpr>,
    },

    Un {
        op:   UnOp,
        expr: Box<TypedExpr>,
    },

    Semi(Box<TypedExpr>),

    Let {
        id:     Symbol,
        params: Box<[TypedParam]>,
        expr:   Box<TypedExpr>,
        body:   Option<Box<TypedExpr>>,
    },

    Type {
        id:           Symbol,
        parameters:   Box<[Rc<Ty>]>,
        constructors: Box<[Constructor]>,
    },

    Fn {
        param: TypedParam,
        expr:  Box<TypedExpr>,
    },

    Match {
        expr: Box<TypedExpr>,
        arms: Box<[TypedMatchArm]>,
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

impl TypedExpr {
    #[must_use]
    pub const fn new(kind: TypedExprKind, span: Span, ty: Rc<Ty>) -> Self {
        Self { kind, span, ty }
    }

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
            TypedExprKind::Semi(expr) => {
                expr.format_helper(f, indentation)?;
                write!(f, ";")
            }
            TypedExprKind::Unit => write!(f, "()"),
            TypedExprKind::Int(i) => write!(f, "{i}"),
            TypedExprKind::Bool(b) => write!(f, "{b}"),
            TypedExprKind::Ident(id) => write!(f, "{id}"),
            TypedExprKind::Bin { op, lhs, rhs } => {
                write!(f, "(({op}) ")?;
                lhs.format_helper(f, indentation + 1)?;
                write!(f, " ")?;
                rhs.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            TypedExprKind::Un { op, expr } => {
                write!(f, "(({op}) ")?;
                expr.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            TypedExprKind::Let {
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
            TypedExprKind::Type {
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
            TypedExprKind::Fn { param, expr } => {
                write!(f, "(fn {param} -> ")?;
                expr.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
            TypedExprKind::If {
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
            TypedExprKind::Match { expr, arms } => {
                write!(f, "(match ")?;
                expr.format_helper(f, indentation + 1)?;
                writeln!(f, " in")?;
                for arm in arms {
                    write!(f, "{tab}")?;
                    arm.format_helper(f, indentation)?;
                }
                write!(f, ")")
            }
            TypedExprKind::Call { callee, arg } => {
                write!(f, "(")?;
                callee.format_helper(f, indentation + 1)?;
                write!(f, " ")?;
                arg.format_helper(f, indentation + 1)?;
                write!(f, ")")
            }
        }
        .and_then(|()| write!(f, ": {}", self.ty))
    }
}
