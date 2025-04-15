use super::{Constructor, Expr, ExprKind, LetBind, MatchArm, Module, Param, Pat, PatKind};
use crate::compiler::token::Ident;
use crate::span::Span;

pub type UntypedModule = Module<()>;
pub type UntypedExpr = Expr<()>;
pub type UntypedLetBind = LetBind<()>;
pub type UntypedPatKind = PatKind<()>;
pub type UntypedPat = Pat<()>;
pub type UntypedExprKind = ExprKind<()>;
pub type UntypedMatchArm = MatchArm<()>;
pub type UntypedParam = Param<()>;
pub type UntypedConstructor = Constructor<()>;

impl UntypedExpr {
    #[must_use]
    pub const fn untyped(kind: UntypedExprKind, span: Span) -> Self {
        Self::new(kind, span, ())
    }
}

impl UntypedPat {
    #[must_use]
    pub const fn untyped(kind: UntypedPatKind, span: Span) -> Self {
        Self::new(kind, span, ())
    }
}

impl UntypedParam {
    #[must_use]
    pub const fn untyped(name: Ident) -> Self {
        Self::new(name, ())
    }
}
