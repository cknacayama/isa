use super::{Expr, ExprKind, LetBind, MatchArm, Module, Param, Pat, PatKind};
use crate::compiler::types::Ty;

pub type TypedModule = Module<Ty>;
pub type TypedExpr = Expr<Ty>;
pub type TypedPatKind = PatKind<Ty>;
pub type TypedLetBind = LetBind<Ty>;
pub type TypedPat = Pat<Ty>;
pub type TypedExprKind = ExprKind<Ty>;
pub type TypedMatchArm = MatchArm<Ty>;
pub type TypedParam = Param<Ty>;
