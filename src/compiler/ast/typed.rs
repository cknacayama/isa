use std::rc::Rc;

use super::{Expr, ExprKind, MatchArm, Module, Param, Pat, PatKind};
use crate::compiler::types::Ty;

pub type TypedModule = Module<Rc<Ty>>;
pub type TypedExpr = Expr<Rc<Ty>>;
pub type TypedPatKind = PatKind<Rc<Ty>>;
pub type TypedPat = Pat<Rc<Ty>>;
pub type TypedExprKind = ExprKind<Rc<Ty>>;
pub type TypedMatchArm = MatchArm<Rc<Ty>>;
pub type TypedParam = Param<Rc<Ty>>;
