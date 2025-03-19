use std::{fmt::Display, rc::Rc};

use crate::compiler::{
    ast::typed::{TypedExpr, TypedExprKind, TypedPat, TypedPatKind},
    env::TypeEnv,
    error::InferError,
    types::Type,
};

pub type InferResult<T> = Result<T, InferError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Subs {
    var: u64,
    ty:  Rc<Type>,
}

impl Subs {
    #[must_use]
    pub fn new(var: u64, ty: Rc<Type>) -> Self {
        Self { var, ty }
    }
}

pub trait Substitute {
    fn substitute(self, subs: &Subs, env: &mut TypeEnv) -> Self;

    fn substitute_many<'a, S>(self, subs: S, env: &mut TypeEnv) -> Self
    where
        Self: Sized,
        S: IntoIterator<Item = &'a Subs>,
    {
        subs.into_iter().fold(self, |ty, s| ty.substitute(s, env))
    }
}

impl Substitute for &mut TypedExpr {
    fn substitute(self, subs: &Subs, env: &mut TypeEnv) -> Self {
        match &mut self.kind {
            TypedExprKind::Let { expr, body, .. } => {
                expr.substitute(subs, env);
                if let Some(body) = body.as_mut() {
                    body.substitute(subs, env);
                }
            }

            TypedExprKind::Fn { expr, .. } => {
                expr.substitute(subs, env);
            }

            TypedExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                cond.substitute(subs, env);
                then.substitute(subs, env);
                otherwise.substitute(subs, env);
            }

            TypedExprKind::Call { callee, arg } => {
                callee.substitute(subs, env);
                arg.substitute(subs, env);
            }

            TypedExprKind::Match { expr, arms } => {
                expr.substitute(subs, env);
                arms.iter_mut().for_each(|(pat, expr)| {
                    pat.substitute(subs, env);
                    expr.substitute(subs, env);
                });
            }

            TypedExprKind::Unit
            | TypedExprKind::Int(_)
            | TypedExprKind::Bool(_)
            | TypedExprKind::Ident(_)
            | TypedExprKind::BinOp(_)
            | TypedExprKind::UnOp(_)
            | TypedExprKind::Semi(_)
            | TypedExprKind::Type { .. } => (),
        }
        self.ty = self.ty.clone().substitute(subs, env);
        self
    }
}

impl Substitute for &mut TypedPat {
    fn substitute(self, subs: &Subs, env: &mut TypeEnv) -> Self {
        match &mut self.kind {
            TypedPatKind::Or(args) | TypedPatKind::Type { args, .. } => {
                args.iter_mut().for_each(|p| {
                    p.substitute(subs, env);
                })
            }

            TypedPatKind::Guard { pat, guard } => {
                pat.substitute(subs, env);
                guard.substitute(subs, env);
            }

            TypedPatKind::Wild
            | TypedPatKind::Unit
            | TypedPatKind::Int(_)
            | TypedPatKind::Bool(_)
            | TypedPatKind::Ident(_) => (),
        }
        self.ty = self.ty.clone().substitute(subs, env);
        self
    }
}

impl Substitute for Rc<Type> {
    fn substitute(self, subs: &Subs, env: &mut TypeEnv) -> Self {
        match self.as_ref() {
            Type::Fn { param, ret } => {
                let ty = Type::Fn {
                    param: param.clone().substitute(subs, env),
                    ret:   ret.clone().substitute(subs, env),
                };
                env.get_type(ty)
            }
            Type::Var(n) if subs.var == *n => subs.ty.clone(),
            Type::Generic { quant, ty } => {
                let ty = ty.clone().substitute(subs, env);
                let quant = quant.clone();
                let ty = Type::Generic { quant, ty };
                env.get_type(ty)
            }
            Type::Named { name, args } => {
                let ty = Type::Named {
                    name: name.clone(),
                    args: args
                        .into_iter()
                        .cloned()
                        .map(|arg| arg.substitute(subs, env))
                        .collect(),
                };
                env.get_type(ty)
            }
            _ => self,
        }
    }
}

#[derive(Debug, Clone, Eq)]
pub struct Constr {
    lhs: Rc<Type>,
    rhs: Rc<Type>,
}

impl PartialEq for Constr {
    fn eq(&self, other: &Self) -> bool {
        (self.lhs.eq(&other.lhs) && self.rhs.eq(&other.rhs))
            || (self.lhs.eq(&other.rhs) && self.rhs.eq(&other.lhs))
    }
}

impl Substitute for Constr {
    fn substitute(self, subs: &Subs, env: &mut TypeEnv) -> Self {
        Self {
            lhs: self.lhs.substitute(subs, env),
            rhs: self.rhs.substitute(subs, env),
        }
    }
}

impl Constr {
    #[must_use]
    pub fn new(lhs: Rc<Type>, rhs: Rc<Type>) -> Self {
        Self { lhs, rhs }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ConstrSet {
    constrs: Vec<Constr>,
}

impl Substitute for ConstrSet {
    fn substitute(mut self, subs: &Subs, env: &mut TypeEnv) -> Self {
        for c in &mut self.constrs {
            *c = c.clone().substitute(subs, env);
        }
        self
    }
}

impl ConstrSet {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn append(&mut self, mut other: Self) {
        self.constrs.append(&mut other.constrs);
    }

    pub fn push(&mut self, c: Constr) {
        self.constrs.push(c);
    }

    pub fn unify(mut self, env: &mut TypeEnv) -> InferResult<Vec<Subs>> {
        let mut subs = Vec::new();

        while let Some(c) = self.constrs.pop() {
            match (c.lhs.as_ref(), c.rhs.as_ref()) {
                (
                    lhs @ (Type::Int | Type::Bool | Type::Var(_) | Type::Named { .. }),
                    rhs @ (Type::Int | Type::Bool | Type::Var(_) | Type::Named { .. }),
                ) if lhs == rhs => {}
                (Type::Var(var), other) | (other, Type::Var(var)) if !other.occurs(*var) => {
                    let other = env.get_type(other.clone());
                    let s = Subs {
                        var: *var,
                        ty:  other,
                    };

                    self = self.substitute(&s, env);

                    subs.push(s);
                }
                (Type::Fn { param: i1, ret: o1 }, Type::Fn { param: i2, ret: o2 }) => {
                    let c1 = Constr::new(i1.clone(), i2.clone());
                    let c2 = Constr::new(o1.clone(), o2.clone());

                    self.push(c1);
                    self.push(c2);
                }
                (
                    Type::Named {
                        name: n1,
                        args: args1,
                    },
                    Type::Named {
                        name: n2,
                        args: args2,
                    },
                ) if n1 == n2 && args1.len() == args2.len() => {
                    for (a1, a2) in args1.iter().zip(args2) {
                        let c = Constr::new(a1.clone(), a2.clone());
                        self.push(c);
                    }
                }
                _ => return Err(InferError::Uninferable(c)),
            }
        }

        Ok(subs)
    }
}

impl Display for Subs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{} |-> ({})", self.var, self.ty)
    }
}

impl Display for Constr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

impl Display for ConstrSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.constrs.iter().try_for_each(|c| write!(f, "{c}, "))
    }
}
