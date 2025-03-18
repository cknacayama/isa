use std::{fmt::Display, rc::Rc};

use super::{ast::TypedExpr, env::TypeEnv, error::InferError, types::Type};

pub type InferResult<T> = Result<T, InferError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Subs {
    var: u64,
    ty:  Rc<Type>,
}

impl Subs {
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
        self.visit(&mut |e| e.ty = e.ty.clone().substitute(subs, env));
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
        for c in self.constrs.iter_mut() {
            *c = c.clone().substitute(subs, env);
        }
        self
    }
}

impl ConstrSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn append(&mut self, mut other: Self) {
        self.constrs.append(&mut other.constrs)
    }

    pub fn push(&mut self, c: Constr) {
        self.constrs.push(c)
    }

    pub fn unify(mut self, env: &mut TypeEnv) -> InferResult<Vec<Subs>> {
        let mut subs = Vec::new();

        while let Some(c) = self.constrs.pop() {
            match (c.lhs.as_ref(), c.rhs.as_ref()) {
                (
                    lhs @ (Type::Int | Type::Bool | Type::Var(_)),
                    rhs @ (Type::Int | Type::Bool | Type::Var(_)),
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
        self.constrs.iter().try_for_each(|c| write!(f, "{}, ", c))
    }
}
