use std::{fmt::Display, rc::Rc};

use super::{
    env::TypeEnv,
    error::InferError,
    types::{Fn, Type},
};

pub type InferResult<'a, T> = Result<T, InferError<'a>>;

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

impl Substitute for Rc<Type> {
    fn substitute(self, subs: &Subs, env: &mut TypeEnv) -> Self {
        match self.as_ref() {
            Type::Fn(f) => {
                let ty = Type::Fn(Fn::new(
                    f.param.clone().substitute(subs, env),
                    f.ret.clone().substitute(subs, env),
                ));
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

    pub fn unify(mut self, env: &mut TypeEnv) -> InferResult<'static, Vec<Subs>> {
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
                (Type::Fn(f1), Type::Fn(f2)) => {
                    let i1 = f1.param.clone();
                    let i2 = f2.param.clone();
                    let o1 = f1.ret.clone();
                    let o2 = f2.ret.clone();

                    let c1 = Constr::new(i1, i2);
                    let c2 = Constr::new(o1, o2);

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
        write!(f, "{} / '{}", self.ty, self.var)
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
