use super::{
    infer::{Subs, Substitute},
    types::Type,
};
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

#[derive(Debug, Clone, Default)]
pub struct Env {
    env: HashMap<Rc<str>, Rc<Type>>,
}

#[derive(Debug, Clone)]
pub struct TypeEnv {
    types: HashSet<Rc<Type>>,
}

impl Default for TypeEnv {
    fn default() -> Self {
        let types = HashSet::from([Rc::new(Type::Unit), Rc::new(Type::Int), Rc::new(Type::Bool)]);

        Self { types }
    }
}

impl TypeEnv {
    pub fn get_type(&mut self, ty: Type) -> Rc<Type> {
        match self.types.get(&ty) {
            Some(ty) => ty.clone(),
            None => {
                let ty = Rc::new(ty);
                self.types.insert(ty.clone());
                ty
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Rc<Type>> {
        self.types.iter()
    }

    pub fn get_unit(&self) -> Rc<Type> {
        self.types.get(&Type::Unit).unwrap().clone()
    }

    pub fn get_int(&self) -> Rc<Type> {
        self.types.get(&Type::Int).unwrap().clone()
    }

    pub fn get_bool(&self) -> Rc<Type> {
        self.types.get(&Type::Bool).unwrap().clone()
    }
}

impl Substitute for Env {
    fn substitute(mut self, subs: &Subs, env: &mut TypeEnv) -> Self {
        for t in self.env.values_mut() {
            *t = t.clone().substitute(subs, env);
        }
        self
    }
}

impl Env {
    pub fn get(&self, id: &str) -> Option<&Rc<Type>> {
        self.env.get(id)
    }

    pub fn insert(&mut self, id: Rc<str>, ty: Rc<Type>) -> Option<Rc<Type>> {
        self.env.insert(id, ty)
    }

    pub fn remove(&mut self, id: &str) -> Option<Rc<Type>> {
        self.env.remove(id)
    }

    pub fn contains_type(&self, ty: &Type) -> bool {
        self.env.values().any(|t| t.as_ref() == ty)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Rc<str>, &Rc<Type>)> {
        self.env.iter()
    }

    fn gen_helper(&self, ty: &Type) -> Vec<u64> {
        match ty {
            Type::Fn { param, ret } => {
                let mut res = self.gen_helper(param);
                for n in self.gen_helper(ret) {
                    if !res.contains(&n) {
                        res.push(n);
                    }
                }
                res
            }
            ty @ Type::Var(n) if !&self.contains_type(ty) => {
                vec![*n]
            }
            Type::Generic { quant, ty } => {
                let mut res = self.gen_helper(ty);
                for n in quant {
                    if !res.contains(n) {
                        res.push(*n);
                    }
                }
                res
            }
            Type::Named { args, .. } => args
                .iter()
                .map(|t| self.gen_helper(t))
                .reduce(|mut acc, mut e| {
                    acc.append(&mut e);
                    acc
                })
                .unwrap_or_else(Vec::new),
            _ => Vec::new(),
        }
    }

    pub fn generalize(&self, ty: Rc<Type>, type_env: &mut TypeEnv) -> Rc<Type> {
        let mut quantifiers = self.gen_helper(&ty);

        if quantifiers.is_empty() {
            return ty;
        }

        let ty = match ty.as_ref() {
            Type::Generic { quant, ty } => {
                quantifiers.extend_from_slice(quant);
                Type::Generic {
                    quant: quantifiers.into_boxed_slice(),
                    ty:    ty.clone(),
                }
            }
            _ => Type::Generic {
                quant: quantifiers.into_boxed_slice(),
                ty,
            },
        };

        type_env.get_type(ty)
    }
}
