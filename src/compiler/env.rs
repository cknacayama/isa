use super::{
    infer::{Subs, Substitute},
    types::{Fn, Type},
};
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

#[derive(Debug, Clone, Default)]
pub struct Env<'a> {
    env: HashMap<&'a str, Rc<Type>>,
}

#[derive(Debug, Clone)]
pub struct TypeEnv {
    types: HashSet<Rc<Type>>,
}

impl Default for TypeEnv {
    fn default() -> Self {
        let types = HashSet::from([Rc::new(Type::Int), Rc::new(Type::Bool)]);

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

    pub fn get_int(&self) -> Rc<Type> {
        self.types.get(&Type::Int).unwrap().clone()
    }

    pub fn get_bool(&self) -> Rc<Type> {
        self.types.get(&Type::Bool).unwrap().clone()
    }
}

impl Substitute for Env<'_> {
    fn substitute(mut self, subs: &Subs, env: &mut TypeEnv) -> Self {
        for t in self.env.values_mut() {
            *t = t.clone().substitute(subs, env);
        }
        self
    }
}

impl<'a> Env<'a> {
    pub fn get(&self, id: &'a str) -> Option<&Rc<Type>> {
        self.env.get(id)
    }

    pub fn insert(&mut self, id: &'a str, ty: Rc<Type>) -> Option<Rc<Type>> {
        self.env.insert(id, ty)
    }

    pub fn remove(&mut self, id: &'a str) -> Option<Rc<Type>> {
        self.env.remove(id)
    }

    pub fn contains_type(&self, ty: &Type) -> bool {
        self.env
            .values()
            .into_iter()
            .find(|t| t.as_ref() == ty)
            .is_some()
    }

    fn gen_helper(&self, ty: &Type) -> Vec<u64> {
        match ty {
            Type::Fn(Fn { param, ret }) => {
                let mut res = self.gen_helper(param);
                for n in self.gen_helper(ret) {
                    if !res.contains(&n) {
                        res.push(n);
                    }
                }
                res
            }
            ty @ Type::Var(n) if !&self.contains_type(&ty) => {
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
                    quant: quantifiers,
                    ty:    ty.clone(),
                }
            }
            _ => Type::Generic {
                quant: quantifiers,
                ty,
            },
        };

        type_env.get_type(ty)
    }
}
