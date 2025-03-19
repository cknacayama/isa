use super::{
    ctx::TypeCtx,
    infer::{Subs, Substitute},
    types::Type,
};
use crate::global::Symbol;
use rustc_hash::FxHashMap;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Env {
    env: Vec<FxHashMap<Symbol, Rc<Type>>>,
}

impl Substitute for Env {
    fn substitute(mut self, subs: &Subs, env: &mut TypeCtx) -> Self {
        for t in self.env.iter_mut().flat_map(FxHashMap::values_mut) {
            *t = t.clone().substitute(subs, env);
        }
        self
    }
}

impl Default for Env {
    fn default() -> Self {
        Self {
            env: vec![FxHashMap::default()],
        }
    }
}

impl Env {
    #[must_use]
    pub fn get(&self, id: &Symbol) -> Option<&Rc<Type>> {
        self.env.iter().rev().find_map(|e| e.get(id))
    }

    pub fn insert(&mut self, id: Symbol, ty: Rc<Type>) -> Option<Rc<Type>> {
        self.env.last_mut().unwrap().insert(id, ty)
    }

    pub fn push_scope(&mut self) {
        self.env.push(FxHashMap::default());
    }

    pub fn pop_scope(&mut self) -> Option<FxHashMap<Symbol, Rc<Type>>> {
        self.env.pop()
    }

    #[must_use]
    pub fn contains_type(&self, ty: &Type) -> bool {
        self.env
            .iter()
            .flat_map(FxHashMap::values)
            .any(|t| t.as_ref() == ty)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Symbol, &Rc<Type>)> {
        self.env.iter().flat_map(FxHashMap::iter)
    }

    #[must_use]
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

    #[must_use]
    pub fn generalize(&self, ty: Rc<Type>, type_env: &mut TypeCtx) -> Rc<Type> {
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
