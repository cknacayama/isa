use super::{ctx::TypeCtx, infer::Substitute, types::Ty};
use crate::global::Symbol;
use rustc_hash::FxHashMap;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Env {
    env: Vec<FxHashMap<Symbol, Rc<Ty>>>,
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
    pub fn get(&self, id: &Symbol) -> Option<&Rc<Ty>> {
        self.env.iter().rev().find_map(|e| e.get(id))
    }

    pub fn insert(&mut self, id: Symbol, ty: Rc<Ty>) -> Option<Rc<Ty>> {
        self.env.last_mut().unwrap().insert(id, ty)
    }

    pub fn push_scope(&mut self) {
        self.env.push(FxHashMap::default());
    }

    pub fn pop_scope(&mut self) -> Option<FxHashMap<Symbol, Rc<Ty>>> {
        self.env.pop()
    }

    #[must_use]
    pub fn contains_type(&self, ty: &Ty) -> bool {
        let ty: *const Ty = ty;
        self.env.iter().flat_map(FxHashMap::values).any(|t| {
            let t: *const Ty = t.as_ref();
            t == ty
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Symbol, &Rc<Ty>)> {
        self.env.iter().flat_map(FxHashMap::iter)
    }

    #[must_use]
    fn gen_helper(&self, ty: &Ty) -> Vec<u64> {
        match ty {
            Ty::Fn { param, ret } => {
                let mut res = self.gen_helper(param);
                for n in self.gen_helper(ret) {
                    if !res.contains(&n) {
                        res.push(n);
                    }
                }
                res
            }
            ty @ Ty::Var(n) if !&self.contains_type(ty) => {
                vec![*n]
            }
            Ty::Scheme { quant, ty } => {
                let mut res = self.gen_helper(ty);
                for n in quant {
                    if !res.contains(n) {
                        res.push(*n);
                    }
                }
                res
            }
            Ty::Named { args, .. } => args
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
    pub fn generalize(&self, ty: Rc<Ty>, type_env: &mut TypeCtx) -> Rc<Ty> {
        let mut quantifiers = self.gen_helper(&ty);

        if quantifiers.is_empty() {
            return ty;
        }

        let ty = match ty.as_ref() {
            Ty::Scheme { quant, ty } => {
                quantifiers.extend_from_slice(quant);
                Ty::Scheme {
                    quant: quantifiers.into_boxed_slice(),
                    ty:    ty.clone(),
                }
            }
            _ => Ty::Scheme {
                quant: quantifiers.into_boxed_slice(),
                ty,
            },
        };

        type_env.intern_type(ty)
    }
}

impl Substitute for Env {
    fn substitute<S>(mut self, subs: &mut S, env: &mut TypeCtx) -> Self
    where
        S: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        for t in self.env.iter_mut().flat_map(FxHashMap::values_mut) {
            *t = t.clone().substitute(subs, env);
        }
        self
    }
}
