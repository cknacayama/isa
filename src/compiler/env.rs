use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::ast::ModuleIdent;
use super::ctx::TypeCtx;
use super::error::InferErrorKind;
use super::infer::Substitute;
use super::types::Ty;
use crate::global::Symbol;

#[derive(Debug, Clone)]
pub struct VarData {
    constructor: bool,
    ty:          Rc<Ty>,
}

impl VarData {
    #[must_use]
    pub fn new(constructor: bool, ty: Rc<Ty>) -> Self {
        Self { constructor, ty }
    }

    #[must_use]
    pub const fn constructor(&self) -> bool {
        self.constructor
    }

    #[must_use]
    pub const fn ty(&self) -> &Rc<Ty> {
        &self.ty
    }

    pub const fn ty_mut(&mut self) -> &mut Rc<Ty> {
        &mut self.ty
    }
}

#[derive(Debug, Clone)]
pub struct Env {
    env:     Vec<FxHashMap<Symbol, VarData>>,
    modules: FxHashMap<Symbol, FxHashMap<Symbol, VarData>>,
}

impl Default for Env {
    fn default() -> Self {
        Self {
            env:     vec![FxHashMap::default()],
            modules: FxHashMap::default(),
        }
    }
}

impl Env {
    pub fn extend_global<I>(&mut self, iter: I) -> bool
    where
        I: IntoIterator<Item = (Symbol, VarData)>,
    {
        self.env
            .first_mut()
            .map(|glob| {
                glob.extend(iter);
            })
            .is_some()
    }

    #[must_use]
    pub fn get(&self, id: &Symbol) -> Option<&VarData> {
        self.env.iter().rev().find_map(|e| e.get(id))
    }

    #[must_use]
    pub fn get_constructor(&self, id: &Symbol) -> Option<Rc<Ty>> {
        self.env
            .iter()
            .rev()
            .find_map(|e| e.get(id))
            .and_then(|var| {
                if var.constructor() {
                    Some(var.ty().clone())
                } else {
                    None
                }
            })
    }

    pub fn insert(&mut self, id: Symbol, ty: Rc<Ty>) -> Option<VarData> {
        self.env
            .last_mut()
            .and_then(|env| env.insert(id, VarData::new(false, ty)))
    }

    pub fn insert_constructor(&mut self, id: Symbol, ty: Rc<Ty>) -> Option<VarData> {
        self.env
            .last_mut()
            .and_then(|env| env.insert(id, VarData::new(true, ty)))
    }

    pub fn get_from_module(&self, module_access: &ModuleIdent) -> Result<VarData, InferErrorKind> {
        let Some(module) = self.modules.get(&module_access.module()) else {
            return Err(InferErrorKind::UnboundModule(module_access.module()));
        };

        let Some(var) = module.get(&module_access.member()) else {
            return Err(InferErrorKind::Unbound(module_access.member()));
        };

        Ok(var.clone())
    }

    pub fn get_constructor_from_module(
        &self,
        module_access: &ModuleIdent,
    ) -> Result<Rc<Ty>, InferErrorKind> {
        let Some(module) = self.modules.get(&module_access.module()) else {
            return Err(InferErrorKind::UnboundModule(module_access.module()));
        };

        let Some(var) = module.get(&module_access.member()) else {
            return Err(InferErrorKind::Unbound(module_access.member()));
        };

        if var.constructor() {
            Ok(var.ty().clone())
        } else {
            Err(InferErrorKind::NotConstructor(module_access.member()))
        }
    }

    pub fn insert_module(
        &mut self,
        module: Symbol,
        declared: FxHashMap<Symbol, VarData>,
    ) -> Option<FxHashMap<Symbol, VarData>> {
        self.modules.insert(module, declared)
    }

    pub fn push_scope(&mut self) {
        self.env.push(FxHashMap::default());
    }

    pub fn pop_scope(&mut self) -> Option<FxHashMap<Symbol, VarData>> {
        self.env.pop()
    }

    #[must_use]
    fn contains_type(&self, id: u64) -> bool {
        self.env
            .iter()
            .flat_map(FxHashMap::values)
            .any(|t| t.ty.occurs(id))
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Symbol, &VarData)> {
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
            Ty::Var(n) if !self.contains_type(*n) => {
                vec![*n]
            }
            Ty::Scheme { quant, ty } => {
                let mut res = self.gen_helper(ty);
                for n in quant.iter() {
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
                    quant: quantifiers.into(),
                    ty:    ty.clone(),
                }
            }
            _ => Ty::Scheme {
                quant: quantifiers.into(),
                ty,
            },
        };

        type_env.intern_type(ty)
    }
}

impl Substitute for &mut Env {
    fn substitute<S>(self, subs: &mut S, env: &mut TypeCtx) -> Self
    where
        S: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        for t in self.env.iter_mut().flat_map(FxHashMap::values_mut) {
            t.ty = t.ty.clone().substitute(subs, env);
        }
        self
    }
}
impl Substitute for &mut VarData {
    fn substitute<S>(self, subs: &mut S, env: &mut TypeCtx) -> Self
    where
        S: FnMut(&Ty, &mut TypeCtx) -> Option<Rc<Ty>>,
    {
        self.ty = self.ty.clone().substitute(subs, env);
        self
    }
}
