use std::rc::Rc;

use rustc_hash::{FxHashMap, FxHashSet};

use super::infer::Substitute;
use super::types::Ty;
use crate::global::Symbol;
use crate::span::Span;

#[derive(Debug, Clone, Copy)]
enum VarKind {
    Constructor,
    ValueDeclaration,
    LetDefinition,
}

impl VarKind {
    #[must_use]
    const fn is_constructor(self) -> bool {
        matches!(self, Self::Constructor)
    }

    #[must_use]
    const fn is_value_declaration(self) -> bool {
        matches!(self, Self::ValueDeclaration)
    }
}

#[derive(Debug, Clone)]
pub struct VarData {
    kind: VarKind,
    ty:   Ty,
    span: Span,
}

impl VarData {
    #[must_use]
    const fn new(kind: VarKind, ty: Ty, span: Span) -> Self {
        Self { kind, ty, span }
    }

    #[must_use]
    pub const fn ty(&self) -> &Ty {
        &self.ty
    }

    const fn kind(&self) -> VarKind {
        self.kind
    }

    pub const fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct Env {
    env: Vec<FxHashMap<Symbol, VarData>>,
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
    pub fn get(&self, id: Symbol) -> Option<&VarData> {
        self.env.iter().rev().find_map(|e| e.get(&id))
    }

    #[must_use]
    pub fn get_constructor(&self, id: Symbol) -> Option<&VarData> {
        self.env
            .iter()
            .rev()
            .find_map(|e| e.get(&id))
            .and_then(|var| {
                if var.kind().is_constructor() {
                    Some(var)
                } else {
                    None
                }
            })
    }

    #[must_use]
    pub fn get_val(&self, id: Symbol) -> Option<&VarData> {
        self.env
            .iter()
            .rev()
            .find_map(|e| e.get(&id))
            .and_then(|var| {
                if var.kind().is_value_declaration() {
                    Some(var)
                } else {
                    None
                }
            })
    }

    pub fn insert(&mut self, id: Symbol, ty: Ty, span: Span) -> Option<VarData> {
        self.env
            .last_mut()
            .and_then(|env| env.insert(id, VarData::new(VarKind::LetDefinition, ty, span)))
    }

    pub fn insert_constructor(&mut self, id: Symbol, ty: Ty, span: Span) -> Option<VarData> {
        self.env
            .last_mut()
            .and_then(|env| env.insert(id, VarData::new(VarKind::Constructor, ty, span)))
    }

    pub fn insert_val(&mut self, id: Symbol, ty: Ty, span: Span) -> Option<VarData> {
        self.env
            .last_mut()
            .and_then(|env| env.insert(id, VarData::new(VarKind::ValueDeclaration, ty, span)))
    }

    pub fn push_scope(&mut self) {
        self.env.push(FxHashMap::default());
    }

    pub fn current_scope(&self) -> Option<&FxHashMap<Symbol, VarData>> {
        self.env.last()
    }

    pub fn pop_scope(&mut self) -> Option<FxHashMap<Symbol, VarData>> {
        self.env.pop()
    }

    pub const fn at_global_scope(&self) -> bool {
        self.scope_depth() == 1
    }

    pub fn global_scope(&self) -> &FxHashMap<Symbol, VarData> {
        self.env.first().unwrap()
    }

    pub const fn scope_depth(&self) -> usize {
        self.env.len()
    }

    fn free_type_variables(&self) -> FxHashSet<u64> {
        let mut free = FxHashSet::default();
        for t in self.env.iter().flat_map(FxHashMap::values) {
            free.extend(t.ty.free_type_variables());
        }
        free
    }

    #[must_use]
    pub fn generalize(&self, ty: Ty) -> Ty {
        let mut quantifiers = ty.free_type_variables();

        if quantifiers.is_empty() {
            return ty;
        }

        let free = self.free_type_variables();

        if !free.is_empty() {
            quantifiers.retain(|q| !free.contains(q));
        }

        if quantifiers.is_empty() {
            return ty;
        }

        match ty {
            Ty::Scheme { quant, ty } => {
                quantifiers.extend_from_slice(&quant);
                Ty::Scheme {
                    quant: quantifiers.into(),
                    ty,
                }
            }
            _ => Ty::Scheme {
                quant: quantifiers.into(),
                ty:    Rc::new(ty),
            },
        }
    }
}

impl Substitute for Env {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.env
            .iter_mut()
            .flat_map(FxHashMap::values_mut)
            .for_each(|t| t.ty.substitute(subs));
    }
}
