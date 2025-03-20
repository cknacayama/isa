use super::types::Ty;
use crate::global::Symbol;
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct TypeCtx {
    types:        FxHashSet<Rc<Ty>>,
    constructors: FxHashMap<Symbol, Rc<Ty>>,
}

impl Default for TypeCtx {
    fn default() -> Self {
        let mut types = FxHashSet::default();
        types.extend([Rc::new(Ty::Unit), Rc::new(Ty::Int), Rc::new(Ty::Bool)]);

        Self {
            types,
            constructors: FxHashMap::default(),
        }
    }
}

impl TypeCtx {
    pub fn get_type(&mut self, ty: Ty) -> Rc<Ty> {
        if let Some(ty) = self.types.get(&ty) {
            ty.clone()
        } else {
            let ty = Rc::new(ty);
            self.types.insert(ty.clone());
            ty
        }
    }

    pub fn get_constructor(&self, name: &Symbol) -> Option<&Rc<Ty>> {
        self.constructors.get(name)
    }

    pub fn insert_constructor(&mut self, name: Symbol, ty: Rc<Ty>) {
        self.constructors.insert(name, ty);
    }

    pub fn iter(&self) -> impl Iterator<Item = &Rc<Ty>> {
        self.types.iter()
    }

    #[must_use]
    pub fn get_unit(&self) -> Rc<Ty> {
        self.types.get(&Ty::Unit).unwrap().clone()
    }

    #[must_use]
    pub fn get_int(&self) -> Rc<Ty> {
        self.types.get(&Ty::Int).unwrap().clone()
    }

    #[must_use]
    pub fn get_bool(&self) -> Rc<Ty> {
        self.types.get(&Ty::Bool).unwrap().clone()
    }
}
