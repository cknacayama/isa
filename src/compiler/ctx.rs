use super::types::Ty;
use crate::global::Symbol;
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

#[derive(Debug, Clone)]
struct BuiltinTypes {
    integer: Rc<Ty>,
    boolean: Rc<Ty>,
    unit:    Rc<Ty>,
}

impl Default for BuiltinTypes {
    fn default() -> Self {
        Self {
            integer: Rc::new(Ty::Int),
            boolean: Rc::new(Ty::Bool),
            unit:    Rc::new(Ty::Unit),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeCtx {
    builtin:      BuiltinTypes,
    types:        FxHashSet<Rc<Ty>>,
    constructors: FxHashMap<Symbol, Rc<Ty>>,
}

impl TypeCtx {
    pub fn intern_type(&mut self, ty: Ty) -> Rc<Ty> {
        if let Some(ty) = self.types.get(&ty) {
            ty.clone()
        } else {
            let ty = Rc::new(ty);
            self.types.insert(ty.clone());
            ty
        }
    }

    #[must_use]
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
        self.builtin.unit.clone()
    }

    #[must_use]
    pub fn get_int(&self) -> Rc<Ty> {
        self.builtin.integer.clone()
    }

    #[must_use]
    pub fn get_bool(&self) -> Rc<Ty> {
        self.builtin.boolean.clone()
    }
}
