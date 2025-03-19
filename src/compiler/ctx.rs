use super::{ast::Constructor, types::Type};
use crate::global::Symbol;
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct TypeCtx {
    types:        FxHashSet<Rc<Type>>,
    constructors: FxHashMap<Symbol, Rc<Type>>,
    variants:     FxHashMap<Rc<Type>, Box<[Constructor]>>,
}

impl Default for TypeCtx {
    fn default() -> Self {
        let mut types = FxHashSet::default();
        types.extend([Rc::new(Type::Unit), Rc::new(Type::Int), Rc::new(Type::Bool)]);

        Self {
            types,
            constructors: FxHashMap::default(),
            variants: FxHashMap::default(),
        }
    }
}

impl TypeCtx {
    pub fn get_type(&mut self, ty: Type) -> Rc<Type> {
        if let Some(ty) = self.types.get(&ty) {
            ty.clone()
        } else {
            let ty = Rc::new(ty);
            self.types.insert(ty.clone());
            ty
        }
    }

    pub fn get_variants(&self, ty: &Type) -> Option<&[Constructor]> {
        self.variants.get(ty).map(Box::as_ref)
    }

    pub fn insert_variants(&mut self, ty: Rc<Type>, variants: Box<[Constructor]>) {
        self.variants.insert(ty, variants);
    }

    pub fn get_constructor(&self, name: &Symbol) -> Option<&Rc<Type>> {
        self.constructors.get(name)
    }

    pub fn insert_constructor(&mut self, name: Symbol, ty: Rc<Type>) {
        self.constructors.insert(name, ty);
    }

    pub fn iter(&self) -> impl Iterator<Item = &Rc<Type>> {
        self.types.iter()
    }

    #[must_use]
    pub fn get_unit(&self) -> Rc<Type> {
        self.types.get(&Type::Unit).unwrap().clone()
    }

    #[must_use]
    pub fn get_int(&self) -> Rc<Type> {
        self.types.get(&Type::Int).unwrap().clone()
    }

    #[must_use]
    pub fn get_bool(&self) -> Rc<Type> {
        self.types.get(&Type::Bool).unwrap().clone()
    }
}
