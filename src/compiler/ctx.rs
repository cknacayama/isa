use std::rc::Rc;

use rustc_hash::FxHashSet;

use super::types::Ty;

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
    id_generator: u64,
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

    pub const fn gen_id(&mut self) -> u64 {
        let cur = self.id_generator;
        self.id_generator += 1;
        cur
    }

    pub fn gen_type_var(&mut self) -> Rc<Ty> {
        let id = self.gen_id();
        self.intern_type(Ty::Var(id))
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
