use std::{collections::HashMap, rc::Rc};

use crate::types::*;

#[derive(Debug, Clone)]
pub struct Ctx<'a> {
    pub locals: HashMap<&'a str, Type>,
    pub procs: HashMap<&'a str, Rc<ProcSig>>,
}

impl<'a> Ctx<'a> {
    pub fn new() -> Self {
        Self {
            locals: HashMap::new(),
            procs: HashMap::new(),
        }
    }

    #[inline]
    pub fn add_local(&mut self, name: &'a str, ty: Type) -> Option<Type> {
        self.locals.insert(name, ty)
    }

    #[inline]
    pub fn add_proc(&mut self, name: &'a str, sig: Rc<ProcSig>) -> Option<Rc<ProcSig>> {
        self.procs.insert(name, sig)
    }

    #[inline]
    pub fn get_local(&self, name: &'a str) -> Option<&Type> {
        self.locals.get(name)
    }

    #[inline]
    pub fn get_proc(&self, name: &'a str) -> Option<&Rc<ProcSig>> {
        self.procs.get(name)
    }
}

impl<'a> Default for Ctx<'a> {
    fn default() -> Self {
        Self::new()
    }
}
