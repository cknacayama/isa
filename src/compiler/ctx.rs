use std::fmt;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::ast::{Constructor, PathIdent};
use super::infer::{Subs, Substitute};
use super::types::Ty;

pub trait CtxFmt {
    type Ctx;

    fn ctx_fmt(&self, f: &mut impl fmt::Write, ctx: &Self::Ctx) -> fmt::Result;

    fn ctx_fmt_string(&self, ctx: &Self::Ctx) -> String {
        let mut out = String::new();
        self.ctx_fmt(&mut out, ctx)
            .unwrap_or_else(|_| unreachable!());
        out
    }
}

#[derive(Debug, Clone, Default)]
pub struct TyData {
    params:       Rc<[Ty]>,
    constructors: Vec<Constructor>,
}

impl TyData {
    #[must_use]
    pub fn new(params: Rc<[Ty]>, constructors: Vec<Constructor>) -> Self {
        Self {
            params,
            constructors,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeCtx {
    constructors: FxHashMap<PathIdent, TyData>,
    id_generator: u64,
}

impl TypeCtx {
    pub fn insert_constructor(&mut self, ty: &Ty, ctor: Constructor) {
        let (name, args) = match ty {
            Ty::Named { name, args } => (*name, args),
            _ => return,
        };
        self.constructors
            .entry(name)
            .or_insert_with(|| TyData::new(args.clone(), Vec::default()))
            .constructors
            .push(ctor);
    }

    #[must_use]
    pub fn get_constructors(&self, ty: &Ty) -> &[Constructor] {
        let Ty::Named { name, .. } = ty else {
            return &[];
        };
        self.constructors
            .get(name)
            .map_or(&[], |data| data.constructors.as_slice())
    }

    #[must_use]
    pub fn get_constructor_subtypes(&self, ty: &Ty, idx: usize) -> Box<[Ty]> {
        let Ty::Named { name, args } = ty else {
            return Box::default();
        };

        let mut data = self.constructors.get(name).cloned().unwrap_or_default();

        let subs = data
            .params
            .iter()
            .zip(args.iter())
            .filter_map(|(ty, arg)| {
                let ty = ty.as_var()?;
                Some(Subs::new(ty, arg.clone()))
            })
            .collect::<Vec<_>>();

        let mut ctors = data.constructors.swap_remove(idx);

        for param in &mut ctors.params {
            *param = param.clone().substitute_many(&subs);
        }

        ctors.params
    }

    pub const fn gen_id(&mut self) -> u64 {
        let cur = self.id_generator;
        self.id_generator += 1;
        cur
    }

    pub fn gen_type_var(&mut self) -> Ty {
        let id = self.gen_id();
        Ty::Var(id)
    }

    pub fn write_variant_name(
        &self,
        f: &mut impl std::fmt::Write,
        ty: &Ty,
        idx: usize,
    ) -> std::fmt::Result {
        let ctor = self.get_constructors(ty)[idx].name;
        write!(f, "{ctor}")
    }
}

impl Substitute for &mut TypeCtx {
    fn substitute<S>(self, subs: &mut S) -> Self
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.constructors
            .values_mut()
            .flat_map(|data| data.constructors.iter_mut())
            .for_each(|c| {
                c.substitute(subs);
            });
        self
    }
}
