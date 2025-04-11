use std::fmt;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::ast::Constructor;
use super::infer::{ClassConstraint, ClassConstraintSet, Subs, Substitute};
use super::types::Ty;
use crate::global::Symbol;
use crate::span::Span;

pub trait CtxFmt {
    type Ctx;

    fn ctx_fmt(&self, f: &mut impl fmt::Write, ctx: &Self::Ctx) -> fmt::Result;
    fn is_simple_fmt(&self) -> bool;
    fn ctx_simple_fmt(&self, f: &mut impl fmt::Write, ctx: &Self::Ctx) -> fmt::Result {
        let simple = self.is_simple_fmt();
        if !simple {
            write!(f, "(")?;
        }
        self.ctx_fmt(f, ctx)?;
        if !simple {
            write!(f, ")")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Default)]
pub struct TyData {
    params:       Rc<[u64]>,
    constructors: Vec<Constructor>,
}

impl TyData {
    #[must_use]
    const fn new(params: Rc<[u64]>, constructors: Vec<Constructor>) -> Self {
        Self {
            params,
            constructors,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AliasData {
    params: Rc<[u64]>,
    ty:     Ty,
}

impl AliasData {
    #[must_use]
    pub const fn new(params: Rc<[u64]>, ty: Ty) -> Self {
        Self { params, ty }
    }

    pub fn params(&self) -> &[u64] {
        &self.params
    }

    pub const fn ty(&self) -> &Ty {
        &self.ty
    }

    pub fn subs(&self, args: &[Ty]) -> Ty {
        let mut ty = self.ty().clone();
        ty.substitute(&mut |ty| {
            self.params()
                .iter()
                .copied()
                .position(|v| ty.as_var().is_some_and(|ty| ty == v))
                .map(|pos| args[pos].clone())
        });
        ty
    }
}

#[derive(Debug, Clone, Default)]
pub struct InstanceData {
    constraints: ClassConstraintSet,
    span:        Span,
}

impl InstanceData {
    pub fn new(span: Span) -> Self {
        Self {
            constraints: ClassConstraintSet::default(),
            span,
        }
    }

    pub const fn constraints(&self) -> &ClassConstraintSet {
        &self.constraints
    }

    pub const fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, Default)]
pub struct ClassData {
    constraints:  ClassConstraintSet,
    instance_var: Symbol,
    signatures:   FxHashMap<Symbol, (Ty, Span)>,
    span:         Span,
}

impl ClassData {
    pub fn new(constraints: ClassConstraintSet, instance_var: Symbol, span: Span) -> Self {
        Self {
            constraints,
            instance_var,
            signatures: FxHashMap::default(),
            span,
        }
    }

    pub fn extend_signature(&mut self, iter: impl Iterator<Item = (Symbol, (Ty, Span))>) {
        self.signatures.extend(iter);
    }

    pub const fn instance_var(&self) -> Symbol {
        self.instance_var
    }

    pub const fn signatures(&self) -> &FxHashMap<Symbol, (Ty, Span)> {
        &self.signatures
    }

    pub const fn span(&self) -> Span {
        self.span
    }

    pub const fn constraints(&self) -> &ClassConstraintSet {
        &self.constraints
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeCtx {
    constructors: FxHashMap<Symbol, TyData>,
    classes:      FxHashMap<Symbol, ClassData>,
    instances:    FxHashMap<Ty, FxHashMap<Symbol, InstanceData>>,
    id_generator: u64,
}

impl TypeCtx {
    pub fn insert_constructor(&mut self, name: Symbol, params: &Rc<[u64]>, ctor: Constructor) {
        self.constructors
            .entry(name)
            .or_insert_with(|| TyData::new(params.clone(), Vec::default()))
            .constructors
            .push(ctor);
    }

    #[must_use]
    pub fn get_constructors(&self, name: Symbol) -> &[Constructor] {
        self.constructors
            .get(&name)
            .map_or(&[], |data| data.constructors.as_slice())
    }

    #[must_use]
    pub fn get_type_arity(&self, name: Symbol) -> Option<usize> {
        self.constructors.get(&name).map(|data| data.params.len())
    }

    pub fn insert_class(&mut self, name: Symbol, data: ClassData) -> Option<ClassData> {
        self.classes.insert(name, data)
    }

    pub fn insert_instance(
        &mut self,
        ty: Ty,
        class: Symbol,
        data: InstanceData,
    ) -> Option<InstanceData> {
        self.instances.entry(ty).or_default().insert(class, data)
    }

    #[must_use]
    pub fn get_class(&self, name: Symbol) -> Option<&ClassData> {
        self.classes.get(&name)
    }

    #[must_use]
    pub fn get_class_mut(&mut self, name: Symbol) -> Option<&mut ClassData> {
        self.classes.get_mut(&name)
    }

    #[must_use]
    pub fn get_constructor_subtypes(&self, ty: &Ty, idx: usize) -> Box<[Ty]> {
        if let Ty::Tuple(types) = ty {
            return types.to_vec().into_boxed_slice();
        }

        let Ty::Named { name, args } = ty else {
            return Box::default();
        };

        let mut data = self.constructors.get(name).cloned().unwrap_or_default();

        let subs = data
            .params
            .iter()
            .copied()
            .zip(args.iter().cloned())
            .map(|(ty, arg)| Subs::new(ty, arg))
            .collect::<Vec<_>>();

        let mut ctor = data.constructors.swap_remove(idx);

        for param in &mut ctor.params {
            param.substitute_many(&subs);
        }

        ctor.params
    }

    pub const fn gen_id(&mut self) -> u64 {
        let cur = self.id_generator;
        self.id_generator += 1;
        cur
    }

    pub const fn gen_type_var(&mut self) -> Ty {
        let id = self.gen_id();
        Ty::Var(id)
    }

    pub fn write_variant_name(
        &self,
        f: &mut impl std::fmt::Write,
        ty: &Ty,
        idx: usize,
    ) -> std::fmt::Result {
        let Ty::Named { name, .. } = ty else {
            return Ok(());
        };
        let ctor = self.get_constructors(*name)[idx].name;
        write!(f, "{ctor}")
    }

    pub fn implementation(&self, ty: &Ty, class: Symbol) -> Option<&InstanceData> {
        if ty.is_scheme() {
            self.instances.iter().find_map(|(instance, classes)| {
                if ty.equivalent(instance) {
                    classes.get(&class)
                } else {
                    None
                }
            })
        } else {
            self.instances
                .get(ty)
                .and_then(|classes| classes.get(&class))
        }
    }

    fn implementation_mut(&mut self, ty: &Ty, class: Symbol) -> Option<&mut InstanceData> {
        if ty.is_scheme() {
            self.instances.iter_mut().find_map(|(instance, classes)| {
                if ty.equivalent(instance) {
                    classes.get_mut(&class)
                } else {
                    None
                }
            })
        } else {
            self.instances
                .get_mut(ty)
                .and_then(|classes| classes.get_mut(&class))
        }
    }

    pub fn instantiate_class(&self, class: Symbol, ty: &Ty) -> Result<(), ClassConstraint> {
        if self.implementation(ty, class).is_some() {
            return Ok(());
        }

        for (instance, data) in self
            .instances
            .iter()
            .filter_map(|(k, v)| v.get(&class).map(|data| (k, data)))
        {
            if let Ty::Scheme {
                ty: instance_ty, ..
            } = instance
            {
                let Some(args) = instance_ty.zip_args(ty) else {
                    continue;
                };

                data.constraints()
                    .iter()
                    .filter_map(|constr| {
                        args.iter().find_map(|(a1, a2)| {
                            if constr.constrained() == a1 {
                                Some(self.instantiate_class(constr.class(), a2))
                            } else {
                                None
                            }
                        })
                    })
                    .try_for_each(std::convert::identity)?;

                return Ok(());
            }
        }

        Err(ClassConstraint::new(class, ty.clone()))
    }

    pub fn set_constraints(&mut self, class: Symbol, ty: &Ty, constr: ClassConstraintSet) {
        self.implementation_mut(ty, class).unwrap().constraints = constr;
    }

    pub const fn instances(&self) -> &FxHashMap<Ty, FxHashMap<Symbol, InstanceData>> {
        &self.instances
    }
}

impl Substitute for TypeCtx {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.constructors
            .values_mut()
            .flat_map(|data| data.constructors.iter_mut())
            .for_each(|c| {
                c.substitute(subs);
            });
    }
}
