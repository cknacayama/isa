use std::fmt;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::ast::Constructor;
use super::infer::{ClassConstraint, ClassConstraintSet, Subs, Substitute};
use super::types::Ty;
use crate::global::{self, Symbol};
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

    pub fn extend_signature(&mut self, iter: impl IntoIterator<Item = (Symbol, (Ty, Span))>) {
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

#[derive(Debug, Clone)]
pub struct TypeCtx {
    constructors: FxHashMap<Symbol, TyData>,
    classes:      FxHashMap<Symbol, ClassData>,
    instances:    FxHashMap<Ty, FxHashMap<Symbol, InstanceData>>,
    id_generator: u64,
}

fn default_classes() -> FxHashMap<Symbol, ClassData> {
    use global::intern_symbol as intern;

    let instance_ty = Ty::Poly {
        name: intern("'a"),
        args: Rc::default(),
    };

    macro_rules! class {
        ($classes:ident, {$($constr:ident)+} => $name:ident, $($member:ident: [$($t:expr,)+], $ret:expr;)+) => {{
            let set = ClassConstraintSet::from([$(ClassConstraint::new(intern(stringify!($constr)), instance_ty.clone(), Span::default()),)+]);
            let mut data = ClassData::new(set, intern("'a"), Span::default());
            data.extend_signature([
                $(signature!($member: [$($t,)+], $ret)),+
            ]);
            $classes.insert(intern(stringify!($name)), data);
        }};
        ($classes:ident, $name:ident, $($member:ident: [$($t:expr,)+], $ret:expr;)+) => {{
            let mut data = ClassData::new(ClassConstraintSet::new(), intern("'a"), Span::default());
            data.extend_signature([
                $(signature!($member: [$($t,)+], $ret)),+
            ]);
            $classes.insert(intern(stringify!($name)), data);
        }};
    }

    macro_rules! signature {
        ($name:ident: [$($t:expr,)+], $ret:expr) => {
            (
                intern(stringify!($name)),
                (
                    Ty::function_type([$($t),+], $ret),
                    Span::default(),
                )
            )
        };
    }

    let mut classes = FxHashMap::default();

    class!(classes, Eq,
        eq: [instance_ty.clone(), instance_ty.clone(),], Ty::Bool;
        ne: [instance_ty.clone(), instance_ty.clone(),], Ty::Bool;
    );
    class!(classes, {Eq} => Cmp,
        lt: [instance_ty.clone(), instance_ty.clone(),], Ty::Bool;
        gt: [instance_ty.clone(), instance_ty.clone(),], Ty::Bool;
        ge: [instance_ty.clone(), instance_ty.clone(),], Ty::Bool;
        le: [instance_ty.clone(), instance_ty.clone(),], Ty::Bool;
    );
    class!(classes, {Cmp} => Number,
        add: [instance_ty.clone(), instance_ty.clone(),], instance_ty.clone();
        sub: [instance_ty.clone(), instance_ty.clone(),], instance_ty.clone();
        mult: [instance_ty.clone(), instance_ty.clone(),], instance_ty.clone();
        div: [instance_ty.clone(), instance_ty.clone(),], instance_ty.clone();
        rem: [instance_ty.clone(), instance_ty.clone(),], instance_ty.clone();
    );

    classes
}

fn default_instances() -> FxHashMap<Ty, FxHashMap<Symbol, InstanceData>> {
    use global::intern_symbol as intern;

    let mut instances = FxHashMap::default();

    macro_rules! instance {
        ($ty:expr, $($name:ident,)+) => {{
            let constraints = ClassConstraintSet::new();
            let span = Span::default();
            let data = InstanceData { constraints, span };
            instances.insert(
                $ty,
                [$((intern(stringify!($name)),data.clone()),)+].into_iter().collect()
            )
        }};
    }

    instance!(Ty::Int, Eq, Cmp, Number,);
    instance!(Ty::Bool, Eq,);
    instance!(Ty::Unit, Eq,);
    instance!(Ty::Char, Eq, Cmp, Number,);

    instances
}

impl Default for TypeCtx {
    fn default() -> Self {
        let classes = default_classes();
        let instances = default_instances();

        Self {
            constructors: FxHashMap::default(),
            classes,
            instances,
            id_generator: 0,
        }
    }
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

        let Ty::Poly { name, args } = ty else {
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

    pub fn gen_named_var(&mut self) -> Symbol {
        let id = self.gen_id();
        let name = format!("'{id}");
        global::intern_symbol(&name)
    }

    pub fn write_variant_name(
        &self,
        f: &mut impl std::fmt::Write,
        ty: &Ty,
        idx: usize,
    ) -> std::fmt::Result {
        let Ty::Poly { name, .. } = ty else {
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

    pub fn instantiate_class(
        &self,
        class: Symbol,
        ty: &Ty,
        span: Span,
    ) -> Result<(), Vec<ClassConstraint>> {
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

                let mut constraints = Vec::new();
                for mut constr in data.constraints().iter().filter_map(|constr| {
                    args.iter().find_map(|(a1, a2)| {
                        if constr.constrained() == a1 {
                            self.instantiate_class(constr.class(), a2, constr.span())
                                .err()
                        } else {
                            None
                        }
                    })
                }) {
                    constraints.append(&mut constr);
                }

                return if constraints.is_empty() {
                    Ok(())
                } else {
                    Err(constraints)
                };
            }
        }

        Err(vec![ClassConstraint::new(class, ty.clone(), span)])
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
