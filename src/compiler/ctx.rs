use std::collections::hash_map::{self, Entry};
use std::fmt::Display;
use std::rc::Rc;
use std::{fmt, vec};

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::smallvec;

use super::ast::Path;
use super::ast::typed::TypedConstructor;
use super::error::{CheckError, CheckErrorKind, CheckResult};
use super::infer::{ClassConstraint, ClassConstraintSet, Subs, Substitute};
use super::token::Ident;
use super::types::Ty;
use crate::compiler::ast::Constructor;
use crate::global::{self};
use crate::span::Span;

#[derive(Debug, Clone)]
pub struct VarData {
    pub ty:      Ty,
    pub constrs: ClassConstraintSet,
    pub span:    Span,
}

impl VarData {
    #[must_use]
    pub const fn new(ty: Ty, constrs: ClassConstraintSet, span: Span) -> Self {
        Self { ty, constrs, span }
    }

    #[must_use]
    pub const fn ty(&self) -> &Ty {
        &self.ty
    }
}

#[derive(Debug, Clone, Default)]
pub struct ModuleData {
    lets:         FxHashMap<Ident, VarData>,
    vals:         FxHashMap<Ident, VarData>,
    imports:      FxHashMap<Ident, Ident>,
    types:        FxHashMap<Ident, TyData>,
    constructors: FxHashMap<Ident, VarData>,
    classes:      FxHashMap<Ident, ClassData>,
}

impl ModuleData {
    pub fn get_type(&self, id: Ident) -> CheckResult<&TyData> {
        self.types
            .get(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_val(&self, id: Ident) -> CheckResult<&VarData> {
        self.vals
            .get(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_var(&self, id: Ident) -> CheckResult<&VarData> {
        self.get_let(id).or_else(|_| self.get_val(id))
    }

    pub fn get_let(&self, id: Ident) -> CheckResult<&VarData> {
        self.lets
            .get(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_import(&self, id: Ident) -> CheckResult<Ident> {
        self.imports
            .get(&id)
            .copied()
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_constructor(&self, id: Ident) -> CheckResult<&VarData> {
        self.constructors
            .get(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_class(&self, id: Ident) -> CheckResult<&ClassData> {
        self.classes
            .get(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_type_mut(&mut self, id: Ident) -> CheckResult<&mut TyData> {
        self.types
            .get_mut(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_val_mut(&mut self, id: Ident) -> CheckResult<&mut VarData> {
        self.vals
            .get_mut(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_let_mut(&mut self, id: Ident) -> CheckResult<&mut VarData> {
        self.lets
            .get_mut(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_constructor_mut(&mut self, id: Ident) -> CheckResult<&mut VarData> {
        self.constructors
            .get_mut(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_import_mut(&mut self, id: Ident) -> CheckResult<Ident> {
        self.imports
            .get_mut(&id)
            .copied()
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_class_mut(&mut self, id: Ident) -> CheckResult<&mut ClassData> {
        self.classes
            .get_mut(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn insert_type(&mut self, id: Ident, data: TyData) -> Option<TyData> {
        self.types.insert(id, data)
    }

    pub fn insert_val(&mut self, id: Ident, data: VarData) -> Option<VarData> {
        self.vals.insert(id, data)
    }

    pub fn insert_let(&mut self, id: Ident, data: VarData) -> Option<VarData> {
        self.lets.insert(id, data)
    }

    pub fn insert_import(&mut self, id: Ident, data: Ident) -> Option<Ident> {
        self.imports.insert(id, data)
    }

    pub fn insert_class(&mut self, id: Ident, data: ClassData) -> Option<ClassData> {
        self.classes.insert(id, data)
    }

    fn exportable(&self, id: Ident) -> bool {
        !self.imports.contains_key(&id)
            && (self.classes.contains_key(&id)
                || self.types.contains_key(&id)
                || self.lets.contains_key(&id)
                || self.vals.contains_key(&id))
    }
}

pub trait Generator {
    fn gen_id(&mut self) -> u64;

    fn gen_type_var(&mut self) -> Ty {
        let id = self.gen_id();
        Ty::Var(id)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct IdGenerator(u64);

impl Default for IdGenerator {
    fn default() -> Self {
        Self(1)
    }
}

impl Generator for IdGenerator {
    fn gen_id(&mut self) -> u64 {
        let id = self.0;
        self.0 += 1;
        id
    }
}

impl Substitute for VarData {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.ty.substitute(subs);
        self.constrs.substitute(subs);
    }
}

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
    constructors: Vec<TypedConstructor>,
}

impl TyData {
    #[must_use]
    const fn new(params: Rc<[u64]>, constructors: Vec<TypedConstructor>) -> Self {
        Self {
            params,
            constructors,
        }
    }

    pub fn constructors(&self) -> &[TypedConstructor] {
        &self.constructors
    }

    pub fn params(&self) -> &[u64] {
        &self.params
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
    pub const fn new(constraints: ClassConstraintSet, span: Span) -> Self {
        Self { constraints, span }
    }

    pub const fn constraints(&self) -> &ClassConstraintSet {
        &self.constraints
    }

    pub const fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct MemberData {
    pub has_default: bool,
    pub set:         ClassConstraintSet,
    pub ty:          Ty,
    pub span:        Span,
}

#[derive(Debug, Clone, Default)]
pub struct ClassData {
    constraints:  ClassConstraintSet,
    instance_var: u64,
    signatures:   FxHashMap<Ident, MemberData>,
    instances:    FxHashMap<Ty, InstanceData>,
    span:         Span,
}

impl ClassData {
    pub fn with_instances(
        constraints: ClassConstraintSet,
        instance_var: u64,
        instances: FxHashMap<Ty, InstanceData>,
        span: Span,
    ) -> Self {
        Self {
            constraints,
            instance_var,
            signatures: FxHashMap::default(),
            instances,
            span,
        }
    }

    pub fn new(constraints: ClassConstraintSet, instance_var: u64, span: Span) -> Self {
        Self {
            constraints,
            instance_var,
            signatures: FxHashMap::default(),
            instances: FxHashMap::default(),
            span,
        }
    }

    pub fn extend_signature(&mut self, iter: impl IntoIterator<Item = (Ident, MemberData)>) {
        self.signatures.extend(iter);
    }

    pub const fn instance_var(&self) -> u64 {
        self.instance_var
    }

    pub const fn signatures(&self) -> &FxHashMap<Ident, MemberData> {
        &self.signatures
    }

    pub const fn span(&self) -> Span {
        self.span
    }

    pub const fn constraints(&self) -> &ClassConstraintSet {
        &self.constraints
    }
}

fn default_classes() -> ModuleData {
    use global::intern_symbol as intern;

    let instance_ty = Ty::Var(0);
    let span = Span::default();

    macro_rules! class {
        ($classes:ident, $instances:expr, {$($constr:ident)+} => $name:ident, $($member:expr;)+) => {{
            let set = ClassConstraintSet::from([
                $(ClassConstraint::new(Path::from_ident(Ident { ident: intern(stringify!($constr)), span }), instance_ty.clone(), span),)+
            ]);
            let mut data = ClassData::with_instances(set, 0, $instances, span);
            data.extend_signature([
                $($member),+
            ]);
            $classes.insert(Ident { ident: intern(stringify!($name)), span }, data);
        }};
        ($classes:ident, $instances:expr, $name:ident, $($member:expr;)+) => {{
            let mut data = ClassData::with_instances(ClassConstraintSet::new(), 0, $instances, span);
            data.extend_signature([
                $($member),+
            ]);
            $classes.insert(Ident { ident: intern(stringify!($name)), span }, data);
        }};
    }

    macro_rules! signature {
        ($name:ident: ($($t:expr,)+) -> $ret:expr) => {
            (
                Ident { ident: intern(stringify!($name)), span: Span::default() },
                MemberData {
                    has_default: false,
                    ty: Ty::function_type([$($t),+], $ret),
                    set: ClassConstraintSet::new(),
                    span: Span::default(),
                }
            )
        };
        (default $name:ident: ($($t:expr,)+) -> $ret:expr) => {
            (
                Ident { ident: intern(stringify!($name)), span: Span::default() },
                MemberData {
                    has_default: true,
                    ty: Ty::function_type([$($t),+], $ret),
                    set: ClassConstraintSet::new(),
                    span: Span::default(),
                }
            )
        };
    }

    macro_rules! type_decl {
        ($classes:ident, $name:ident = $($constructor:expr,)+) => {{
            $classes.insert(
                Ident {
                    ident: intern(stringify!($name)),
                    span,
                },
                TyData::new(
                        Rc::from([]),
                        vec![$($constructor),+],
                ),
            );
        }};
        ($classes:ident, $name:ident $($param:literal)+ = $($constructor:expr,)+) => {{
            $classes.insert(
                Ident {
                    ident: intern(stringify!($name)),
                    span,
                },
                TyData::new(
                        Rc::from([$($param),+]),
                        vec![$($constructor),+],
                ),
            );
        }};
    }

    macro_rules! constructor {
        ($name:ident $($param:literal )* -> $ret:expr) => {{
            Constructor {
                name: Ident { ident: intern(stringify!($name)), span },
                params: Box::from([$(Ty::Var($param)),*]),
                span,
                ty: Ty::function_type([$(Ty::Var($param)),*], $ret),
            }
        }};
    }

    macro_rules! instances {
        ($($instance:expr,)+) => {{
            [
                $(
                    (
                        $instance,
                        InstanceData { constraints: ClassConstraintSet::new(), span },
                    )
                ,)+
            ].into_iter().collect::<FxHashMap<Ty, InstanceData>>()
        }};
    }

    let mut classes = FxHashMap::default();
    let mut types = FxHashMap::default();

    let ordering_type = Ty::Named {
        name: Path::from_ident(Ident {
            ident: global::intern_symbol("Ordering"),
            span,
        }),
        args: Rc::from([]),
    };

    let eq_instances = instances!(Ty::Unit, Ty::Int, Ty::Bool, Ty::Char,);
    let num_instances = instances!(Ty::Int,);
    let bool_instances = instances!(Ty::Bool,);

    class!(classes, eq_instances, Eq,
        signature!(eq: (instance_ty.clone(), instance_ty.clone(),) -> Ty::Bool);
        signature!(default ne: (instance_ty.clone(), instance_ty.clone(),) -> Ty::Bool);
    );
    class!(classes, num_instances.clone(), Add,
        signature!(add: (instance_ty.clone(), instance_ty.clone(),) -> instance_ty.clone());
    );
    class!(classes, num_instances.clone(),Sub,
        signature!(sub: (instance_ty.clone(), instance_ty.clone(),) -> instance_ty.clone());
    );
    class!(classes, num_instances.clone(),Mul,
        signature!(mul: (instance_ty.clone(), instance_ty.clone(),) -> instance_ty.clone());
    );
    class!(classes,num_instances.clone(), Div,
        signature!(div: (instance_ty.clone(), instance_ty.clone(),) -> instance_ty.clone());
        signature!(rem: (instance_ty.clone(), instance_ty.clone(),) -> instance_ty.clone());
    );
    class!(classes, num_instances.clone(),Neg,
        signature!(neg: (instance_ty.clone(),) -> instance_ty.clone());
        signature!(abs: (instance_ty.clone(),) -> instance_ty.clone());
    );
    class!(classes,bool_instances.clone(), Not,
        signature!(not: (instance_ty.clone(),) -> instance_ty.clone());
    );
    class!(classes,bool_instances.clone(), And,
        signature!(and: (instance_ty.clone(), instance_ty.clone(),) -> Ty::Bool);
    );
    class!(classes,bool_instances, Or,
        signature!(or: (instance_ty.clone(), instance_ty.clone(),) -> Ty::Bool);
    );
    class!(classes, num_instances.clone(), {Eq} => Cmp,
        signature!(cmp: (instance_ty.clone(), instance_ty.clone(),) -> ordering_type.clone());
        signature!(default lt: (instance_ty.clone(), instance_ty.clone(),) -> Ty::Bool);
        signature!(default gt: (instance_ty.clone(), instance_ty.clone(),) -> Ty::Bool);
        signature!(default ge: (instance_ty.clone(), instance_ty.clone(),) -> Ty::Bool);
        signature!(default le: (instance_ty.clone(), instance_ty.clone(),) -> Ty::Bool);
    );
    class!(classes, num_instances, {Add Sub Mul Div Neg Cmp} => Number,
        signature!(from_int: (Ty::Int,) -> instance_ty);
    );

    type_decl!(
        types,
        Ordering = constructor!(Less -> ordering_type.clone()),
        constructor!(Equal -> ordering_type.clone()),
        constructor!(Greater -> ordering_type),
    );

    // type_decl!(
    //     classes,
    //     Option 1 = constructor!(None -> option_type.clone()),
    //     constructor!(Some 1 -> option_type.clone()),
    // );

    ModuleData {
        types,
        classes,
        ..Default::default()
    }
}

#[derive(Debug, Clone)]
pub struct Ctx {
    modules:        FxHashMap<Ident, ModuleData>,
    env:            Vec<FxHashMap<Ident, VarData>>,
    current_module: Ident,
}

impl Default for Ctx {
    fn default() -> Self {
        let env = default_classes();
        let mut ctx = Self {
            env:            vec![FxHashMap::default()],
            modules:        FxHashMap::default(),
            current_module: Ident::default(),
        };
        ctx.insert_module(
            Ident {
                ident: global::intern_symbol("prelude"),
                span:  Span::default(),
            },
            env,
        );
        ctx
    }
}

impl Ctx {
    pub const fn current_module(&self) -> Ident {
        self.current_module
    }

    pub const fn set_current_module(&mut self, module: Ident) {
        self.current_module = module;
    }

    pub fn get(&self, id: Ident) -> CheckResult<&VarData> {
        self.env
            .iter()
            .rev()
            .find_map(|e| e.get(&id))
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_var(&self, id: Ident) -> CheckResult<&VarData> {
        self.get(id).or_else(|_| {
            let current = self.current()?;
            current.get_var(id).or_else(|_| {
                let import = current.get_import(id)?;
                self.get_module(import)?.get_var(id)
            })
        })
    }

    pub fn insert_var(&mut self, name: Ident, data: VarData) -> Option<VarData> {
        self.env.last_mut().unwrap().insert(name, data)
    }

    pub fn current(&self) -> CheckResult<&ModuleData> {
        self.modules.get(&self.current_module).ok_or_else(|| {
            CheckError::new(
                CheckErrorKind::Unbound(self.current_module.ident),
                self.current_module.span,
            )
        })
    }

    pub fn current_mut(&mut self) -> CheckResult<&mut ModuleData> {
        self.modules.get_mut(&self.current_module).ok_or_else(|| {
            CheckError::new(
                CheckErrorKind::Unbound(self.current_module.ident),
                self.current_module.span,
            )
        })
    }

    pub fn get_module(&self, id: Ident) -> CheckResult<&ModuleData> {
        self.modules
            .get(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::NotModule(id.ident), id.span))
    }

    pub fn get_module_mut(&mut self, id: Ident) -> CheckResult<&mut ModuleData> {
        self.modules
            .get_mut(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::NotModule(id.ident), id.span))
    }

    pub fn create_module(&mut self, id: Ident) {
        self.modules.insert(id, ModuleData::default());
        self.current_module = id;
        let _ = self.import_prelude();
    }

    fn insert_module(&mut self, id: Ident, data: ModuleData) {
        self.modules.insert(id, data);
    }

    pub fn extend_module(&mut self, name: Ident, data: FxHashMap<Ident, VarData>) {
        self.modules.entry(name).or_default().lets.extend(data);
    }

    pub fn push_scope(&mut self) {
        self.env.push(FxHashMap::default());
    }

    pub fn current_scope(&self) -> Option<&FxHashMap<Ident, VarData>> {
        self.env.last()
    }

    pub fn pop_scope(&mut self) -> Option<FxHashMap<Ident, VarData>> {
        self.env.pop()
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

    pub fn insert_constructor_for_ty(
        &mut self,
        name: Ident,
        params: &Rc<[u64]>,
        ctor: &TypedConstructor,
    ) -> CheckResult<()> {
        let module = self.current_mut()?;

        let data = module
            .types
            .entry(name)
            .or_insert_with(|| TyData::new(params.clone(), Vec::default()));

        if let Some(prev) = data.constructors.iter().find(|c| c.name == ctor.name) {
            Err(CheckError::new(
                CheckErrorKind::SameNameConstructor(ctor.name.ident, prev.span),
                ctor.span,
            ))
        } else {
            data.constructors.push(ctor.clone());
            Ok(())
        }
    }

    pub fn get_constructor(&self, id: &Path) -> CheckResult<&Ty> {
        match *id.segments.as_slice() {
            [id] => {
                let current = self.current()?;
                current
                    .get_constructor(id)
                    .or_else(|_| {
                        let module = current.get_import(id)?;
                        self.get_module(module)?.get_constructor(id)
                    })
                    .map(VarData::ty)
            }

            [ty, id] => {
                let current = self.current()?;
                let data = current.get_type(ty).or_else(|_| {
                    let module = current.get_import(ty)?;
                    self.get_module(module)?.get_type(ty)
                })?;

                data.constructors
                    .iter()
                    .find_map(|c| if c.name == id { Some(&c.ty) } else { None })
                    .ok_or_else(|| {
                        CheckError::new(CheckErrorKind::NotConstructorName(id.ident), id.span)
                    })
            }
            [_, _, _] => todo!(),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(id.clone()),
                id.span(),
            )),
        }
    }

    fn get_maybe_import<T, F>(&self, module: Ident, id: Ident, f: F) -> CheckResult<&T>
    where
        F: Fn(&ModuleData, Ident) -> CheckResult<&T>,
    {
        let module = self.get_module(module)?;
        f(module, id).or_else(|_| {
            let import = module.get_import(id)?;
            let module = self.get_module(import)?;
            f(module, id)
        })
    }

    fn get_maybe_import_mut<T, F, FMut>(
        &mut self,
        module: Ident,
        id: Ident,
        f: F,
        fmut: FMut,
    ) -> CheckResult<&mut T>
    where
        F: Fn(&ModuleData, Ident) -> CheckResult<&T>,
        FMut: Fn(&mut ModuleData, Ident) -> CheckResult<&mut T>,
    {
        let data = self.get_module(module)?;
        if f(data, id).is_ok() {
            fmut(self.get_module_mut(module).unwrap(), id)
        } else {
            let import = data.get_import(id)?;
            let data = self.get_module_mut(import)?;
            fmut(data, id)
        }
    }

    pub fn get_ty(&self, id: &Path) -> CheckResult<&TyData> {
        match *id.segments.as_slice() {
            [id] => self.get_maybe_import(self.current_module, id, ModuleData::get_type),
            [module, id] => self.get_maybe_import(module, id, ModuleData::get_type),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(id.clone()),
                id.span(),
            )),
        }
    }

    pub fn get_class(&self, name: &Path) -> CheckResult<&ClassData> {
        match *name.segments.as_slice() {
            [id] => self.get_maybe_import(self.current_module, id, ModuleData::get_class),
            [module, id] => self.get_maybe_import(module, id, ModuleData::get_class),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(name.clone()),
                name.span(),
            )),
        }
    }

    pub fn get_class_mut(&mut self, name: &Path) -> CheckResult<&mut ClassData> {
        match *name.segments.as_slice() {
            [id] => self.get_maybe_import_mut(
                self.current_module,
                id,
                ModuleData::get_class,
                ModuleData::get_class_mut,
            ),
            [module, id] => self.get_maybe_import_mut(
                module,
                id,
                ModuleData::get_class,
                ModuleData::get_class_mut,
            ),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(name.clone()),
                name.span(),
            )),
        }
    }

    #[must_use]
    pub fn get_constructors_for_ty(&self, name: &Path) -> &[TypedConstructor] {
        self.get_ty(name)
            .map_or(&[], |data| data.constructors.as_slice())
    }

    pub fn get_type_arity(&self, name: &Path) -> CheckResult<usize> {
        self.get_ty(name).map(|data| data.params.len())
    }

    pub fn insert_class(&mut self, name: Ident, data: ClassData) -> CheckResult<()> {
        self.current_mut()?.insert_class(name, data);
        Ok(())
    }

    pub fn import<'a>(
        &mut self,
        to: Ident,
        imports: impl IntoIterator<Item = &'a Path>,
    ) -> CheckResult<()> {
        for path in imports {
            self.import_single(to, path)?;
        }
        Ok(())
    }

    fn import_prelude(&mut self) -> CheckResult<()> {
        let prelude_name = Ident {
            ident: global::intern_symbol("prelude"),
            span:  Span::default(),
        };
        let prelude = self.get_module(prelude_name)?;

        let mut to_import = Vec::new();

        to_import.extend(prelude.classes.keys());
        to_import.extend(prelude.types.keys());
        to_import.extend(prelude.vals.keys());

        for import in to_import {
            self.current_mut()?.insert_import(import, prelude_name);
        }

        Ok(())
    }

    fn import_single(&mut self, to: Ident, what: &Path) -> CheckResult<()> {
        let &[module, id] = what.segments.as_slice() else {
            return Err(CheckError::new(
                CheckErrorKind::InvalidPath(what.clone()),
                what.span(),
            ));
        };

        if module == to {
            return Ok(());
        }

        let module_data = self.get_module(module)?;

        if !module_data.exportable(id) {
            return Err(CheckError::new(
                CheckErrorKind::InvalidImport(what.clone()),
                what.span(),
            ));
        }

        let to = self.get_module_mut(to)?;
        to.insert_import(id, module);

        Ok(())
    }

    pub fn insert_instance_at_env(
        &mut self,
        ty: Ty,
        class: Ident,
        data: InstanceData,
    ) -> CheckResult<()> {
        let class_data = self.current_mut()?.get_class_mut(class)?;

        let span = data.span;
        match class_data.instances.insert(ty.clone(), data) {
            Some(previous) => Err(CheckError::new(
                CheckErrorKind::MultipleInstances(Path::from_ident(class), ty, previous.span),
                span,
            )),
            None => Ok(()),
        }
    }

    pub fn insert_instance(&mut self, ty: Ty, class: &Path, data: InstanceData) -> CheckResult<()> {
        let class_data = self.get_class_mut(class)?;

        let span = data.span;
        match class_data.instances.insert(ty.clone(), data) {
            Some(previous) => Err(CheckError::new(
                CheckErrorKind::MultipleInstances(class.clone(), ty, previous.span),
                span,
            )),
            None => Ok(()),
        }
    }

    pub fn assume_constraints(&mut self, set: &ClassConstraintSet) {
        for c in set.iter() {
            let _ = self.insert_instance(
                c.constrained().clone(),
                c.class(),
                InstanceData::new(ClassConstraintSet::new(), c.span()),
            );
        }
    }

    pub fn assume_constraint_tree(&mut self, ty: &Ty, set: &ClassConstraintSet) {
        for c in set.iter() {
            let Ok(constrs) = self
                .get_class(c.class())
                .map(|data| data.constraints.clone())
            else {
                continue;
            };
            self.assume_constraint_tree(ty, &constrs);
            for c in set.iter() {
                let _ = self.insert_instance(
                    ty.clone(),
                    c.class(),
                    InstanceData::new(ClassConstraintSet::new(), c.span()),
                );
            }
        }
    }

    #[must_use]
    pub fn get_constructor_subtypes(&self, ty: &Ty, idx: usize) -> Box<[Ty]> {
        if let Ty::Tuple(types) = ty {
            return types.to_vec().into_boxed_slice();
        }

        let Ty::Named { name, args } = ty else {
            return Box::default();
        };

        let mut data = self.get_ty(name).cloned().unwrap_or_default();

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

    pub fn write_variant_name(
        &self,
        f: &mut impl std::fmt::Write,
        ty: &Ty,
        idx: usize,
    ) -> std::fmt::Result {
        let Ty::Named { name, .. } = ty else {
            return Ok(());
        };
        let ctor = self.get_constructors_for_ty(name)[idx].name;
        write!(f, "{ctor}")
    }

    pub fn implementation(&self, ty: &Ty, class: &Path) -> CheckResult<&InstanceData> {
        let class_data = self.get_class(class)?;

        let instance = if ty.is_scheme() {
            class_data.instances.iter().find_map(|(instance, data)| {
                if ty.equivalent(instance) {
                    Some(data)
                } else {
                    None
                }
            })
        } else {
            class_data.instances.get(ty)
        };

        instance.ok_or_else(|| {
            CheckError::new(
                CheckErrorKind::NotInstance(ty.clone(), class.clone()),
                class.span(),
            )
        })
    }

    fn implementation_mut(&mut self, ty: &Ty, class: &Path) -> CheckResult<&mut InstanceData> {
        let class_data = self.get_class_mut(class)?;

        let instance = if ty.is_scheme() {
            class_data
                .instances
                .iter_mut()
                .find_map(|(instance, data)| {
                    if ty.equivalent(instance) {
                        Some(data)
                    } else {
                        None
                    }
                })
        } else {
            class_data.instances.get_mut(ty)
        };

        instance.ok_or_else(|| {
            CheckError::new(
                CheckErrorKind::NotInstance(ty.clone(), class.clone()),
                class.span(),
            )
        })
    }

    pub fn instantiate_class(
        &self,
        class: &Path,
        ty: &Ty,
        span: Span,
    ) -> Result<(), Vec<ClassConstraint>> {
        if self.implementation(ty, class).is_ok() {
            return Ok(());
        }

        let data = self
            .get_class(class)
            .map_err(|_| vec![ClassConstraint::new(class.clone(), ty.clone(), span)])?;

        for (instance, data) in &data.instances {
            if let Ty::Scheme {
                ty: instance_ty, ..
            } = instance
            {
                let Some(args) = instance_ty.zip_args(ty) else {
                    continue;
                };

                let mut constraints = Vec::new();

                data.constraints()
                    .iter()
                    .filter_map(|constr| {
                        args.iter().find_map(|(a1, a2)| {
                            if constr.constrained() == a1 {
                                self.instantiate_class(constr.class(), a2, span).err()
                            } else {
                                None
                            }
                        })
                    })
                    .for_each(|mut constr| {
                        constraints.append(&mut constr);
                    });

                return if constraints.is_empty() {
                    Ok(())
                } else {
                    Err(constraints)
                };
            }
        }

        Err(vec![ClassConstraint::new(class.clone(), ty.clone(), span)])
    }

    pub fn set_constraints(&mut self, class: &Path, ty: &Ty, constr: ClassConstraintSet) {
        self.implementation_mut(ty, class).unwrap().constraints = constr;
    }

    pub fn new_path_from_current(&self, name: Ident) -> Path {
        let mut module = self.current_module;
        module.span = name.span;
        Path {
            segments: smallvec![module, name],
        }
    }
}

impl Display for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, module) in &self.modules {
            writeln!(f, "module {id} =")?;
            write!(f, "{module}")?;
        }
        Ok(())
    }
}

impl Display for ModuleData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, import) in &self.imports {
            writeln!(f, "  import {id}::{import}")?;
        }

        for (id, class) in &self.classes {
            writeln!(
                f,
                "  class {}{id} '{} =",
                class.constraints(),
                class.instance_var()
            )?;
            for (id, sig) in class.signatures() {
                writeln!(f, "    val {}{id}: {}", sig.set, sig.ty)?;
            }
            for (ty, data) in &class.instances {
                writeln!(f, "    instance {}{ty}", data.constraints)?;
            }
        }

        for (id, ty) in &self.types {
            write!(f, "  type {id}")?;
            for p in ty.params() {
                write!(f, " '{p}")?;
            }
            write!(f, " =")?;
            for c in ty.constructors() {
                write!(f, " | {}", c.name)?;
                for p in &c.params {
                    write!(f, " {p}")?;
                }
            }
            writeln!(f)?;
        }

        for (id, bind) in self
            .lets
            .iter()
            .chain(self.vals.iter())
            .chain(self.constructors.iter())
        {
            writeln!(f, "  val {}{id}: {}", bind.constrs, bind.ty)?;
        }

        Ok(())
    }
}

impl Substitute for Ctx {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.env
            .iter_mut()
            .flat_map(FxHashMap::values_mut)
            .for_each(|t| t.substitute(subs));
    }
}
