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
    const fn new(ty: Ty, constrs: ClassConstraintSet, span: Span) -> Self {
        Self { ty, constrs, span }
    }

    #[must_use]
    pub const fn ty(&self) -> &Ty {
        &self.ty
    }
}

#[derive(Debug, Clone)]
pub struct ModuleData {
    ctx: FxHashMap<Ident, CtxData>,
}

impl ModuleData {
    pub const fn new(ctx: FxHashMap<Ident, CtxData>) -> Self {
        Self { ctx }
    }

    pub const fn ctx(&self) -> &FxHashMap<Ident, CtxData> {
        &self.ctx
    }

    pub fn get(&self, id: Ident) -> CheckResult<&CtxData> {
        self.ctx
            .get(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_mut(&mut self, id: Ident) -> CheckResult<&mut CtxData> {
        self.ctx
            .get_mut(&id)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_var(&self, id: Ident) -> CheckResult<&VarData> {
        self.get(id)?
            .as_var()
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
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

#[derive(Debug, Clone)]
pub enum CtxData {
    Module(ModuleData),
    Ty(TyData),
    Class(ClassData),
    Let(VarData),
    Val(VarData),
    Constructor(VarData),
    Import(Ident),
}

impl CtxData {
    pub const fn exportable(&self) -> bool {
        matches!(
            self,
            Self::Ty(_) | Self::Class(_) | Self::Let(_) | Self::Constructor(_)
        )
    }

    pub const fn as_var(&self) -> Option<&VarData> {
        match self {
            Self::Let(var) | Self::Val(var) | Self::Constructor(var) => Some(var),
            _ => None,
        }
    }

    pub const fn as_var_mut(&mut self) -> Option<&mut VarData> {
        match self {
            Self::Let(var) | Self::Val(var) | Self::Constructor(var) => Some(var),
            _ => None,
        }
    }

    pub const fn as_ty(&self) -> Option<&TyData> {
        if let Self::Ty(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_class(&self) -> Option<&ClassData> {
        if let Self::Class(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_val(&self) -> Option<&VarData> {
        if let Self::Val(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_constructor(&self) -> Option<&VarData> {
        if let Self::Constructor(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_ty_mut(&mut self) -> Option<&mut TyData> {
        if let Self::Ty(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_class_mut(&mut self) -> Option<&mut ClassData> {
        if let Self::Class(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_module_mut(&mut self) -> Option<&mut ModuleData> {
        if let Self::Module(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_module(&self) -> Option<&ModuleData> {
        if let Self::Module(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_let(&self) -> Option<&VarData> {
        if let Self::Let(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_let_mut(&mut self) -> Option<&mut VarData> {
        if let Self::Let(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub const fn as_import(&self) -> Option<Ident> {
        if let Self::Import(v) = self {
            Some(*v)
        } else {
            None
        }
    }
}

fn default_classes() -> FxHashMap<Ident, CtxData> {
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
            $classes.insert(Ident { ident: intern(stringify!($name)), span }, CtxData::Class(data));
        }};
        ($classes:ident, $instances:expr, $name:ident, $($member:expr;)+) => {{
            let mut data = ClassData::with_instances(ClassConstraintSet::new(), 0, $instances, span);
            data.extend_signature([
                $($member),+
            ]);
            $classes.insert(Ident { ident: intern(stringify!($name)), span }, CtxData::Class(data));
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
                CtxData::Ty(TyData::new(
                        Rc::from([]),
                        vec![$($constructor),+],
                )),
            );
        }};
        ($classes:ident, $name:ident $($param:literal)+ = $($constructor:expr,)+) => {{
            $classes.insert(
                Ident {
                    ident: intern(stringify!($name)),
                    span,
                },
                CtxData::Ty(TyData::new(
                        Rc::from([$($param),+]),
                        vec![$($constructor),+],
                )),
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
        classes,
        Ordering = constructor!(Less -> ordering_type.clone()),
        constructor!(Equal -> ordering_type.clone()),
        constructor!(Greater -> ordering_type),
    );

    // type_decl!(
    //     classes,
    //     Option 1 = constructor!(None -> option_type.clone()),
    //     constructor!(Some 1 -> option_type.clone()),
    // );

    classes
}

#[derive(Debug, Clone)]
pub struct Ctx {
    env:            Vec<FxHashMap<Ident, CtxData>>,
    current_module: Ident,
}

impl Default for Ctx {
    fn default() -> Self {
        let env = default_classes();
        let mut ctx = Self {
            env:            vec![FxHashMap::default()],
            current_module: Ident::default(),
        };
        ctx.extend_module(
            Ident {
                ident: global::intern_symbol("prelude"),
                span:  Span::default(),
            },
            ModuleData::new(env),
        );
        ctx
    }
}

impl IntoIterator for Ctx {
    type Item = (Ident, CtxData);
    type IntoIter = std::iter::FlatMap<
        vec::IntoIter<FxHashMap<Ident, CtxData>>,
        hash_map::IntoIter<Ident, CtxData>,
        fn(FxHashMap<Ident, CtxData>) -> <FxHashMap<Ident, CtxData> as IntoIterator>::IntoIter,
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.env.into_iter().flat_map(FxHashMap::into_iter)
    }
}

impl Ctx {
    pub fn from_single(env: FxHashMap<Ident, CtxData>) -> Self {
        Self {
            env:            vec![env],
            current_module: Ident::default(),
        }
    }

    fn iter(&self) -> impl Iterator<Item = (&Ident, &CtxData)> {
        self.env.iter().flat_map(FxHashMap::iter)
    }

    pub const fn set_current_module(&mut self, module: Ident) {
        self.current_module = module;
    }

    pub fn get(&self, id: Ident) -> CheckResult<&CtxData> {
        self.env
            .iter()
            .rev()
            .find_map(|e| e.get(&id))
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_var(&self, id: Ident) -> CheckResult<&VarData> {
        self.resolve(id)?
            .as_var()
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_mut(&mut self, id: Ident) -> CheckResult<&mut CtxData> {
        self.env
            .iter_mut()
            .rev()
            .find_map(|e| e.get_mut(&id))
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn get_constructor(&self, id: &Path) -> CheckResult<&Ty> {
        match *id.segments.as_slice() {
            [id] => self
                .get_from_current(id)?
                .as_constructor()
                .ok_or_else(|| {
                    CheckError::new(CheckErrorKind::NotConstructorName(id.ident), id.span)
                })
                .map(VarData::ty),
            [ty, id] => self
                .get_from_current(ty)?
                .as_ty()
                .ok_or_else(|| CheckError::new(CheckErrorKind::NotType(ty.ident), ty.span))
                .and_then(|data| {
                    data.constructors
                        .iter()
                        .find_map(|c| if c.name == id { Some(&c.ty) } else { None })
                        .ok_or_else(|| {
                            CheckError::new(CheckErrorKind::NotConstructorName(id.ident), id.span)
                        })
                }),
            [_, _, _] => todo!(),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(id.clone()),
                id.span(),
            )),
        }
    }

    pub fn resolve(&self, id: Ident) -> CheckResult<&CtxData> {
        self.get(id).or_else(|_| {
            let module = self.current_module;
            self.get_from_module(module, id)
        })
    }

    fn get_from_module(&self, module: Ident, member: Ident) -> CheckResult<&CtxData> {
        let module = self.get_module(module)?;
        let data = module.get(member)?;

        data.as_import()
            .map_or(Ok(data), |module| self.get_from_module(module, member))
    }

    fn get_from_module_mut(&mut self, module: Ident, member: Ident) -> CheckResult<&mut CtxData> {
        let module_data = self.get_module(module)?;
        let data = module_data.get(member)?;

        if let Some(module) = data.as_import() {
            self.get_from_module_mut(module, member)
        } else {
            Ok(self
                .get_module_mut(module)
                .unwrap()
                .get_mut(member)
                .unwrap())
        }
    }

    pub fn get_from_current(&self, id: Ident) -> CheckResult<&CtxData> {
        self.get_from_module(self.current_module, id)
    }

    pub fn get_from_current_mut(&mut self, id: Ident) -> CheckResult<&mut CtxData> {
        self.get_from_module_mut(self.current_module, id)
    }

    pub fn get_val(&self, id: Ident) -> CheckResult<&VarData> {
        let val = self.resolve(id)?;
        val.as_val()
            .ok_or_else(|| CheckError::new(CheckErrorKind::NotVal(id.ident), id.span))
    }

    pub fn get_module(&self, id: Ident) -> CheckResult<&ModuleData> {
        let module = self.get(id)?;
        module
            .as_module()
            .ok_or_else(|| CheckError::new(CheckErrorKind::NotModule(id.ident), id.span))
    }

    pub fn get_module_mut(&mut self, id: Ident) -> CheckResult<&mut ModuleData> {
        let module = self.get_mut(id)?;
        module
            .as_module_mut()
            .ok_or_else(|| CheckError::new(CheckErrorKind::NotModule(id.ident), id.span))
    }

    fn global_scope_mut(&mut self) -> &mut FxHashMap<Ident, CtxData> {
        self.env.first_mut().unwrap()
    }

    fn global_scope(&self) -> &FxHashMap<Ident, CtxData> {
        self.env.first().unwrap()
    }

    fn extend_global(&mut self, iter: impl IntoIterator<Item = (Ident, CtxData)>) {
        self.global_scope_mut().extend(iter);
    }

    pub fn extend_module(&mut self, name: Ident, data: ModuleData) {
        match self.global_scope_mut().entry(name) {
            Entry::Occupied(mut occupied_entry) => {
                if let Some(module) = occupied_entry.get_mut().as_module_mut() {
                    module.ctx.extend(data.ctx);
                }
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(CtxData::Module(data));
            }
        }
    }

    fn insert(&mut self, id: Ident, data: CtxData) -> Option<CtxData> {
        self.env.last_mut().unwrap().insert(id, data)
    }

    pub fn insert_let(
        &mut self,
        id: Ident,
        ty: Ty,
        constrs: ClassConstraintSet,
        span: Span,
    ) -> Option<CtxData> {
        self.env
            .last_mut()
            .and_then(|env| env.insert(id, CtxData::Let(VarData::new(ty, constrs, span))))
    }

    pub fn insert_constructor(
        &mut self,
        id: Ident,
        ty: Ty,
        constrs: ClassConstraintSet,
        span: Span,
    ) -> Option<CtxData> {
        self.env
            .last_mut()
            .and_then(|env| env.insert(id, CtxData::Constructor(VarData::new(ty, constrs, span))))
    }

    pub fn insert_val(
        &mut self,
        id: Ident,
        ty: Ty,
        constrs: ClassConstraintSet,
        span: Span,
    ) -> Option<CtxData> {
        self.env
            .last_mut()
            .and_then(|env| env.insert(id, CtxData::Val(VarData::new(ty, constrs, span))))
    }

    pub fn push_scope_with_prelude(&mut self) {
        self.push_scope();
        let _ = self.import_prelude();
    }

    pub fn push_scope(&mut self) {
        self.env.push(FxHashMap::default());
    }

    pub fn current_scope(&self) -> Option<&FxHashMap<Ident, CtxData>> {
        self.env.last()
    }

    pub fn pop_scope(&mut self) -> Option<FxHashMap<Ident, CtxData>> {
        self.env.pop()
    }

    fn free_type_variables(&self) -> FxHashSet<u64> {
        let mut free = FxHashSet::default();
        for t in self
            .env
            .iter()
            .flat_map(FxHashMap::values)
            .filter_map(CtxData::as_var)
        {
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
        let module = self.get_module_mut(self.current_module)?;

        let data = module
            .ctx
            .entry(name)
            .or_insert_with(|| CtxData::Ty(TyData::new(params.clone(), Vec::default())))
            .as_ty_mut()
            .ok_or_else(|| CheckError::new(CheckErrorKind::NotType(name.ident), name.span))?;

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

    pub fn get_ty(&self, id: &Path) -> CheckResult<&TyData> {
        match *id.segments.as_slice() {
            [id] => self
                .get_from_current(id)?
                .as_ty()
                .ok_or_else(|| CheckError::new(CheckErrorKind::NotType(id.ident), id.span)),
            [module, id] => self
                .get_from_module(module, id)?
                .as_ty()
                .ok_or_else(|| CheckError::new(CheckErrorKind::NotType(id.ident), id.span)),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(id.clone()),
                id.span(),
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

    pub fn insert_class(&mut self, name: Ident, data: ClassData) -> Option<CtxData> {
        self.env
            .last_mut()
            .and_then(|env| env.insert(name, CtxData::Class(data)))
    }

    pub fn insert_instance_at_env(
        &mut self,
        ty: Ty,
        class: Ident,
        data: InstanceData,
    ) -> CheckResult<()> {
        let class_data = self
            .get_mut(class)?
            .as_class_mut()
            .ok_or_else(|| CheckError::new(CheckErrorKind::NotClass(class.ident), class.span))?;

        let span = data.span;
        match class_data.instances.insert(ty.clone(), data) {
            Some(previous) => Err(CheckError::new(
                CheckErrorKind::MultipleInstances(Path::from_ident(class), ty, previous.span),
                span,
            )),
            None => Ok(()),
        }
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

        prelude
            .ctx
            .keys()
            .map(|&id| Path {
                segments: smallvec![prelude_name, id],
            })
            .collect::<Vec<_>>()
            .into_iter()
            .for_each(|path| {
                let _ = self.import_single_current(&path);
            });

        Ok(())
    }

    fn import_single_current(&mut self, what: &Path) -> CheckResult<()> {
        let &[module, id] = what.segments.as_slice() else {
            return Err(CheckError::new(
                CheckErrorKind::InvalidPath(what.clone()),
                what.span(),
            ));
        };

        let export = self.get_from_module(module, id)?;
        if !export.exportable() {
            return Err(CheckError::new(
                CheckErrorKind::InvalidImport(what.clone()),
                what.span(),
            ));
        }

        self.insert(id, CtxData::Import(module));

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

        let export = self.get_from_module(module, id)?;
        if !export.exportable() {
            return Err(CheckError::new(
                CheckErrorKind::InvalidImport(what.clone()),
                what.span(),
            ));
        }

        let to = self.get_module_mut(to)?;

        to.ctx.insert(id, CtxData::Import(module));

        Ok(())
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

    pub fn get_class(&self, name: &Path) -> CheckResult<&ClassData> {
        match *name.segments.as_slice() {
            [id] => self
                .get_from_current(id)?
                .as_class()
                .ok_or_else(|| CheckError::new(CheckErrorKind::NotClass(id.ident), id.span)),
            [module, id] => self
                .get_from_module(module, id)?
                .as_class()
                .ok_or_else(|| CheckError::new(CheckErrorKind::NotClass(id.ident), id.span)),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(name.clone()),
                name.span(),
            )),
        }
    }

    pub fn get_class_mut(&mut self, name: &Path) -> CheckResult<&mut ClassData> {
        match *name.segments.as_slice() {
            [id] => self
                .get_from_current_mut(id)?
                .as_class_mut()
                .ok_or_else(|| CheckError::new(CheckErrorKind::NotClass(id.ident), id.span)),
            [module, id] => self
                .get_from_module_mut(module, id)?
                .as_class_mut()
                .ok_or_else(|| CheckError::new(CheckErrorKind::NotClass(id.ident), id.span)),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(name.clone()),
                name.span(),
            )),
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

    pub const fn current_module(&self) -> Ident {
        self.current_module
    }
}

impl Display for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, data) in self.iter() {
            writeln!(f, "{id}: {data}")?;
        }
        Ok(())
    }
}

impl Display for CtxData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Module(module_data) => {
                writeln!(f)?;
                for (id, data) in module_data.ctx() {
                    writeln!(f, "  {id}: {data}")?;
                }
                Ok(())
            }

            Self::Ty(data) => {
                write!(f, "type")?;
                for param in data.params() {
                    write!(f, " '{param}")?;
                }
                write!(f, " =")?;
                for ctor in data.constructors() {
                    write!(f, " | {ctor}")?;
                }
                Ok(())
            }

            Self::Class(data) => {
                writeln!(f, "class {}'{} =", data.constraints(), data.instance_var())?;
                for (id, member) in data.signatures() {
                    writeln!(f, "    {}{id}: {}", member.set, member.ty)?;
                }
                for (ty, data) in &data.instances {
                    writeln!(f, "    instance {}{ty}", data.constraints())?;
                }
                Ok(())
            }

            Self::Let(var_data) | Self::Val(var_data) | Self::Constructor(var_data) => {
                write!(f, "{} {}", var_data.constrs, var_data.ty)
            }

            Self::Import(module) => {
                write!(f, "import {module}")
            }
        }
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
            .filter_map(CtxData::as_let_mut)
            .for_each(|t| t.substitute(subs));
    }
}
