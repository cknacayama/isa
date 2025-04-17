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
    types:        FxHashMap<Ident, TyData>,
    constructors: FxHashMap<Ident, VarData>,
    classes:      FxHashMap<Ident, ClassDataImport>,
}

impl ModuleData {
    pub fn get_type(&self, id: Ident) -> CheckResult<&TyData> {
        self.types
            .get(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_val(&self, id: Ident) -> CheckResult<&VarData> {
        self.vals
            .get(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_var(&self, id: Ident) -> CheckResult<&VarData> {
        self.get_let(id).or_else(|_| self.get_val(id))
    }

    pub fn get_let(&self, id: Ident) -> CheckResult<&VarData> {
        self.lets
            .get(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_constructor(&self, id: Ident) -> CheckResult<&VarData> {
        self.constructors
            .get(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    fn get_class(&self, id: Ident) -> CheckResult<&ClassDataImport> {
        self.classes
            .get(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_type_mut(&mut self, id: Ident) -> CheckResult<&mut TyData> {
        self.types
            .get_mut(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_val_mut(&mut self, id: Ident) -> CheckResult<&mut VarData> {
        self.vals
            .get_mut(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_let_mut(&mut self, id: Ident) -> CheckResult<&mut VarData> {
        self.lets
            .get_mut(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_constructor_mut(&mut self, id: Ident) -> CheckResult<&mut VarData> {
        self.constructors
            .get_mut(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_class_data_mut(&mut self, id: Ident) -> CheckResult<&mut ClassData> {
        self.classes
            .get_mut(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
            .and_then(|class| {
                class
                    .as_class_mut()
                    .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotClass, id))
            })
    }

    fn get_class_mut(&mut self, id: Ident) -> CheckResult<&mut ClassDataImport> {
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

    pub fn insert_class(&mut self, id: Ident, data: ClassData) -> Option<ClassDataImport> {
        self.classes.insert(id, ClassDataImport::Class(data))
    }

    pub fn insert_class_import(&mut self, id: Ident, data: Ident) -> Option<ClassDataImport> {
        self.classes.insert(id, ClassDataImport::Import(data))
    }

    fn exportable(&self, id: Ident) -> bool {
        self.classes.get(&id).is_some_and(ClassDataImport::is_class)
            || self.types.contains_key(&id)
            || self.lets.contains_key(&id)
            || self.vals.contains_key(&id)
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
    imported:     Option<Ident>,
}

impl TyData {
    #[must_use]
    const fn new(params: Rc<[u64]>, constructors: Vec<TypedConstructor>) -> Self {
        Self {
            params,
            constructors,
            imported: None,
        }
    }

    fn as_import(self, module: Ident) -> Self {
        Self {
            imported: Some(module),
            ..self
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
enum ClassDataImport {
    Import(Ident),
    Class(ClassData),
}

impl ClassDataImport {
    const fn as_import(&self) -> Option<Ident> {
        if let Self::Import(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    const fn as_class(&self) -> Option<&ClassData> {
        if let Self::Class(v) = self {
            Some(v)
        } else {
            None
        }
    }

    const fn as_class_mut(&mut self) -> Option<&mut ClassData> {
        if let Self::Class(v) = self {
            Some(v)
        } else {
            None
        }
    }

    #[must_use]
    const fn is_import(&self) -> bool {
        matches!(self, Self::Import(..))
    }

    #[must_use]
    const fn is_class(&self) -> bool {
        matches!(self, Self::Class(..))
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
            $classes.insert(Ident { ident: intern(stringify!($name)), span }, ClassDataImport::Class(data));
        }};
        ($classes:ident, $instances:expr, $name:ident, $($member:expr;)+) => {{
            let mut data = ClassData::with_instances(ClassConstraintSet::new(), 0, $instances, span);
            data.extend_signature([
                $($member),+
            ]);
            $classes.insert(Ident { ident: intern(stringify!($name)), span }, ClassDataImport::Class(data));
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
            current.get_var(id)
        })
    }

    pub fn insert_var(&mut self, name: Ident, data: VarData) -> Option<VarData> {
        self.env.last_mut().unwrap().insert(name, data)
    }

    pub fn current(&self) -> CheckResult<&ModuleData> {
        self.modules
            .get(&self.current_module)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, self.current_module))
    }

    pub fn current_mut(&mut self) -> CheckResult<&mut ModuleData> {
        self.modules
            .get_mut(&self.current_module)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, self.current_module))
    }

    pub fn get_module(&self, id: Ident) -> CheckResult<&ModuleData> {
        self.modules
            .get(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotModule, id))
    }

    pub fn get_module_mut(&mut self, id: Ident) -> CheckResult<&mut ModuleData> {
        self.modules
            .get_mut(&id)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotModule, id))
    }

    pub fn create_module(&mut self, id: Ident) -> CheckResult<()> {
        let prelude = self.import_prelude()?;
        self.modules.insert(id, prelude);
        self.current_module = id;
        Ok(())
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
                current.get_constructor(id).map(VarData::ty)
            }

            [ty, id] => {
                let current = self.current()?;
                let data = current.get_type(ty)?;

                data.constructors
                    .iter()
                    .find_map(|c| if c.name == id { Some(&c.ty) } else { None })
                    .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotConstructorName, id))
            }
            [_, _, _] => todo!(),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(id.clone()),
                id.span(),
            )),
        }
    }

    fn get_from_module<T, F>(&self, module: Ident, id: Ident, f: F) -> CheckResult<&T>
    where
        F: FnOnce(&ModuleData, Ident) -> CheckResult<&T>,
    {
        let module = self.get_module(module)?;
        f(module, id)
    }

    fn get_from_module_mut<T, F>(&mut self, module: Ident, id: Ident, f: F) -> CheckResult<&mut T>
    where
        F: FnOnce(&mut ModuleData, Ident) -> CheckResult<&mut T>,
    {
        let module = self.get_module_mut(module)?;
        f(module, id)
    }

    pub fn get_ty(&self, id: &Path) -> CheckResult<&TyData> {
        let (module, id) = self.get_module_and_ident(id)?;

        self.get_from_module(module, id, ModuleData::get_type)
    }

    pub fn get_class(&self, name: &Path) -> CheckResult<&ClassData> {
        let (module, id) = self.get_module_and_ident(name)?;

        let class = self.get_from_module(module, id, ModuleData::get_class)?;
        match class {
            ClassDataImport::Import(module) => Ok(self
                .get_from_module(*module, id, ModuleData::get_class)
                .unwrap()
                .as_class()
                .unwrap()),
            ClassDataImport::Class(class_data) => Ok(class_data),
        }
    }

    pub fn get_class_mut(&mut self, name: &Path) -> CheckResult<&mut ClassData> {
        let (mut module, id) = self.get_module_and_ident(name)?;

        let class = self.get_from_module(module, id, ModuleData::get_class)?;

        if let Some(import) = class.as_import() {
            module = import;
        }

        Ok(self
            .get_from_module_mut(module, id, ModuleData::get_class_mut)
            .unwrap()
            .as_class_mut()
            .unwrap())
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

    fn get_module_and_ident(&self, path: &Path) -> CheckResult<(Ident, Ident)> {
        match *path.segments.as_slice() {
            [id] => Ok((self.current_module, id)),
            [module, id] => Ok((module, id)),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(path.clone()),
                path.span(),
            )),
        }
    }

    pub fn same_type_name(&self, lhs: &Path, rhs: &Path) -> CheckResult<bool> {
        let (lhs_module, lhs_ty) = self.get_module_and_ident(lhs)?;
        let (rhs_module, rhs_ty) = self.get_module_and_ident(rhs)?;

        if lhs_ty != rhs_ty {
            return Ok(false);
        }
        if lhs_module == rhs_module {
            return Ok(true);
        }

        let lhs = self.get_ty(lhs)?;
        let rhs = self.get_ty(rhs)?;

        let lhs = lhs.imported.unwrap_or(lhs_module);
        let rhs = rhs.imported.unwrap_or(rhs_module);

        Ok(lhs == rhs)
    }

    fn import_prelude(&self) -> CheckResult<ModuleData> {
        let prelude_name = Ident {
            ident: global::intern_symbol("prelude"),
            span:  Span::default(),
        };
        let prelude = self.get_module(prelude_name)?;

        let classes = prelude
            .classes
            .iter()
            .map(|(&id, _)| (id, ClassDataImport::Import(prelude_name)))
            .collect();
        let types = prelude
            .types
            .iter()
            .map(|(&id, data)| (id, data.clone().as_import(prelude_name)))
            .collect();
        let vals = prelude.vals.clone();

        let module = ModuleData {
            vals,
            types,
            classes,
            ..Default::default()
        };

        Ok(module)
    }

    pub fn insert_instance_at_env(
        &mut self,
        ty: Ty,
        class: Ident,
        data: InstanceData,
    ) -> CheckResult<()> {
        let class_data = self
            .current_mut()?
            .get_class_mut(class)?
            .as_class_mut()
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotClass, class))?;

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
                c.ty().clone(),
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

    pub fn equivalent(&self, lhs: &Ty, rhs: &Ty) -> bool {
        match (lhs, rhs) {
            (Ty::Named { name: n1, args: a1 }, Ty::Named { name: n2, args: a2 }) => {
                self.same_type_name(n1, n2).unwrap()
                    && a1.len() == a2.len()
                    && a1
                        .iter()
                        .zip(a2.iter())
                        .all(|(t1, t2)| self.equivalent(t1, t2))
            }

            (Ty::Generic { args: a1, .. }, Ty::Generic { args: a2, .. })
            | (Ty::Tuple(a1), Ty::Tuple(a2)) => {
                a1.len() == a2.len()
                    && a1
                        .iter()
                        .zip(a2.iter())
                        .all(|(t1, t2)| self.equivalent(t1, t2))
            }

            (Ty::Fn { param: p1, ret: r1 }, Ty::Fn { param: p2, ret: r2 }) => {
                self.equivalent(p1, p2) && self.equivalent(r1, r2)
            }

            (Ty::Scheme { quant: q1, ty: t1 }, Ty::Scheme { quant: q2, ty: t2 }) => {
                q1.len() == q2.len() && self.equivalent(t1, t2)
            }

            (Ty::Var(_), Ty::Var(_)) => true,

            (lhs, rhs) => lhs == rhs,
        }
    }

    pub fn implementation(&self, ty: &Ty, class: &Path) -> CheckResult<&InstanceData> {
        let class_data = self.get_class(class)?;

        let instance = if ty.is_scheme() {
            class_data.instances.iter().find_map(|(instance, data)| {
                if self.equivalent(ty, instance) {
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

    fn implementation_mut(&mut self, mut ty: Ty, class: &Path) -> CheckResult<&mut InstanceData> {
        if ty.is_scheme() {
            let class_data = self.get_class(class)?;
            let instance = class_data
                .instances
                .keys()
                .find(|instance| self.equivalent(&ty, instance));
            if let Some(instance) = instance {
                ty = instance.clone();
            }
        }

        let class_data = self.get_class_mut(class)?;

        let instance = class_data.instances.get_mut(&ty);

        instance.ok_or_else(|| {
            CheckError::new(CheckErrorKind::NotInstance(ty, class.clone()), class.span())
        })
    }

    fn zip_args(&self, lhs: &Ty, rhs: &Ty) -> Option<Vec<(Ty, Ty)>> {
        match (lhs, rhs) {
            (Ty::Named { name: n1, args: a1 }, Ty::Named { name: n2, args: a2 })
                if self.same_type_name(n1, n2).unwrap() && a1.len() == a2.len() =>
            {
                Some(a1.iter().cloned().zip(a2.iter().cloned()).collect())
            }
            (Ty::Generic { args: a1, .. }, Ty::Generic { args: a2, .. })
            | (Ty::Tuple(a1), Ty::Tuple(a2))
                if a1.len() == a2.len() =>
            {
                Some(a1.iter().cloned().zip(a2.iter().cloned()).collect())
            }
            (Ty::Fn { param: p1, ret: r1 }, Ty::Fn { param: p2, ret: r2 }) => {
                Some(vec![(p1.into(), p2.into()), (r1.into(), r2.into())])
            }
            (Ty::Scheme { quant: q1, ty: t1 }, Ty::Scheme { quant: q2, ty: t2 })
                if q1.len() == q2.len() =>
            {
                self.zip_args(t1, t2)
            }

            (Ty::Var(_), Ty::Var(_)) => Some(Vec::new()),

            (lhs, rhs) if lhs == rhs => Some(Vec::new()),

            _ => None,
        }
    }

    pub fn instantiate_class(
        &self,
        class: &Path,
        ty: &Ty,
        span: Span,
    ) -> CheckResult<Vec<ClassConstraint>> {
        if self.implementation(ty, class).is_ok() {
            return Ok(Vec::new());
        }

        let data = self.get_class(class)?;

        let Some((args, constraints)) = data.instances.iter().find_map(|(instance, data)| {
            let Ty::Scheme {
                ty: instance_ty, ..
            } = instance
            else {
                return None;
            };
            self.zip_args(instance_ty, ty)
                .map(|args| (args, data.constraints().iter()))
        }) else {
            return Ok(vec![ClassConstraint::new(class.clone(), ty.clone(), span)]);
        };

        let new = constraints
            .filter_map(|c| {
                args.iter().find_map(|(a1, a2)| {
                    if c.ty() == a1 {
                        self.instantiate_class(c.class(), a2, span).ok()
                    } else {
                        None
                    }
                })
            })
            .reduce(|mut new, mut constr| {
                new.append(&mut constr);
                new
            });

        Ok(new.unwrap_or_default())
    }

    pub fn set_constraints(&mut self, class: &Path, ty: Ty, constr: ClassConstraintSet) {
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
        for (id, class) in &self.classes {
            match class {
                ClassDataImport::Import(import) => {
                    writeln!(f, "  import {import}::{id}")?;
                }
                ClassDataImport::Class(class) => {
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
        for env in &mut self.env {
            for t in env.values_mut() {
                t.substitute(subs);
            }
        }
    }
}
