use std::fmt::Display;
use std::ops::BitOr;
use std::rc::Rc;
use std::{fmt, vec};

use rustc_hash::FxHashMap;
use smallvec::smallvec;

use super::ast::{Constructor, Import, ImportClause, ImportWildcard, Path, mod_path};
use super::error::{CheckError, CheckErrorKind, CheckResult};
use super::infer::{ClassConstraint, ClassConstraintSet, Subs, Substitute};
use super::token::Ident;
use super::types::Ty;
use crate::global::{Symbol, symbol};
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
    lets:         FxHashMap<Symbol, VarData>,
    vals:         FxHashMap<Symbol, VarData>,
    constructors: FxHashMap<Symbol, VarData>,
    types:        FxHashMap<Symbol, ImportData<TyData>>,
    classes:      FxHashMap<Symbol, ImportData<ClassData>>,
}

impl ModuleData {
    pub fn get_ty(&self, id: Ident) -> CheckResult<&ImportData<TyData>> {
        self.types
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_val(&self, id: Ident) -> CheckResult<&VarData> {
        self.vals
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_var(&self, id: Ident) -> CheckResult<&VarData> {
        self.get_let(id)
            .or_else(|_| self.get_val(id))
            .or_else(|_| self.get_constructor(id))
    }

    pub fn get_let(&self, id: Ident) -> CheckResult<&VarData> {
        self.lets
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_constructor(&self, id: Ident) -> CheckResult<&VarData> {
        self.constructors
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    fn get_class(&self, id: Ident) -> CheckResult<&ImportData<ClassData>> {
        self.classes
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_type_mut(&mut self, id: Ident) -> CheckResult<&mut ImportData<TyData>> {
        self.types
            .get_mut(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_class_data_mut(&mut self, id: Ident) -> CheckResult<&mut ClassData> {
        self.classes
            .get_mut(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
            .and_then(|class| {
                class
                    .as_own_mut()
                    .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotClass, id))
            })
    }

    fn get_class_mut(&mut self, id: Ident) -> CheckResult<&mut ImportData<ClassData>> {
        self.classes
            .get_mut(&id.ident)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn insert_type(&mut self, id: Symbol, data: TyData) -> Option<ImportData<TyData>> {
        self.types.insert(id, ImportData::Own(data))
    }

    pub fn insert_val(&mut self, id: Symbol, data: VarData) -> Option<VarData> {
        self.vals.insert(id, data)
    }

    pub fn insert_constructor(&mut self, id: Symbol, data: VarData) -> Option<VarData> {
        self.constructors.insert(id, data)
    }

    pub fn insert_class(&mut self, id: Symbol, data: ClassData) -> Option<ImportData<ClassData>> {
        self.classes.insert(id, ImportData::Own(data))
    }

    fn insert_class_import(&mut self, id: Symbol, data: Ident) -> Option<ImportData<ClassData>> {
        self.classes.insert(id, ImportData::Import(data))
    }

    fn insert_type_import(&mut self, id: Symbol, data: Ident) -> Option<ImportData<TyData>> {
        self.types.insert(id, ImportData::Import(data))
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

impl IdGenerator {
    pub const fn new() -> Self {
        Self(0)
    }
}

impl Default for IdGenerator {
    fn default() -> Self {
        Self::new()
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
    constructors: Vec<Constructor<Ty>>,
    span:         Span,
}

impl TyData {
    #[must_use]
    const fn new(params: Rc<[u64]>, constructors: Vec<Constructor<Ty>>, span: Span) -> Self {
        Self {
            params,
            constructors,
            span,
        }
    }

    fn constructors(&self) -> &[Constructor<Ty>] {
        &self.constructors
    }

    pub fn find_constructor(&self, ctor: Ident) -> CheckResult<&Constructor<Ty>> {
        self.constructors
            .iter()
            .find(|c| c.name == ctor)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotConstructorName, ctor))
    }

    fn params(&self) -> &[u64] {
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

    pub fn resolve(aliases: &mut [(Path, Self)]) {
        let mut changed = true;
        while changed {
            changed = false;
            let cloned = aliases.to_vec();
            for (alias, data) in cloned {
                let mut subs = |ty: &Ty| match ty {
                    Ty::Named { name, args } if name == &alias => {
                        changed = true;
                        Some(data.subs(args))
                    }
                    _ => None,
                };
                for (_, alias) in aliases.iter_mut().filter(|(name, _)| name != &alias) {
                    alias.substitute(&mut subs);
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct InstanceData {
    set:  ClassConstraintSet,
    span: Span,
}

impl InstanceData {
    pub const fn new(set: ClassConstraintSet, span: Span) -> Self {
        Self { set, span }
    }

    pub const fn set(&self) -> &ClassConstraintSet {
        &self.set
    }
}

#[derive(Debug, Clone)]
pub struct MemberData {
    pub has_default: bool,
    pub set:         ClassConstraintSet,
    pub ty:          Ty,
    pub span:        Span,
}

#[derive(Debug, Clone)]
pub struct ClassData {
    constraints:  ClassConstraintSet,
    instance_var: u64,
    signatures:   FxHashMap<Ident, MemberData>,
    instances:    FxHashMap<Ty, InstanceData>,
    span:         Span,
}

impl ClassData {
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
pub enum ImportData<T> {
    Import(Ident),
    Own(T),
}

impl<T> ImportData<T> {
    const fn as_import(&self) -> Option<Ident> {
        if let Self::Import(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    const fn as_own(&self) -> Option<&T> {
        if let Self::Own(v) = self {
            Some(v)
        } else {
            None
        }
    }

    const fn as_own_mut(&mut self) -> Option<&mut T> {
        if let Self::Own(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct OperatorData {
    ty:  Ty,
    set: ClassConstraintSet,
}

impl OperatorData {
    pub fn new<T>(ty: Ty, set: T) -> Self
    where
        ClassConstraintSet: From<T>,
    {
        Self {
            ty,
            set: ClassConstraintSet::from(set),
        }
    }

    pub const fn ty(&self) -> &Ty {
        &self.ty
    }

    pub const fn set(&self) -> &ClassConstraintSet {
        &self.set
    }
}

#[derive(Debug, Default, Clone)]
pub struct Ctx {
    modules:        FxHashMap<Symbol, ModuleData>,
    env:            Vec<FxHashMap<Symbol, VarData>>,
    infix:          FxHashMap<Symbol, OperatorData>,
    prefix:         FxHashMap<Symbol, OperatorData>,
    empty_args:     Rc<[Ty]>,
    current_module: Ident,
}

impl Ctx {
    pub const fn current_module(&self) -> Ident {
        self.current_module
    }

    pub fn unit(&self) -> Ty {
        Ty::Tuple(self.empty_args.clone())
    }

    pub const fn set_current_module(&mut self, module: Ident) {
        self.current_module = module;
    }

    pub fn get(&self, id: Ident) -> CheckResult<&VarData> {
        self.env
            .iter()
            .rev()
            .find_map(|e| e.get(&id.ident))
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_var(&self, id: Ident) -> CheckResult<&VarData> {
        self.get(id).or_else(|_| {
            let current = self.current()?;
            current.get_var(id)
        })
    }

    pub fn insert_var(&mut self, name: Symbol, data: VarData) -> Option<VarData> {
        self.env.last_mut().unwrap().insert(name, data)
    }

    pub fn insert_infix(&mut self, op: Symbol, data: OperatorData) -> Option<OperatorData> {
        self.infix.insert(op, data)
    }

    pub fn insert_prefix(&mut self, op: Symbol, data: OperatorData) -> Option<OperatorData> {
        self.prefix.insert(op, data)
    }

    pub fn get_infix(&self, op: Ident) -> CheckResult<&OperatorData> {
        self.infix
            .get(&op.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, op))
    }

    pub fn get_prefix(&self, op: Ident) -> CheckResult<&OperatorData> {
        self.prefix
            .get(&op.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, op))
    }

    pub fn current(&self) -> CheckResult<&ModuleData> {
        self.modules
            .get(&self.current_module.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, self.current_module))
    }

    pub const fn current_depth(&self) -> usize {
        self.env.len()
    }

    pub fn current_mut(&mut self) -> CheckResult<&mut ModuleData> {
        self.modules
            .get_mut(&self.current_module.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, self.current_module))
    }

    pub fn get_module(&self, id: Ident) -> CheckResult<&ModuleData> {
        self.modules
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotModule, id))
    }

    pub fn get_module_mut(&mut self, id: Ident) -> CheckResult<&mut ModuleData> {
        self.modules
            .get_mut(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotModule, id))
    }

    pub fn create_module(&mut self, id: Ident) {
        self.current_module = id;
        self.insert_module(id.ident, ModuleData::default());
    }

    fn insert_module(&mut self, id: Symbol, data: ModuleData) {
        self.modules.insert(id, data);
    }

    pub fn extend_module(&mut self, name: Symbol, data: FxHashMap<Symbol, VarData>) {
        self.modules.entry(name).or_default().lets.extend(data);
    }

    pub fn push_scope(&mut self) {
        self.env.push(FxHashMap::default());
    }

    pub fn pop_scope(&mut self) -> Option<FxHashMap<Symbol, VarData>> {
        self.env.pop()
    }

    fn free_type_variables(&self) -> Vec<u64> {
        self.env
            .iter()
            .skip(1)
            .flat_map(FxHashMap::values)
            .map(|data| data.ty().free_type_variables())
            .reduce(|mut acc, v| {
                acc.extend(v);
                acc
            })
            .unwrap_or_default()
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

    pub fn insert_ty(&mut self, name: Ident, params: Rc<[u64]>) -> CheckResult<()> {
        let module = self.current_mut()?;

        module
            .insert_type(name.ident, TyData::new(params, Vec::new(), name.span))
            .map_or(Ok(()), |prev| {
                let prev = match prev {
                    ImportData::Import(ident) => {
                        let module = self.get_module(ident).unwrap();
                        let prev = module.get_ty(name).unwrap().as_own().unwrap();
                        prev.span
                    }
                    ImportData::Own(prev) => prev.span,
                };
                Err(CheckError::new(
                    CheckErrorKind::SameNameType(name.ident, prev),
                    name.span,
                ))
            })
    }

    pub fn insert_constructor_for_ty(
        &mut self,
        name: Ident,
        ctor: &Constructor<Ty>,
    ) -> CheckResult<()> {
        let module = self.current_mut()?;

        let data = module.get_type_mut(name)?.as_own_mut().unwrap();

        if let Ok(prev) = data.find_constructor(ctor.name) {
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
                let current = self.current_module;
                let data = self.get_data_from_module(current, ty, ModuleData::get_ty)?;

                data.find_constructor(id).map(|c| &c.ty)
            }

            [module, ty, id] => {
                let data = self.get_data_from_module(module, ty, ModuleData::get_ty)?;

                data.find_constructor(id).map(|c| &c.ty)
            }

            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(id.clone()),
                id.span(),
            )),
        }
    }

    fn get_data_from_module<T, F>(&self, module: Ident, id: Ident, f: F) -> CheckResult<&T>
    where
        F: Fn(&ModuleData, Ident) -> CheckResult<&ImportData<T>>,
    {
        let data = self.get_from_module(module, id, &f)?;
        match data {
            ImportData::Import(module) => Ok(self
                .get_from_module(*module, id, f)
                .unwrap()
                .as_own()
                .unwrap()),
            ImportData::Own(ty) => Ok(ty),
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

    pub fn get_ty_data(&self, id: &Path) -> CheckResult<&TyData> {
        let (module, id) = self.get_module_and_ident(id)?;
        self.get_data_from_module(module, id, ModuleData::get_ty)
    }

    pub fn get_class(&self, name: &Path) -> CheckResult<&ClassData> {
        let (module, id) = self.get_module_and_ident(name)?;
        self.get_data_from_module(module, id, ModuleData::get_class)
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
            .as_own_mut()
            .unwrap())
    }

    #[must_use]
    pub fn get_constructors_for_ty(&self, name: &Path) -> &[Constructor<Ty>] {
        self.get_ty_data(name)
            .map_or(&[], |data| data.constructors.as_slice())
    }

    pub fn get_type_arity(&self, name: &Path) -> CheckResult<usize> {
        self.get_ty_data(name).map(|data| data.params.len())
    }

    pub fn insert_class(&mut self, name: Symbol, data: ClassData) -> CheckResult<()> {
        self.current_mut()?.insert_class(name, data);
        Ok(())
    }

    fn get_module_and_ident(&self, path: &Path) -> CheckResult<(Ident, Ident)> {
        match *path.segments.as_slice() {
            [id] => {
                let cur = Ident::new(self.current_module.ident, id.span);
                Ok((cur, id))
            }
            [module, id] => Ok((module, id)),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(path.clone()),
                path.span(),
            )),
        }
    }

    pub fn resolve_type_name(&self, name: &Path) -> CheckResult<Path> {
        let (module, ty) = self.get_module_and_ident(name)?;
        let data = self.get_from_module(module, ty, ModuleData::get_ty)?;
        let module = data
            .as_import()
            .map_or(module, |id| Ident::new(id.ident, module.span));
        Ok(Path::new(smallvec![module, ty]))
    }

    fn import_from_module(&mut self, from: Ident, id: Ident) -> CheckResult<bool> {
        let module_data = self.get_module(from)?;

        if let Ok(data) = module_data.get_ty(id).cloned() {
            let from = data.as_import().unwrap_or(from);
            let new = self
                .current_mut()?
                .insert_type_import(id.ident, from)
                .is_none();
            return Ok(new);
        }
        if let Ok(data) = module_data.get_class(id).cloned() {
            let from = data.as_import().unwrap_or(from);
            let new = self
                .current_mut()?
                .insert_class_import(id.ident, from)
                .is_none();
            return Ok(new);
        }
        if let Ok(data) = module_data.get_val(id).cloned() {
            let new = self.current_mut()?.insert_val(id.ident, data).is_none();
            return Ok(new);
        }

        let path = Path {
            segments: smallvec![from, id],
        };
        let span = from.span.union(id.span);

        Err(CheckError::new(CheckErrorKind::InvalidImport(path), span))
    }

    fn import(&mut self, import: Import) -> (bool, Vec<CheckError>) {
        match import.wildcard {
            ImportWildcard::Nil => match self.import_single(&import.path) {
                Ok(ok) => (ok, Vec::new()),
                Err(err) => (false, vec![err]),
            },
            ImportWildcard::Clause(clause) => {
                let [module] = *import.path.segments.as_slice() else {
                    return (
                        false,
                        vec![CheckError::new(
                            CheckErrorKind::InvalidImport(import.path.clone()),
                            import.path.span(),
                        )],
                    );
                };
                let clause = clause
                    .into_iter()
                    .map(|mut import| {
                        let mut path = Path::new(smallvec![module]);
                        path.segments.extend(import.path.segments);
                        import.path = path;
                        import
                    })
                    .collect();
                let clause = ImportClause(clause);
                self.import_clause(clause)
            }
            ImportWildcard::Wildcard => match self.import_wildcard(&import.path) {
                Ok(ok) => (ok, Vec::new()),
                Err(err) => (false, vec![err]),
            },
        }
    }

    fn import_wildcard(&mut self, path: &Path) -> CheckResult<bool> {
        if let [module] = *path.segments.as_slice() {
            let module_data = self.get_module(module)?;

            let classes = module_data
                .classes
                .iter()
                .map(|(&id, data)| {
                    let data = ImportData::Import(data.as_import().unwrap_or(module));
                    (id, data)
                })
                .collect::<Vec<_>>();
            let types = module_data
                .types
                .iter()
                .map(|(&id, data)| {
                    let data = ImportData::Import(data.as_import().unwrap_or(module));
                    (id, data)
                })
                .collect::<Vec<_>>();
            let vals = module_data.vals.clone();
            let constructors = module_data.constructors.clone();

            let module = self.current_mut()?;

            let res = vals
                .into_iter()
                .map(|(k, v)| module.vals.insert(k, v).is_none())
                .chain(
                    types
                        .into_iter()
                        .map(|(k, v)| module.types.insert(k, v).is_none()),
                )
                .chain(
                    classes
                        .into_iter()
                        .map(|(k, v)| module.classes.insert(k, v).is_none()),
                )
                .chain(
                    constructors
                        .into_iter()
                        .map(|(k, v)| module.constructors.insert(k, v).is_none()),
                )
                .reduce(BitOr::bitor)
                .unwrap_or(false);

            Ok(res)
        } else {
            let ty_data = self.get_ty_data(path)?;
            let constructors: Vec<_> = ty_data
                .constructors
                .iter()
                .map(|c| (c.name, c.ty.clone(), c.span))
                .collect();

            let cur = self.current_mut()?;

            let res = constructors
                .into_iter()
                .map(|(ctor, ty, span)| {
                    cur.insert_constructor(
                        ctor.ident,
                        VarData::new(ty, ClassConstraintSet::new(), span),
                    )
                    .is_none()
                })
                .reduce(BitOr::bitor)
                .unwrap_or(false);

            Ok(res)
        }
    }

    pub fn import_clause(&mut self, import_clause: ImportClause) -> (bool, Vec<CheckError>) {
        let mut errors = Vec::new();
        let mut res = false;
        for import in import_clause {
            let (changed, err) = self.import(import);
            res |= changed;
            errors.extend(err);
        }
        (res, errors)
    }

    fn import_single(&mut self, path: &Path) -> CheckResult<bool> {
        match *path.segments.as_slice() {
            [module, id] => self.import_from_module(module, id),

            [module, ty, ctor] => {
                let data = self.get_data_from_module(module, ty, ModuleData::get_ty)?;
                let data = data.find_constructor(ctor)?;
                let data = VarData::new(data.ty.clone(), ClassConstraintSet::new(), path.span());
                let new = self
                    .current_mut()?
                    .insert_constructor(ctor.ident, data)
                    .is_none();
                Ok(new)
            }

            _ => Err(CheckError::new(
                CheckErrorKind::InvalidImport(path.clone()),
                path.span(),
            )),
        }
    }

    pub fn import_prelude(&mut self) -> CheckResult<bool> {
        self.import_wildcard(&mod_path!(prelude))
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
            .as_own_mut()
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

    pub fn insert_instance(
        &mut self,
        instance: Ty,
        class: &Path,
        data: InstanceData,
    ) -> CheckResult<()> {
        let constrs = if let Ty::Scheme { ty, .. } = &instance {
            self.instantiate_class(class, ty, data.span)?
        } else {
            self.instantiate_class(class, &instance, data.span)?
        };

        if let [(span, c)] = constrs.as_slice()
            && c.constrs.is_empty()
        {
            return Err(CheckError::new(
                CheckErrorKind::MultipleInstances(class.clone(), instance, *span),
                data.span,
            ));
        }

        if let Some((span, _)) = constrs.iter().find(|(_, set)| {
            set.iter().all(|c| c.ty().is_var()) && data.set().iter().all(|c| set.contains(c))
        }) {
            return Err(CheckError::new(
                CheckErrorKind::MultipleInstances(class.clone(), instance, *span),
                data.span,
            ));
        }

        let class_data = self.get_class_mut(class)?;
        class_data.instances.insert(instance, data);
        Ok(())
    }

    fn assume_instance(&mut self, ty: Ty, class: &Path, data: InstanceData) -> CheckResult<()> {
        let class_data = self.get_class_mut(class)?;
        class_data.instances.insert(ty, data);
        Ok(())
    }

    pub fn assume_constraints(&mut self, set: &ClassConstraintSet) {
        for c in set.iter() {
            let _ = self.assume_instance(
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
                let _ = self.assume_instance(
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

        let mut data = self.get_ty_data(name).cloned().unwrap_or_default();

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

    fn implementation_mut(&mut self, mut ty: Ty, class: &Path) -> CheckResult<&mut InstanceData> {
        if ty.is_scheme() {
            let class_data = self.get_class(class)?;
            let instance = class_data
                .instances
                .keys()
                .find(|instance| ty.equivalent(instance));
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

    fn zip_args(lhs: &Ty, rhs: &Ty) -> Option<Vec<(Ty, Ty)>> {
        match (lhs, rhs) {
            (Ty::Named { name: n1, args: a1 }, Ty::Named { name: n2, args: a2 })
                if n1 == n2 && a1.len() == a2.len() =>
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
                Self::zip_args(t1, t2)
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
    ) -> CheckResult<Vec<(Span, ClassConstraintSet)>> {
        let data = self.get_class(class)?;

        if let Some(data) = data.instances.get(ty) {
            return Ok(vec![(data.span, ClassConstraintSet::new())]);
        }

        let mut sets = Vec::new();
        for (args, set, inst_span) in data.instances.iter().filter_map(|(inst, data)| match inst {
            Ty::Scheme { ty: inst, .. } => {
                Self::zip_args(inst, ty).map(|args| (args, data.set().iter(), data.span))
            }
            _ => None,
        }) {
            let set = set
                .filter_map(|c| {
                    args.iter().find_map(|(a1, a2)| {
                        if c.ty() == a1 {
                            Some(self.instantiate_class(c.class(), a2, span))
                        } else {
                            None
                        }
                    })
                })
                .try_fold(ClassConstraintSet::new(), |mut new, constr| {
                    for (_, c) in constr? {
                        new.extend(c);
                    }
                    Ok(new)
                })?;
            sets.push((inst_span, set));
        }

        if sets.is_empty() {
            Ok(vec![(
                span,
                ClassConstraintSet::from(ClassConstraint::new(class.clone(), ty.clone(), span)),
            )])
        } else {
            Ok(sets)
        }
    }

    pub fn set_constraints(&mut self, class: &Path, ty: Ty, constr: ClassConstraintSet) {
        self.implementation_mut(ty, class).unwrap().set = constr;
    }
}

impl Substitute for Ctx {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        // We can skip the first scope
        // because you do not access type
        // variables from these binds
        // due to instantiation
        for env in &mut self.env[1..] {
            for t in env.values_mut() {
                t.substitute(subs);
            }
        }
    }
}

impl Substitute for AliasData {
    fn substitute<S>(&mut self, subs: &mut S)
    where
        S: FnMut(&Ty) -> Option<Ty>,
    {
        self.ty.substitute(subs);
    }
}

#[derive(Debug)]
struct TyVarFormatter<T>
where
    T: Iterator<Item = char>,
{
    vars:  FxHashMap<u64, char>,
    chars: T,
}

impl<T> TyVarFormatter<T>
where
    T: Iterator<Item = char>,
{
    fn get(&mut self, var: u64) -> char {
        *self
            .vars
            .entry(var)
            .or_insert_with(|| self.chars.next().unwrap())
    }
}

impl Ty {
    fn fmt_var<T: Iterator<Item = char>>(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        chars: &mut TyVarFormatter<T>,
    ) -> std::fmt::Result {
        match self {
            Self::Int => write!(f, "int"),
            Self::Bool => write!(f, "bool"),
            Self::Char => write!(f, "char"),
            Self::Real => write!(f, "real"),
            Self::Fn { param, ret } => {
                if param.is_simple_fmt() {
                    param.fmt_var(f, chars)?;
                } else {
                    write!(f, "(")?;
                    param.fmt_var(f, chars)?;
                    write!(f, ")")?;
                }
                write!(f, " -> ")?;
                ret.fmt_var(f, chars)
            }
            Self::Var(var) => {
                let c = chars.get(*var);
                write!(f, "'{c}")
            }
            Self::Scheme { quant, ty } => {
                for n in quant.iter() {
                    let c = chars.get(*n);
                    write!(f, "'{c} ")?;
                }
                write!(f, ". ")?;
                ty.fmt_var(f, chars)
            }
            Self::Named { name, args } => {
                write!(f, "{}", name.base_name())?;
                for arg in args.iter() {
                    if arg.is_simple_fmt() {
                        write!(f, " ")?;
                        arg.fmt_var(f, chars)?;
                    } else {
                        write!(f, " (")?;
                        arg.fmt_var(f, chars)?;
                        write!(f, ")")?;
                    }
                }
                Ok(())
            }
            Self::Generic { var, args } => {
                let var = chars.get(*var);
                write!(f, "'{var}")?;
                for arg in args.iter() {
                    if arg.is_simple_fmt() {
                        write!(f, " ")?;
                        arg.fmt_var(f, chars)?;
                    } else {
                        write!(f, " (")?;
                        arg.fmt_var(f, chars)?;
                        write!(f, ")")?;
                    }
                }
                Ok(())
            }
            Self::Tuple(types) => {
                write!(f, "(")?;
                let mut first = true;
                for ty in types.iter() {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    ty.fmt_var(f, chars)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut chars = TyVarFormatter {
            vars:  FxHashMap::default(),
            chars: ('a'..='z').chain('A'..='Z').chain('0'..='9'),
        };
        self.fmt_var(f, &mut chars)
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
        for (id, class) in self
            .classes
            .iter()
            .filter_map(|(id, class)| class.as_own().map(|c| (id, c)))
        {
            let mut chars = TyVarFormatter {
                vars:  FxHashMap::default(),
                chars: ('a'..='z').chain('A'..='Z').chain('0'..='9'),
            };
            write!(f, "  class ")?;
            class.constraints.fmt_var(f, &mut chars)?;
            writeln!(f, "{id} '{} =", chars.get(class.instance_var()))?;
            for (id, sig) in class.signatures() {
                write!(f, "    val ")?;
                sig.set.fmt_var(f, &mut chars)?;
                write!(f, "{id}: ")?;
                sig.ty.fmt_var(f, &mut chars)?;
                writeln!(f)?;
            }
            for (ty, data) in class.instances.iter().filter(|(ty, _)| !ty.is_var()) {
                let mut chars = TyVarFormatter {
                    vars:  FxHashMap::default(),
                    chars: ('a'..='z').chain('A'..='Z').chain('0'..='9'),
                };
                write!(f, "    instance ")?;
                data.set.fmt_var(f, &mut chars)?;
                ty.fmt_var(f, &mut chars)?;
                writeln!(f)?;
            }
        }

        for (id, ty) in self
            .types
            .iter()
            .filter_map(|(id, ty)| ty.as_own().map(|ty| (id, ty)))
        {
            let mut chars = TyVarFormatter {
                vars:  FxHashMap::default(),
                chars: ('a'..='z').chain('A'..='Z').chain('0'..='9'),
            };
            write!(f, "  type {id}")?;
            for p in ty.params() {
                write!(f, " '{}", chars.get(*p))?;
            }
            writeln!(f, " =")?;
            for c in ty.constructors() {
                write!(f, "    | {}", c.name)?;
                for p in &c.params {
                    write!(f, " ")?;
                    p.fmt_var(f, &mut chars)?;
                }
                writeln!(f)?;
            }
        }

        for (id, bind) in self
            .lets
            .iter()
            .filter(|(id, _)| !self.vals.contains_key(id))
            .chain(self.vals.iter())
            .chain(self.constructors.iter())
        {
            let mut chars = TyVarFormatter {
                vars:  FxHashMap::default(),
                chars: ('a'..='z').chain('A'..='Z').chain('0'..='9'),
            };
            write!(f, "  val ")?;
            bind.constrs.fmt_var(f, &mut chars)?;
            write!(f, "{id}: ")?;
            bind.ty.fmt_var(f, &mut chars)?;
            writeln!(f)?;
        }

        Ok(())
    }
}

impl ClassConstraintSet {
    fn fmt_var<T: Iterator<Item = char>>(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        chars: &mut TyVarFormatter<T>,
    ) -> std::fmt::Result {
        if self.constrs.is_empty() {
            return Ok(());
        }
        write!(f, "{{")?;
        let mut first = true;
        for ty in &self.constrs {
            if first {
                first = false;
            } else {
                write!(f, ", ")?;
            }
            write!(f, "{} ", ty.class().base_name())?;
            ty.ty().fmt_var(f, chars)?;
        }
        write!(f, "}} => ")
    }
}
