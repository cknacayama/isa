use std::fmt::Display;
use std::ops::BitOr;
use std::{fmt, vec};

use rustc_hash::FxHashMap;

use super::ast::{
    Constructor, Fixity, Ident, Import, ImportClause, ImportWildcard, Path, mod_path,
};
use super::error::{CheckError, CheckErrorKind, CheckResult};
use super::infer::{ClassConstraint, ClassConstraintSet, Subs, Substitute};
use super::types::{Ty, TyId, TyKind, TyQuant, TySlice};
use crate::global::{Span, Symbol};
use crate::separated_fmt;

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
    fn get_ty(&self, id: Ident) -> CheckResult<&ImportData<TyData>> {
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

    fn get_let(&self, id: Ident) -> CheckResult<&VarData> {
        self.lets
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    fn get_constructor(&self, id: Ident) -> CheckResult<&VarData> {
        self.constructors
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    fn get_class(&self, id: Ident) -> CheckResult<&ImportData<ClassData>> {
        self.classes
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    fn get_type_mut(&mut self, id: Ident) -> CheckResult<&mut ImportData<TyData>> {
        self.types
            .get_mut(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_class_data_mut(&mut self, id: Ident) -> CheckResult<&mut ClassData> {
        self.classes
            .get_mut(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))?
            .as_own_mut()
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotClass, id))
    }

    fn get_class_mut(&mut self, id: Ident) -> CheckResult<&mut ImportData<ClassData>> {
        self.classes
            .get_mut(&id.ident)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    fn insert_type(&mut self, id: Symbol, data: TyData) -> Option<ImportData<TyData>> {
        self.types.insert(id, ImportData::Own(data))
    }

    pub fn insert_val(&mut self, id: Symbol, data: VarData) -> Option<VarData> {
        self.vals.insert(id, data)
    }

    fn insert_constructor(&mut self, id: Symbol, data: VarData) -> Option<VarData> {
        self.constructors.insert(id, data)
    }

    fn insert_class(&mut self, id: Symbol, data: ClassData) -> Option<ImportData<ClassData>> {
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
    fn gen_id(&mut self) -> TyId;

    fn gen_type_var(&mut self) -> Ty {
        Ty::intern(TyKind::Var(self.gen_id()))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct IdGenerator(u32);

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
    fn gen_id(&mut self) -> TyId {
        let id = self.0;
        self.0 += 1;
        TyId::new(id)
    }
}

impl Substitute for VarData {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.ty.substitute(subs) | self.constrs.substitute(subs)
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

#[derive(Debug, Clone)]
pub struct TyData {
    params:       TyQuant,
    constructors: Vec<Constructor<Ty>>,
    span:         Span,
}

impl Default for TyData {
    fn default() -> Self {
        Self {
            params:       Ty::empty_quant(),
            constructors: Default::default(),
            span:         Default::default(),
        }
    }
}

impl TyData {
    #[must_use]
    const fn new(params: TyQuant, constructors: Vec<Constructor<Ty>>, span: Span) -> Self {
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

    fn params(&self) -> &[TyId] {
        &self.params
    }
}

#[derive(Debug, Clone)]
pub struct AliasData {
    params: TyQuant,
    ty:     Ty,
}

impl AliasData {
    #[must_use]
    pub const fn new(params: TyQuant, ty: Ty) -> Self {
        Self { params, ty }
    }

    pub fn params(&self) -> &[TyId] {
        &self.params
    }

    pub const fn ty(&self) -> &Ty {
        &self.ty
    }

    pub fn subs(&self, args: &[Ty]) -> Ty {
        let mut ty = *self.ty();
        ty.substitute(&mut |ty| {
            self.params()
                .iter()
                .copied()
                .position(|v| ty.as_var().is_some_and(|ty| ty == v))
                .map(|pos| args[pos])
        });
        ty
    }

    pub fn resolve(aliases: &mut [(Path, Self)]) {
        let mut changed = true;
        while changed {
            changed = false;
            let cloned = aliases.to_vec();
            for (alias, data) in cloned {
                let mut subs = |ty: &TyKind| match ty {
                    TyKind::Named { name, args } if name == &alias => {
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
    parents:     Box<[Path]>,
    constraints: ClassConstraintSet,
    signatures:  FxHashMap<Ident, MemberData>,
    instances:   FxHashMap<Ty, InstanceData>,
    span:        Span,
}

impl ClassData {
    pub fn new(span: Span) -> Self {
        Self {
            parents: Box::new([]),
            constraints: ClassConstraintSet::new(),
            signatures: FxHashMap::default(),
            instances: FxHashMap::default(),
            span,
        }
    }

    pub fn extend_signature(
        &mut self,
        iter: impl IntoIterator<Item = (Ident, MemberData)>,
        parents: Box<[Path]>,
        constraints: ClassConstraintSet,
    ) {
        self.signatures.extend(iter);
        self.parents = parents;
        self.constraints = constraints;
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

    pub fn parents(&self) -> &[Path] {
        &self.parents
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
    pub fixity: Fixity,
    pub prec:   u8,
    pub ty:     Ty,
    pub set:    ClassConstraintSet,
    pub span:   Span,
}

impl OperatorData {
    pub fn new<T>(fixity: Fixity, prec: u8, ty: Ty, set: T, span: Span) -> Self
    where
        ClassConstraintSet: From<T>,
    {
        Self {
            fixity,
            prec,
            ty,
            set: ClassConstraintSet::from(set),
            span,
        }
    }

    pub const fn span(&self) -> Span {
        self.span
    }

    pub const fn ty(&self) -> &Ty {
        &self.ty
    }

    pub const fn set(&self) -> &ClassConstraintSet {
        &self.set
    }

    pub const fn fixity(&self) -> Fixity {
        self.fixity
    }

    pub const fn prec(&self) -> u8 {
        self.prec
    }
}

#[derive(Debug, Default, Clone)]
pub struct Ctx {
    modules:        FxHashMap<Symbol, ModuleData>,
    env:            Vec<FxHashMap<Symbol, VarData>>,
    infix:          FxHashMap<Symbol, OperatorData>,
    prefix:         FxHashMap<Symbol, OperatorData>,
    current_module: Ident,
}

impl Ctx {
    pub const fn current_module(&self) -> Ident {
        self.current_module
    }

    pub const fn set_current_module(&mut self, module: Ident) {
        self.current_module = module;
    }

    fn get(&self, id: Ident) -> CheckResult<&VarData> {
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

    fn get_module_mut(&mut self, id: Ident) -> CheckResult<&mut ModuleData> {
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

    fn free_type_variables(&self) -> Vec<TyId> {
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

        match ty.kind() {
            TyKind::Scheme { quant, ty } => {
                quantifiers.extend_from_slice(quant);
                Ty::intern(TyKind::Scheme {
                    quant: Ty::intern_quant(quantifiers),
                    ty:    *ty,
                })
            }
            _ => Ty::intern(TyKind::Scheme {
                quant: Ty::intern_quant(quantifiers),
                ty,
            }),
        }
    }

    pub fn insert_ty(&mut self, name: Ident, params: TyQuant) -> CheckResult<()> {
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
            data.constructors.push(*ctor);
            Ok(())
        }
    }

    pub fn get_constructor(&self, id: &Path) -> CheckResult<&Ty> {
        match *id.as_slice() {
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

            _ => unreachable!(),
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

    fn get_class_mut(&mut self, name: &Path) -> CheckResult<&mut ClassData> {
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

    pub fn insert_class(&mut self, name: Symbol, data: ClassData) -> CheckResult<()> {
        self.current_mut()?.insert_class(name, data);
        Ok(())
    }

    fn get_module_and_ident(&self, path: &Path) -> CheckResult<(Ident, Ident)> {
        match *path.as_slice() {
            [id] => {
                let cur = Ident::new(self.current_module.ident, id.span);
                Ok((cur, id))
            }
            [module, id] => Ok((module, id)),
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidPath(*path),
                path.span(),
            )),
        }
    }

    pub fn resolve_type_name(&self, name: &Path) -> CheckResult<Path> {
        self.resolve_name(name, ModuleData::get_ty)
    }

    fn resolve_name<T>(
        &self,
        name: &Path,
        get: impl FnOnce(&ModuleData, Ident) -> CheckResult<&ImportData<T>>,
    ) -> CheckResult<Path> {
        let (module, ty) = self.get_module_and_ident(name)?;
        let data = self.get_from_module(module, ty, get)?;
        let module = data
            .as_import()
            .map_or(module, |id| Ident::new(id.ident, module.span));
        Ok(Path::from_two(module, ty))
    }

    pub fn resolve_class_name(&self, name: &Path) -> CheckResult<Path> {
        self.resolve_name(name, ModuleData::get_class)
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

        let path = Path::from_two(from, id);
        let span = from.span.join(id.span);

        Err(CheckError::new(CheckErrorKind::InvalidImport(path), span))
    }

    fn import(&mut self, import: Import) -> (bool, Vec<CheckError>) {
        match import.wildcard {
            ImportWildcard::Nil => match self.import_single(&import.path) {
                Ok(ok) => (ok, Vec::new()),
                Err(err) => (false, vec![err]),
            },
            ImportWildcard::Clause(clause) => {
                let [module] = *import.path.as_slice() else {
                    return (
                        false,
                        vec![CheckError::new(
                            CheckErrorKind::InvalidImport(import.path),
                            import.path.span(),
                        )],
                    );
                };
                let mut new_clause = Vec::new();
                let mut errors = Vec::new();
                for mut import in clause {
                    let mut path = vec![module];
                    path.extend(import.path.as_slice());
                    if let Some(path) = Path::from_slice(&path) {
                        import.path = path;
                        new_clause.push(import);
                    } else {
                        let span = import.path.span();
                        errors.push(CheckError::new(
                            CheckErrorKind::InvalidPath(import.path),
                            span,
                        ));
                    }
                }
                let clause = ImportClause(new_clause.into_boxed_slice());
                let (res, mut errs) = self.import_clause(clause);
                errs.extend(errors);
                (res, errs)
            }
            ImportWildcard::Wildcard => match self.import_wildcard(&import.path) {
                Ok(ok) => (ok, Vec::new()),
                Err(err) => (false, vec![err]),
            },
        }
    }

    fn import_wildcard(&mut self, path: &Path) -> CheckResult<bool> {
        if let [module] = *path.as_slice() {
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
                .map(|c| (c.name, c.ty, c.span))
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
        match *path.as_slice() {
            [module, id] => self.import_from_module(module, id),

            [module, ty, ctor] => {
                let data = self.get_data_from_module(module, ty, ModuleData::get_ty)?;
                let data = data.find_constructor(ctor)?;
                let data = VarData::new(data.ty, ClassConstraintSet::new(), path.span());
                let new = self
                    .current_mut()?
                    .insert_constructor(ctor.ident, data)
                    .is_none();
                Ok(new)
            }

            _ => Err(CheckError::new(
                CheckErrorKind::InvalidImport(*path),
                path.span(),
            )),
        }
    }

    pub fn import_prelude(&mut self) -> CheckResult<bool> {
        self.import_wildcard(&mod_path!(prelude))
    }

    fn is_super_class(&self, class: &Path, child: &Path) -> bool {
        class == child
            || self
                .get_class(child)
                .map(|child| {
                    child
                        .parents()
                        .iter()
                        .any(|parent| self.is_super_class(class, parent))
                })
                .unwrap_or(false)
    }

    fn set_contains_class(&self, set: &ClassConstraintSet, class: &ClassConstraint) -> bool {
        set.iter().any(|c| {
            c.ty() == class.ty()
                && (self.is_super_class(class.class(), c.class())
                    || self.is_super_class(c.class(), class.class()))
        })
    }

    pub fn insert_instance(
        &mut self,
        instance: Ty,
        class: &Path,
        data: InstanceData,
    ) -> CheckResult<()> {
        let constrs = if let TyKind::Scheme { ty, .. } = instance.kind() {
            self.instantiate_class(class, *ty, data.span)?
        } else {
            self.instantiate_class(class, instance, data.span)?
        };

        if let [(span, constrs)] = constrs.as_slice()
            && constrs.is_empty()
        {
            return Err(CheckError::new(
                CheckErrorKind::MultipleInstances(*class, instance, *span),
                data.span,
            ));
        }

        if let Some((span, _)) = constrs.iter().find(|(_, set)| {
            set.iter().all(|c| c.ty().is_var())
                && (data.set().is_empty()
                    || data.set().iter().any(|c| self.set_contains_class(set, c)))
        }) {
            return Err(CheckError::new(
                CheckErrorKind::MultipleInstances(*class, instance, *span),
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
            let Ok(constrs) = self.get_class(c.class()).map(|data| data.parents.clone()) else {
                continue;
            };
            self.assume_constraint_tree(c.ty(), &constrs);
            let _ = self.assume_instance(
                c.ty(),
                c.class(),
                InstanceData::new(ClassConstraintSet::new(), c.span()),
            );
        }
    }

    fn assume_constraint_tree(&mut self, ty: Ty, parents: &[Path]) {
        for c in parents {
            let Ok(constrs) = self.get_class(c).map(|data| data.parents.clone()) else {
                continue;
            };
            self.assume_constraint_tree(ty, &constrs);
            let _ = self.assume_instance(
                ty,
                c,
                InstanceData::new(ClassConstraintSet::new(), Span::default()),
            );
        }
    }

    #[must_use]
    pub fn get_constructor_subtypes(&self, ty: Ty, idx: usize) -> TySlice {
        if let TyKind::Tuple(types) = ty.kind() {
            return *types;
        }

        let TyKind::Named { name, args } = ty.kind() else {
            return Ty::empty_slice();
        };

        let mut data = self.get_ty_data(name).cloned().unwrap_or_default();

        let subs = data
            .params
            .iter()
            .copied()
            .zip(args.iter().copied())
            .map(|(ty, arg)| Subs::new(ty, arg))
            .collect::<Vec<_>>();

        let mut ctor = data.constructors.swap_remove(idx);
        ctor.params.substitute_many(&subs);

        ctor.params
    }

    pub fn write_variant_name(
        &self,
        f: &mut impl std::fmt::Write,
        ty: Ty,
        idx: usize,
    ) -> std::fmt::Result {
        let TyKind::Named { name, .. } = ty.kind() else {
            return Ok(());
        };
        let ctor = self.get_constructors_for_ty(name)[idx].name;
        write!(f, "{ctor}")
    }

    pub fn implementation(&self, ty: Ty, class: &Path) -> CheckResult<&InstanceData> {
        let class_data = self.get_class(class)?;

        let instance = if ty.is_scheme() {
            class_data
                .instances
                .iter()
                .find_map(|(&inst, data)| ty.equivalent(inst).then_some(data))
        } else {
            class_data.instances.get(&ty)
        };

        instance
            .ok_or_else(|| CheckError::new(CheckErrorKind::NotInstance(ty, *class), class.span()))
    }

    fn implementation_mut(&mut self, mut ty: Ty, class: &Path) -> CheckResult<&mut InstanceData> {
        if ty.is_scheme() {
            let class_data = self.get_class(class)?;
            let instance = class_data
                .instances
                .keys()
                .find(|&&instance| ty.equivalent(instance));
            if let Some(instance) = instance {
                ty = *instance;
            }
        }

        let class_data = self.get_class_mut(class)?;

        let instance = class_data.instances.get_mut(&ty);

        instance
            .ok_or_else(|| CheckError::new(CheckErrorKind::NotInstance(ty, *class), class.span()))
    }

    pub fn instantiate_class(
        &self,
        class: &Path,
        ty: Ty,
        span: Span,
    ) -> CheckResult<Vec<(Span, ClassConstraintSet)>> {
        let data = self.get_class(class)?;

        if let Some(data) = data.instances.get(&ty) {
            return Ok(vec![(data.span, ClassConstraintSet::new())]);
        }

        let sets = data
            .instances
            .iter()
            .filter_map(|(inst, data)| {
                inst.get_scheme_ty()?
                    .zip_args(ty)
                    .map(|args| (args, data.set().iter(), data.span))
            })
            .map(|(args, set, inst_span)| {
                let mut new = ClassConstraintSet::new();

                for (c, arg) in set
                    .zip(std::iter::repeat(args.iter()))
                    .flat_map(|(c, zip)| {
                        zip.filter_map(move |(a1, a2)| (c.ty() == *a1).then_some((c, a2)))
                    })
                {
                    for (_, c) in self.instantiate_class(c.class(), *arg, span)? {
                        new.extend(c);
                    }
                }

                Ok((inst_span, new))
            })
            .collect::<CheckResult<Vec<_>>>()?;

        if sets.is_empty() {
            Ok(vec![(
                span,
                ClassConstraintSet::from(ClassConstraint::new(*class, ty, span)),
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
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        let mut res = false;
        // We can skip the first scope
        // because you do not access type
        // variables from these binds
        // due to instantiation
        for env in &mut self.env[1..] {
            res |= env
                .values_mut()
                .map(|t| t.substitute(subs))
                .reduce(BitOr::bitor)
                .unwrap_or(false);
        }
        res
    }
}

impl Substitute for AliasData {
    fn substitute<S>(&mut self, subs: &mut S) -> bool
    where
        S: FnMut(&TyKind) -> Option<Ty>,
    {
        self.ty.substitute(subs)
    }
}

#[derive(Debug)]
struct TyVarFormatter<T>
where
    T: Iterator<Item = char>,
{
    vars:  FxHashMap<TyId, char>,
    chars: T,
}

impl<T> TyVarFormatter<T>
where
    T: Iterator<Item = char>,
{
    fn get(&mut self, var: TyId) -> char {
        *self
            .vars
            .entry(var)
            .or_insert_with(|| self.chars.next().unwrap())
    }
}

impl Ty {
    fn fmt_var<T: Iterator<Item = char>>(
        self,
        f: &mut std::fmt::Formatter<'_>,
        chars: &mut TyVarFormatter<T>,
    ) -> std::fmt::Result {
        match self.kind() {
            TyKind::Int => write!(f, "int"),
            TyKind::Bool => write!(f, "bool"),
            TyKind::Char => write!(f, "char"),
            TyKind::Real => write!(f, "real"),
            TyKind::Fn { param, ret } => {
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
            TyKind::Var(var) => {
                let c = chars.get(*var);
                write!(f, "'{c}")
            }
            TyKind::Scheme { quant, ty } => {
                for n in quant.iter() {
                    let c = chars.get(*n);
                    write!(f, "'{c} ")?;
                }
                write!(f, ". ")?;
                ty.fmt_var(f, chars)
            }
            TyKind::Named { name, args } => {
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
            TyKind::This(args) => {
                write!(f, "TyKind")?;
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
            TyKind::Generic { var, args } => {
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
            TyKind::Tuple(types) => {
                write!(f, "(")?;
                separated_fmt(f, types.iter(), ", ", |ty, f| ty.fmt_var(f, chars))?;
                write!(f, ")")?;
                Ok(())
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
            writeln!(f, "{id} =")?;
            for (id, sig) in class.signatures() {
                write!(f, "    val ")?;
                sig.set.fmt_var(f, &mut chars)?;
                write!(f, "{id} : ")?;
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
                for p in c.params.iter() {
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
            write!(f, "{id} : ")?;
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
        if self.is_empty() {
            return Ok(());
        }
        write!(f, "{{")?;
        separated_fmt(f, self.iter(), ", ", |ty, f| {
            write!(f, "{} ", ty.class().base_name())?;
            ty.ty().fmt_var(f, chars)
        })?;
        write!(f, "}} => ")
    }
}
