use std::fmt::Display;
use std::rc::Rc;
use std::{fmt, vec};

use rustc_hash::{FxHashMap, FxHashSet};
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
    types:        FxHashMap<Symbol, TyData>,
    constructors: FxHashMap<Symbol, VarData>,
    classes:      FxHashMap<Symbol, ClassDataImport>,
}

impl ModuleData {
    pub fn get_type(&self, id: Ident) -> CheckResult<&TyData> {
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

    fn get_class(&self, id: Ident) -> CheckResult<&ClassDataImport> {
        self.classes
            .get(&id.ident)
            .ok_or_else(|| CheckError::from_ident(CheckErrorKind::Unbound, id))
    }

    pub fn get_type_mut(&mut self, id: Ident) -> CheckResult<&mut TyData> {
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
                    .as_class_mut()
                    .ok_or_else(|| CheckError::from_ident(CheckErrorKind::NotClass, id))
            })
    }

    fn get_class_mut(&mut self, id: Ident) -> CheckResult<&mut ClassDataImport> {
        self.classes
            .get_mut(&id.ident)
            .ok_or_else(|| CheckError::new(CheckErrorKind::Unbound(id.ident), id.span))
    }

    pub fn insert_type(&mut self, id: Symbol, data: TyData) -> Option<TyData> {
        self.types.insert(id, data)
    }

    pub fn insert_val(&mut self, id: Symbol, data: VarData) -> Option<VarData> {
        self.vals.insert(id, data)
    }

    pub fn insert_constructor(&mut self, id: Symbol, data: VarData) -> Option<VarData> {
        self.constructors.insert(id, data)
    }

    pub fn insert_class(&mut self, id: Symbol, data: ClassData) -> Option<ClassDataImport> {
        self.classes.insert(id, ClassDataImport::Class(data))
    }

    pub fn insert_class_import(&mut self, id: Symbol, data: Ident) -> Option<ClassDataImport> {
        self.classes.insert(id, ClassDataImport::Import(data))
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
    constructors: Vec<Constructor<Ty>>,
    imported:     Option<Ident>,
    span:         Span,
}

impl TyData {
    #[must_use]
    const fn new(params: Rc<[u64]>, constructors: Vec<Constructor<Ty>>, span: Span) -> Self {
        Self {
            params,
            constructors,
            imported: None,
            span,
        }
    }

    fn with_import(self, module: Ident) -> Self {
        Self {
            imported: Some(module),
            ..self
        }
    }

    fn constructors(&self) -> &[Constructor<Ty>] {
        &self.constructors
    }

    fn find_constructor(&self, ctor: Ident) -> CheckResult<&Constructor<Ty>> {
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
pub enum ClassDataImport {
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
    const fn is_class(&self) -> bool {
        matches!(self, Self::Class(..))
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
    current_module: Ident,
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

    pub fn current_scope(&self) -> Option<&FxHashMap<Symbol, VarData>> {
        self.env.last()
    }

    pub fn pop_scope(&mut self) -> Option<FxHashMap<Symbol, VarData>> {
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

    pub fn insert_ty(&mut self, name: Ident, params: Rc<[u64]>) -> CheckResult<()> {
        let module = self.current_mut()?;

        if let Some(prev) =
            module.insert_type(name.ident, TyData::new(params, Vec::new(), name.span))
        {
            Err(CheckError::new(
                CheckErrorKind::SameNameType(name.ident, prev.span),
                name.span,
            ))
        } else {
            Ok(())
        }
    }

    pub fn insert_constructor_for_ty(
        &mut self,
        name: Ident,
        ctor: &Constructor<Ty>,
    ) -> CheckResult<()> {
        let module = self.current_mut()?;

        let data = module.get_type_mut(name)?;

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
                let current = self.current()?;
                let data = current.get_type(ty)?;

                data.find_constructor(id).map(|c| &c.ty)
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
    pub fn get_constructors_for_ty(&self, name: &Path) -> &[Constructor<Ty>] {
        self.get_ty(name)
            .map_or(&[], |data| data.constructors.as_slice())
    }

    pub fn get_type_arity(&self, name: &Path) -> CheckResult<usize> {
        self.get_ty(name).map(|data| data.params.len())
    }

    pub fn insert_class(&mut self, name: Symbol, data: ClassData) -> CheckResult<()> {
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

    pub fn resolve_type_name(&self, name: &Path) -> CheckResult<Path> {
        let (module, ty) = self.get_module_and_ident(name)?;
        let data = self.get_ty(name)?;
        if let Some(import) = data.imported {
            Ok(Path::new(smallvec![import, ty]))
        } else {
            Ok(Path::new(smallvec![module, ty]))
        }
    }

    pub fn same_type_name(&self, lhs: &Path, rhs: &Path) -> CheckResult<bool> {
        let (lhs_module, lhs_ty) = self.get_module_and_ident(lhs)?;
        let (rhs_module, rhs_ty) = self.get_module_and_ident(rhs)?;

        if lhs_ty != rhs_ty {
            return Ok(false);
        }

        println!("{lhs}");
        println!("{rhs}");

        if lhs_module == rhs_module {
            return Ok(true);
        }

        let lhs = self.get_ty(lhs)?;
        let rhs = self.get_ty(rhs)?;

        let lhs = lhs.imported.unwrap_or(lhs_module);
        let rhs = rhs.imported.unwrap_or(rhs_module);

        Ok(lhs == rhs)
    }

    fn import_from_module(&mut self, from: Ident, id: Ident) -> CheckResult<()> {
        let module_data = self.get_module(from)?;

        if let Ok(data) = module_data.get_type(id).cloned() {
            if data.imported.is_some() {
                self.current_mut()?.insert_type(id.ident, data);
            } else {
                self.current_mut()?
                    .insert_type(id.ident, data.with_import(from));
            }
            return Ok(());
        }
        if let Ok(data) = module_data.get_class(id).cloned() {
            if let ClassDataImport::Import(data) = data {
                self.current_mut()?.insert_class_import(id.ident, data);
            } else {
                self.current_mut()?.insert_class_import(id.ident, from);
            }
            return Ok(());
        }
        if let Ok(data) = module_data.get_val(id).cloned() {
            self.current_mut()?.insert_val(id.ident, data);
            return Ok(());
        }

        let path = Path {
            segments: smallvec![from, id],
        };
        let span = from.span.union(id.span);

        Err(CheckError::new(CheckErrorKind::InvalidImport(path), span))
    }

    fn import(&mut self, import: Import) -> CheckResult<()> {
        match import.wildcard {
            ImportWildcard::Nil => self.import_single(&import.path),
            ImportWildcard::Clause(clause) => {
                let [module] = *import.path.segments.as_slice() else {
                    return Err(CheckError::new(
                        CheckErrorKind::InvalidImport(import.path.clone()),
                        import.path.span(),
                    ));
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
            ImportWildcard::Wildcard => self.import_wildcard(&import.path),
        }
    }

    fn import_wildcard(&mut self, path: &Path) -> CheckResult<()> {
        match *path.segments.as_slice() {
            [module] => {
                let module_data = self.get_module(module)?;

                let classes = module_data
                    .classes
                    .iter()
                    .map(|(&id, data)| match *data {
                        ClassDataImport::Import(ident) => (id, ClassDataImport::Import(ident)),
                        ClassDataImport::Class(_) => (id, ClassDataImport::Import(module)),
                    })
                    .collect::<Vec<_>>();
                let types = module_data
                    .types
                    .iter()
                    .map(|(&id, data)| {
                        let data = TyData {
                            imported: data.imported.or(Some(module)),
                            ..data.clone()
                        };
                        (id, data)
                    })
                    .collect::<Vec<_>>();
                let vals = module_data.vals.clone();
                let constructors = module_data.constructors.clone();

                let module = self.current_mut()?;

                module.vals.extend(vals);
                module.types.extend(types);
                module.classes.extend(classes);
                module.constructors.extend(constructors);

                Ok(())
            }
            [module, ty] => {
                let module_data = self.get_module(module)?;
                let ty_data = module_data.get_type(ty)?;
                let constructors: Vec<_> = ty_data
                    .constructors
                    .iter()
                    .map(|c| (c.name, c.ty.clone(), c.span))
                    .collect();

                let cur = self.current_mut()?;
                for (ctor, ty, span) in constructors {
                    cur.insert_constructor(
                        ctor.ident,
                        VarData::new(ty, ClassConstraintSet::new(), span),
                    );
                }

                Ok(())
            }
            _ => Err(CheckError::new(
                CheckErrorKind::InvalidImport(path.clone()),
                path.span(),
            )),
        }
    }

    pub fn import_clause(&mut self, import_clause: ImportClause) -> CheckResult<()> {
        let mut res = Ok(());
        for import in import_clause {
            res = self.import(import).and(res);
        }
        res
    }

    fn import_single(&mut self, path: &Path) -> CheckResult<()> {
        match *path.segments.as_slice() {
            [module, id] => self.import_from_module(module, id),

            [module, ty, ctor] => {
                let module_data = self.get_module(module)?;
                let data = module_data.get_type(ty).and_then(|ty| match ty.imported {
                    Some(_) => Err(CheckError::new(
                        CheckErrorKind::InvalidImport(path.clone()),
                        path.span(),
                    )),
                    None => Ok(ty),
                })?;
                let data = data.find_constructor(ctor)?;
                let data = VarData::new(data.ty.clone(), ClassConstraintSet::new(), path.span());
                self.current_mut()?.insert_constructor(ctor.ident, data);
                Ok(())
            }

            _ => Err(CheckError::new(
                CheckErrorKind::InvalidImport(path.clone()),
                path.span(),
            )),
        }
    }

    pub fn import_prelude(&mut self) -> CheckResult<()> {
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
                n1 == n2
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
            .reduce(|mut new, constr| {
                new.extend(constr);
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
