use std::fmt::{Debug, Display};
use std::hash::{Hash, Hasher};
use std::ops::{Deref, Range};
use std::sync::{Mutex, MutexGuard, OnceLock};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::compiler::types::{TyId, TyKind};
use crate::span::SpanData;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Span(u32);

#[derive(Clone, Copy)]
pub struct Ty(&'static TyKind);

#[derive(Clone, Copy)]
pub struct TySlice(&'static [Ty]);

#[derive(Clone, Copy)]
pub struct TyQuant(&'static [TyId]);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyPath(u32);

impl Debug for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self.0, f)
    }
}
impl Debug for TySlice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self.0, f)
    }
}
impl Debug for TyQuant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self.0, f)
    }
}

impl Deref for TySlice {
    type Target = [Ty];

    fn deref(&self) -> &'static Self::Target {
        self.0
    }
}

impl Default for TySlice {
    fn default() -> Self {
        Ty::empty_slice()
    }
}

impl Default for TyQuant {
    fn default() -> Self {
        Ty::empty_quant()
    }
}

impl Deref for TyQuant {
    type Target = [TyId];

    fn deref(&self) -> &'static Self::Target {
        self.0
    }
}

impl Hash for Ty {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0, state);
    }
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl Eq for Ty {
}

impl Hash for TySlice {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0, state);
    }
}

impl PartialEq for TySlice {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl Eq for TySlice {
}

impl Hash for TyQuant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0, state);
    }
}

impl PartialEq for TyQuant {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl Eq for TyQuant {
}

impl TyPath {
    pub fn get(self) -> &'static [Symbol] {
        Env::get(|env| env.ctx.get_name(self))
    }
}

impl Default for Span {
    fn default() -> Self {
        Self::zero()
    }
}

impl Span {
    #[must_use]
    pub const fn new(idx: u32) -> Self {
        Self(idx)
    }

    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    #[must_use]
    pub const fn zero() -> Self {
        Self(0)
    }
}

impl Default for Symbol {
    fn default() -> Self {
        Self::zero()
    }
}

impl Symbol {
    #[must_use]
    pub const fn zero() -> Self {
        Self(0)
    }

    pub fn intern(symbol: &str) -> Self {
        Env::get(|mut e| e.symbols.intern(symbol))
    }

    pub fn intern_owned(symbol: String) -> Self {
        Env::get(|mut e| e.symbols.intern_owned(symbol))
    }
}

impl Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match Env::get(|e| e.symbols.get(*self)) {
            Some(symbol) => write!(f, "{symbol:?}"),
            None => f.debug_tuple("Symbol").field(&self.0).finish(),
        }
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match Env::get(|e| e.symbols.get(*self)) {
            Some(symbol) => write!(f, "{symbol}"),
            None => write!(f, "<?{}>", self.0),
        }
    }
}

impl Debug for TyPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = Env::get(|e| e.ctx.get_name(*self));
        Debug::fmt(name, f)
    }
}

impl Display for TyPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = Env::get(|e| e.ctx.get_name(*self));
        write!(f, "{}", name.last().unwrap())
    }
}

impl Span {
    pub fn intern(span: SpanData) -> Self {
        Env::get(|mut e| e.spans.intern(span))
    }

    #[must_use]
    pub fn join(self, other: Self) -> Self {
        let (self_data, other_data) =
            Env::get(|e| (e.spans.get(self).unwrap(), e.spans.get(other).unwrap()));
        let new_data = self_data.join(&other_data);
        Self::intern(new_data)
    }

    #[must_use]
    pub fn file_id(self) -> usize {
        let data = Env::get(|e| e.spans.get(self).unwrap());
        data.file_id()
    }
}

impl From<Span> for Range<usize> {
    fn from(value: Span) -> Self {
        let data = Env::get(|e| e.spans.get(value).unwrap_or_default());
        data.start()..data.end()
    }
}

impl Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match Env::get(|e| e.spans.get(*self)) {
            Some(span) => write!(f, "{span:?}"),
            None => f.debug_tuple("Span").field(&self.0).finish(),
        }
    }
}

#[derive(Default)]
struct Env {
    symbols: SymbolInterner,
    spans:   SpanInterner,
    ctx:     GlobalCtx,
}

impl Env {
    fn get<T>(f: impl FnOnce(MutexGuard<'_, Self>) -> T) -> T {
        static GLOBAL_DATA: OnceLock<Mutex<Env>> = OnceLock::new();
        f(GLOBAL_DATA.get_or_init(Default::default).lock().unwrap())
    }
}

impl Ty {
    #[must_use]
    pub const fn new_unchecked(kind: &'static TyKind) -> Self {
        Self(kind)
    }

    #[inline]
    pub const fn kind(self) -> &'static TyKind {
        self.0
    }

    pub fn intern(ty: TyKind) -> Self {
        Env::get(|mut e| e.ctx.intern(ty))
    }

    pub fn force_insert(ty: TyKind) -> Self {
        Env::get(|mut e| e.ctx.force_insert(ty))
    }

    pub fn intern_slice(ty: Vec<Self>) -> TySlice {
        Env::get(|mut e| e.ctx.intern_slice(ty))
    }

    pub fn intern_quant(ty: Vec<TyId>) -> TyQuant {
        Env::get(|mut e| e.ctx.intern_quant(ty))
    }

    pub fn intern_path(name: Vec<Symbol>) -> TyPath {
        Env::get(|mut e| e.ctx.intern_name(name))
    }

    #[must_use]
    pub const fn int() -> Self {
        INT
    }

    #[must_use]
    pub const fn bool() -> Self {
        BOOL
    }

    #[must_use]
    pub const fn char() -> Self {
        CHAR
    }

    #[must_use]
    pub const fn real() -> Self {
        REAL
    }

    #[must_use]
    pub const fn empty_slice() -> TySlice {
        EMPTY_SLICE
    }

    #[must_use]
    pub const fn empty_quant() -> TyQuant {
        EMPTY_QUANT
    }
}

struct SymbolInterner {
    indexes: FxHashMap<&'static str, u32>,
    symbols: Vec<&'static str>,
}

macro_rules! default_symbols {
    [$($symbol:literal),+ $(,)?] => {{
        const SYMBOLS_LEN: usize = [$($symbol),+].len();
        const SYMBOLS: [&'static str; SYMBOLS_LEN] = [$($symbol),+];
        let mut indexes = FxHashMap::default();
        indexes.reserve(SYMBOLS_LEN);
        let mut i = 0usize;
        while i < SYMBOLS_LEN {
            #[allow(clippy::cast_possible_truncation)]
            indexes.insert(SYMBOLS[i], i as u32);
            i += 1;
        }
        let symbols = Vec::from(SYMBOLS);
        SymbolInterner {
            indexes,
            symbols,
        }
    }};
}

impl Default for SymbolInterner {
    fn default() -> Self {
        default_symbols![
            "", "+", "-", "/", "*", "^", "^^", "!", "==", "!=", ">", ">=", "<", "<=", "&&", "||",
            ">>", ">>=", "$", ".", "List", "Option", "Result", "Add", "Sub", "Mul", "Div", "Pow",
            "Neg", "Eq", "Cmp", "Number", "And", "Or", "Not", "Nil", "Cons", "Some", "None",
        ]
    }
}

impl SymbolInterner {
    fn get(&self, symbol: Symbol) -> Option<&'static str> {
        self.symbols.get(symbol.0 as usize).copied()
    }

    fn intern(&mut self, symbol: &str) -> Symbol {
        if let Some(idx) = self.indexes.get(symbol) {
            Symbol(*idx)
        } else {
            let symbol = Box::leak(Box::from(symbol));
            let idx = self.symbols.len().try_into().unwrap();
            self.symbols.push(symbol);
            self.indexes.insert(symbol, idx);
            Symbol(idx)
        }
    }

    fn intern_owned(&mut self, symbol: String) -> Symbol {
        if let Some(idx) = self.indexes.get(symbol.as_str()) {
            Symbol(*idx)
        } else {
            let symbol = Box::leak(symbol.into_boxed_str());
            let idx = self.symbols.len().try_into().unwrap();
            self.symbols.push(symbol);
            self.indexes.insert(symbol, idx);
            Symbol(idx)
        }
    }
}

#[derive(Default)]
struct SpanInterner {
    spans: Vec<SpanData>,
}

impl SpanInterner {
    fn get(&self, span: Span) -> Option<SpanData> {
        self.spans.get(span.index()).copied()
    }

    fn intern(&mut self, span: SpanData) -> Span {
        let idx = self.spans.len().try_into().unwrap();
        self.spans.push(span);
        Span::new(idx)
    }
}

#[derive(Default)]
struct GlobalCtx {
    types:        FxHashSet<&'static TyKind>,
    slices:       FxHashSet<&'static [Ty]>,
    quantifiers:  FxHashSet<&'static [TyId]>,
    name_indexes: FxHashMap<&'static [Symbol], u32>,
    names:        Vec<&'static [Symbol]>,
}

static INT: Ty = Ty(&TyKind::Int);
static BOOL: Ty = Ty(&TyKind::Bool);
static CHAR: Ty = Ty(&TyKind::Char);
static REAL: Ty = Ty(&TyKind::Real);
static EMPTY_SLICE: TySlice = TySlice(&[]);
static EMPTY_QUANT: TyQuant = TyQuant(&[]);

impl GlobalCtx {
    const fn try_get_primitive(ty: &TyKind) -> Option<Ty> {
        match ty {
            TyKind::Int => Some(INT),
            TyKind::Bool => Some(BOOL),
            TyKind::Char => Some(CHAR),
            TyKind::Real => Some(REAL),
            _ => None,
        }
    }

    fn force_insert(&mut self, ty: TyKind) -> Ty {
        let ty = Box::leak(Box::new(ty));
        self.types.insert(ty);
        Ty(ty)
    }

    fn intern(&mut self, ty: TyKind) -> Ty {
        if let Some(ty) = Self::try_get_primitive(&ty) {
            return ty;
        }
        if let Some(ty) = self.types.get(&ty) {
            return Ty(ty);
        }

        let ty = Box::leak(Box::new(ty));
        self.types.insert(ty);
        Ty(ty)
    }

    fn intern_slice(&mut self, ty: Vec<Ty>) -> TySlice {
        if ty.is_empty() {
            return EMPTY_SLICE;
        }

        if let Some(slice) = self.slices.get(ty.as_slice()) {
            return TySlice(slice);
        }

        let slice = Box::leak(ty.into_boxed_slice());
        self.slices.insert(slice);
        TySlice(slice)
    }

    fn intern_quant(&mut self, ty: Vec<TyId>) -> TyQuant {
        if ty.is_empty() {
            return EMPTY_QUANT;
        }

        if let Some(slice) = self.quantifiers.get(ty.as_slice()) {
            return TyQuant(slice);
        }

        let slice = Box::leak(ty.into_boxed_slice());
        self.quantifiers.insert(slice);
        TyQuant(slice)
    }

    fn intern_name(&mut self, name: Vec<Symbol>) -> TyPath {
        if let Some(idx) = self.name_indexes.get(name.as_slice()) {
            return TyPath(*idx);
        }

        let name = Box::leak(name.into_boxed_slice());
        let idx = self.names.len().try_into().unwrap();
        self.name_indexes.insert(name, idx);
        self.names.push(name);
        TyPath(idx)
    }

    fn get_name(&self, name: TyPath) -> &'static [Symbol] {
        self.names[name.0 as usize]
    }
}

macro_rules! ty_path {
    ($seg:ident) => {{
        use crate::global::{Symbol, Ty, TyPath};
        Ty::intern_path(vec![Symbol::intern(stringify!($seg))])
    }};
    ($fst:ident::$snd:ident) => {{
        use crate::global::{Symbol, Ty};
        Ty::intern_path(vec![
            Symbol::intern(stringify!($fst)),
            Symbol::intern(stringify!($snd)),
        ])
    }};
}
pub(crate) use ty_path;
