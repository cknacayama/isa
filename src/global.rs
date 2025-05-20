use std::fmt::{Debug, Display};
use std::ops::{Deref, Range};
use std::sync::{Mutex, MutexGuard, OnceLock};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::compiler::types::{TyId, TyKind};
use crate::intern::{IdxInterner, Interned, InternedIdx, Interner};
use crate::span::SpanData;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Span(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ty(Interned<'static, TyKind>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TySlice(Interned<'static, [Ty]>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyQuant(Interned<'static, [TyId]>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyPath(InternedIdx<'static, u32, [Symbol]>);

impl Debug for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}
impl Debug for TySlice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}
impl Debug for TyQuant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Deref for TySlice {
    type Target = [Ty];

    fn deref(&self) -> &'static Self::Target {
        self.0.interned()
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
        self.0.interned()
    }
}

impl TyPath {
    pub fn get(self) -> &'static [Symbol] {
        Env::get(|env| env.ctx.get(self.0))
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
        let name = Env::get(|e| e.ctx.get(self.0));
        Debug::fmt(name, f)
    }
}

impl Display for TyPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = Env::get(|e| e.ctx.get(self.0));
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
    pub const fn new_unchecked(ty: &'static TyKind) -> Self {
        Ty(Interned::new_unchecked(ty))
    }

    #[inline]
    pub const fn kind(self) -> &'static TyKind {
        self.0.interned()
    }

    pub fn intern(ty: TyKind) -> Self {
        Env::get(|mut e| Self(e.ctx.intern(ty)))
    }

    pub fn force_insert(ty: TyKind) -> Self {
        Env::get(|mut e| e.ctx.force_insert(ty))
    }

    pub fn intern_slice(ty: Vec<Self>) -> TySlice {
        Env::get(|mut e| TySlice(e.ctx.intern(ty)))
    }

    pub fn intern_quant(ty: Vec<TyId>) -> TyQuant {
        Env::get(|mut e| TyQuant(e.ctx.intern(ty)))
    }

    pub fn intern_path(name: Vec<Symbol>) -> TyPath {
        Env::get(|mut e| TyPath(e.ctx.intern_idx(name)))
    }

    #[must_use]
    pub const fn int() -> Self {
        Ty(Interned::new_unchecked(INT))
    }

    #[must_use]
    pub const fn bool() -> Self {
        Ty(Interned::new_unchecked(BOOL))
    }

    #[must_use]
    pub const fn char() -> Self {
        Ty(Interned::new_unchecked(CHAR))
    }

    #[must_use]
    pub const fn real() -> Self {
        Ty(Interned::new_unchecked(REAL))
    }

    #[must_use]
    pub const fn empty_slice() -> TySlice {
        TySlice(Interned::new_unchecked(EMPTY_SLICE))
    }

    #[must_use]
    pub const fn empty_quant() -> TyQuant {
        TyQuant(Interned::new_unchecked(EMPTY_QUANT))
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

static INT: &'static TyKind = &TyKind::Int;
static BOOL: &'static TyKind = &TyKind::Bool;
static CHAR: &'static TyKind = &TyKind::Char;
static REAL: &'static TyKind = &TyKind::Real;
static EMPTY_SLICE: &'static [Ty] = &[];
static EMPTY_QUANT: &'static [TyId] = &[];

impl GlobalCtx {
    const fn try_get_primitive(ty: &TyKind) -> Option<&'static TyKind> {
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
        Ty(Interned::new_unchecked(ty))
    }
}

impl Interner<'static, TyKind> for GlobalCtx {
    type Data = TyKind;

    fn intern(&mut self, ty: Self::Data) -> Interned<'static, TyKind> {
        if let Some(ty) = Self::try_get_primitive(&ty) {
            return Interned::new_unchecked(ty);
        }
        if let Some(ty) = self.types.get(&ty) {
            return Interned::new_unchecked(ty);
        }

        let ty = Box::leak(Box::new(ty));
        self.types.insert(ty);
        Interned::new_unchecked(ty)
    }
}

impl Interner<'static, [Ty]> for GlobalCtx {
    type Data = Vec<Ty>;

    fn intern(&mut self, slice: Self::Data) -> Interned<'static, [Ty]> {
        if slice.is_empty() {
            return Interned::new_unchecked(EMPTY_SLICE);
        }

        if let Some(slice) = self.slices.get(slice.as_slice()) {
            return Interned::new_unchecked(*slice);
        }

        let slice = Box::leak(slice.into_boxed_slice());
        self.slices.insert(slice);
        Interned::new_unchecked(slice)
    }
}

impl Interner<'static, [TyId]> for GlobalCtx {
    type Data = Vec<TyId>;

    fn intern(&mut self, data: Self::Data) -> Interned<'static, [TyId]> {
        if data.is_empty() {
            return Interned::new_unchecked(EMPTY_QUANT);
        }

        if let Some(slice) = self.quantifiers.get(data.as_slice()) {
            return Interned::new_unchecked(slice);
        }

        let slice = Box::leak(data.into_boxed_slice());
        self.quantifiers.insert(slice);
        Interned::new_unchecked(slice)
    }
}

impl IdxInterner<'static, u32, [Symbol]> for GlobalCtx {
    type Data = Vec<Symbol>;

    fn intern_idx(&mut self, data: Self::Data) -> InternedIdx<'static, u32, [Symbol]> {
        if let Some(idx) = self.name_indexes.get(data.as_slice()) {
            return InternedIdx::new_unchecked(*idx);
        }

        let name = Box::leak(data.into_boxed_slice());
        let idx = self.names.len().try_into().unwrap();
        self.name_indexes.insert(name, idx);
        self.names.push(name);
        InternedIdx::new_unchecked(idx)
    }

    fn get(&self, idx: InternedIdx<'static, u32, [Symbol]>) -> &'static [Symbol] {
        self.names[idx.index() as usize]
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
