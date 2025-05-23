use std::fmt::{Debug, Display};
use std::ops::{Deref, Range};
use std::sync::{LazyLock, Mutex, MutexGuard};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::compiler::types::{TyId, TyKind};
use crate::intern::{Intern, Internship};
use crate::span::SpanData;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ty(Intern<'static, TyKind>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TySlice(Intern<'static, [Ty]>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyQuant(Intern<'static, [TyId]>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyPath(Intern<'static, [Symbol]>);

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
    #[must_use]
    pub const fn interned(self) -> &'static [Symbol] {
        self.0.interned()
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

    #[must_use]
    pub fn intern(symbol: &str) -> Self {
        Env::get(|mut e| e.symbols.intern(symbol))
    }

    #[must_use]
    pub fn intern_owned(symbol: String) -> Self {
        Env::get(|mut e| e.symbols.intern_owned(symbol))
    }
}

impl Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol = Env::get(|e| e.symbols.get(*self));
        write!(f, "{symbol:?}")
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol = Env::get(|e| e.symbols.get(*self));
        write!(f, "{symbol}")
    }
}

impl Debug for TyPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Display for TyPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.last().unwrap())
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
        static GLOBAL_DATA: LazyLock<Mutex<Env>> = LazyLock::new(Default::default);
        GLOBAL_DATA.lock().map(f).unwrap()
    }
}

impl Ty {
    #[must_use]
    pub const fn new_unchecked(ty: &'static TyKind) -> Self {
        Self(Intern::new_unchecked(ty))
    }

    #[inline]
    #[must_use]
    pub const fn kind(self) -> &'static TyKind {
        self.0.interned()
    }

    #[must_use]
    pub fn intern(ty: TyKind) -> Self {
        Self(Env::get(|mut e| e.ctx.intern(ty)))
    }

    #[must_use]
    pub fn force_insert(ty: TyKind) -> Self {
        Env::get(|mut e| e.ctx.force_insert(ty))
    }

    #[must_use]
    pub fn intern_slice(ty: Vec<Self>) -> TySlice {
        TySlice(Env::get(|mut e| e.ctx.intern(ty)))
    }

    #[must_use]
    pub fn intern_quant(ty: Vec<TyId>) -> TyQuant {
        TyQuant(Env::get(|mut e| e.ctx.intern(ty)))
    }

    #[must_use]
    pub fn intern_path(name: Vec<Symbol>) -> TyPath {
        TyPath(Env::get(|mut e| e.ctx.intern(name)))
    }

    #[must_use]
    pub const fn int() -> Self {
        Self(Intern::new_unchecked(INT))
    }

    #[must_use]
    pub const fn bool() -> Self {
        Self(Intern::new_unchecked(BOOL))
    }

    #[must_use]
    pub const fn char() -> Self {
        Self(Intern::new_unchecked(CHAR))
    }

    #[must_use]
    pub const fn real() -> Self {
        Self(Intern::new_unchecked(REAL))
    }

    #[must_use]
    pub const fn empty_slice() -> TySlice {
        TySlice(Intern::new_unchecked(EMPTY_SLICE))
    }

    #[must_use]
    pub const fn empty_quant() -> TyQuant {
        TyQuant(Intern::new_unchecked(EMPTY_QUANT))
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
    fn get(&self, symbol: Symbol) -> &'static str {
        self.symbols[symbol.0 as usize]
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
    fn get(&self, span: u32) -> SpanData {
        self.spans[span as usize]
    }

    fn intern(&mut self, span: SpanData) -> Span {
        let idx = self.spans.len().try_into().unwrap();
        self.spans.push(span);
        Span::new_interned(idx)
    }
}

#[derive(Default)]
struct GlobalCtx {
    types:       FxHashSet<&'static TyKind>,
    slices:      FxHashSet<&'static [Ty]>,
    quantifiers: FxHashSet<&'static [TyId]>,
    names:       FxHashSet<&'static [Symbol]>,
}

static INT: &TyKind = &TyKind::Int;
static BOOL: &TyKind = &TyKind::Bool;
static CHAR: &TyKind = &TyKind::Char;
static REAL: &TyKind = &TyKind::Real;
static EMPTY_SLICE: &[Ty] = &[];
static EMPTY_QUANT: &[TyId] = &[];

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
        Ty(Intern::new_unchecked(ty))
    }
}

impl Internship<'static, TyKind> for GlobalCtx {
    type Insight = TyKind;

    fn intern(&mut self, ty: Self::Insight) -> Intern<'static, TyKind> {
        if let Some(ty) = Self::try_get_primitive(&ty) {
            return Intern::new_unchecked(ty);
        }
        if let Some(ty) = self.types.get(&ty) {
            return Intern::new_unchecked(ty);
        }

        let ty = Box::leak(Box::new(ty));
        self.types.insert(ty);
        Intern::new_unchecked(ty)
    }
}

impl Internship<'static, [Ty]> for GlobalCtx {
    type Insight = Vec<Ty>;

    fn intern(&mut self, slice: Self::Insight) -> Intern<'static, [Ty]> {
        if slice.is_empty() {
            return Intern::new_unchecked(EMPTY_SLICE);
        }

        self.slices.intern(slice)
    }
}

impl Internship<'static, [TyId]> for GlobalCtx {
    type Insight = Vec<TyId>;

    fn intern(&mut self, data: Self::Insight) -> Intern<'static, [TyId]> {
        if data.is_empty() {
            return Intern::new_unchecked(EMPTY_QUANT);
        }

        self.quantifiers.intern(data)
    }
}

impl Internship<'static, [Symbol]> for GlobalCtx {
    type Insight = Vec<Symbol>;

    fn intern(&mut self, data: Self::Insight) -> Intern<'static, [Symbol]> {
        self.names.intern(data)
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

#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct Span {
    lo_or_index:       u32,
    len:               u16,
    file_id_or_marker: u16,
}

#[derive(Clone, Copy)]
struct InlineSpan {
    lo:      u32,
    len:     u16,
    file_id: u16,
}

impl InlineSpan {
    const fn from_span(span: Span) -> Self {
        Self {
            lo:      span.lo_or_index,
            len:     span.len,
            file_id: span.file_id_or_marker,
        }
    }

    const fn data(self) -> SpanData {
        let lo = self.lo as usize;
        let hi = lo + self.len as usize;
        SpanData::new(self.file_id as usize, lo, hi)
    }
}

#[derive(Clone, Copy)]
struct InternSpan {
    index: u32,
}

impl InternSpan {
    const fn from_span(span: Span) -> Self {
        Self {
            index: span.lo_or_index,
        }
    }
}

macro_rules! match_span_kind {
    (
        $span:expr,
        InlineSpan($span1:ident) => $arm1:expr,
        InternSpan($span2:ident) => $arm2:expr,
    ) => {
        if $span.file_id_or_marker != INTERNED_TAG {
            let $span1 = InlineSpan::from_span($span);
            $arm1
        } else {
            let $span2 = InternSpan::from_span($span);
            $arm2
        }
    };
}

const MAX_LEN: u16 = u16::MAX;
const MAX_LO: u32 = u32::MAX;
const MAX_FILE_ID: u16 = 0b0111_1111_1111_1111;
const INTERNED_TAG: u16 = !MAX_FILE_ID;

impl Default for Span {
    fn default() -> Self {
        Self::zero()
    }
}

impl Span {
    #[must_use]
    const fn new_interned(idx: u32) -> Self {
        Self {
            lo_or_index:       idx,
            len:               0,
            file_id_or_marker: INTERNED_TAG,
        }
    }

    #[must_use]
    pub const fn zero() -> Self {
        Self {
            lo_or_index:       0,
            len:               0,
            file_id_or_marker: 0,
        }
    }

    #[must_use]
    pub fn intern(lo: usize, hi: usize, file_id: usize) -> Self {
        let len = hi - lo;
        if lo > MAX_LO as usize || file_id > MAX_FILE_ID as usize || len > MAX_LEN as usize {
            Env::get(|mut e| e.spans.intern(SpanData::new(file_id, lo, hi)))
        } else {
            #[allow(clippy::cast_possible_truncation)]
            Self {
                lo_or_index:       lo as u32,
                len:               len as u16,
                file_id_or_marker: file_id as u16,
            }
        }
    }

    #[must_use]
    pub fn join(self, other: Self) -> Self {
        // FIXME: shouldn't need to lock
        // global state twice
        let lhs = self.data();
        let rhs = other.data();

        let span = lhs.join(&rhs);
        Self::intern(span.lo(), span.hi(), span.file_id())
    }

    #[must_use]
    pub fn file_id(self) -> usize {
        match_span_kind!(self,
            InlineSpan(span) => span.file_id as usize,
            InternSpan(span) => {
                Env::get(|e| e.spans.get(span.index).file_id())
            },
        )
    }

    fn data(self) -> SpanData {
        match_span_kind!(self,
            InlineSpan(span) => span.data(),
            InternSpan(span) => {
                Env::get(|e| e.spans.get(span.index))
            },
        )
    }
}

impl From<Span> for Range<usize> {
    fn from(value: Span) -> Self {
        let data = value.data();
        data.lo()..data.hi()
    }
}

impl Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data = self.data();
        write!(f, "{data:?}")
    }
}
