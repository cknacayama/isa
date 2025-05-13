use std::cell::RefCell;
use std::fmt::Display;
use std::ops::Range;

use rustc_hash::FxHashMap;

use crate::span::SpanData;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Span(u32);

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
    pub const fn zero() -> Self {
        Self(0)
    }

    pub fn intern(symbol: &str) -> Self {
        Env::get(|e| e.symbols.intern(symbol))
    }
}

impl std::fmt::Debug for Symbol {
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

impl Span {
    pub fn intern(span: SpanData) -> Self {
        Env::get(|e| e.spans.intern(span))
    }

    #[must_use]
    pub fn join(self, other: Self) -> Self {
        let (self_data, other_data) =
            Env::get(|e| (e.spans.get(self).unwrap(), e.spans.get(other).unwrap()));
        let new_data = self_data.join(&other_data);
        Self::intern(new_data)
    }

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

impl std::fmt::Debug for Span {
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
}

impl Env {
    fn new() -> Self {
        Self::default()
    }

    fn get<T>(f: impl FnOnce(&mut Self) -> T) -> T {
        GLOBAL_DATA.with_borrow_mut(f)
    }
}

thread_local! {
    static GLOBAL_DATA: RefCell<Env> = RefCell::new(Env::new());
}

#[must_use]
pub fn intern_owned_symbol(symbol: String) -> Symbol {
    Env::get(|e| e.symbols.intern_owned(symbol))
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
