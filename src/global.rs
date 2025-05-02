use std::cell::RefCell;
use std::fmt::Display;
use std::ops::Range;

use rustc_hash::FxHashMap;

use crate::span::{Span, SpanData};

#[derive(Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct Symbol(u32);

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match GLOBAL_DATA.with_borrow(|e| e.symbols.get(*self)) {
            Some(symbol) => write!(f, "{symbol:?}"),
            None => f.debug_tuple("Symbol").field(&self.0).finish(),
        }
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match GLOBAL_DATA.with_borrow(|e| e.symbols.get(*self)) {
            Some(symbol) => write!(f, "{symbol}"),
            None => write!(f, "<?{}>", self.0),
        }
    }
}

impl Span {
    #[must_use]
    pub fn union(self, other: Self) -> Self {
        let (self_data, other_data) =
            GLOBAL_DATA.with_borrow(|e| (e.spans.get(self).unwrap(), e.spans.get(other).unwrap()));
        let new_data = self_data.union(&other_data);
        intern_span(new_data)
    }

    pub fn file_id(self) -> usize {
        let data = GLOBAL_DATA.with_borrow(|e| e.spans.get(self).unwrap());
        data.file_id()
    }
}

impl From<Span> for Range<usize> {
    fn from(value: Span) -> Self {
        let data = GLOBAL_DATA.with_borrow(|e| e.spans.get(value).unwrap_or_default());
        data.start()..data.end()
    }
}

#[derive(Debug, Default)]
struct GlobalEnv {
    symbols: SymbolInterner,
    spans:   SpanInterner,
}

impl GlobalEnv {
    fn new() -> Self {
        Self::default()
    }
}

thread_local! {
    static GLOBAL_DATA: RefCell<GlobalEnv> = RefCell::new(GlobalEnv::new());
}

macro_rules! symbol {
    ($sym:expr) => {
        crate::global::intern_symbol($sym)
    };
}
macro_rules! owned_symbol {
    ($sym:expr) => {
        crate::global::intern_owned_symbol($sym)
    };
}
pub(crate) use {owned_symbol, symbol};

#[must_use]
pub fn intern_symbol(symbol: &str) -> Symbol {
    GLOBAL_DATA.with_borrow_mut(|e| e.symbols.intern(symbol))
}

#[must_use]
pub fn intern_owned_symbol(symbol: String) -> Symbol {
    GLOBAL_DATA.with_borrow_mut(|e| e.symbols.intern_owned(symbol))
}

#[must_use]
pub fn intern_span(span: SpanData) -> Span {
    GLOBAL_DATA.with_borrow_mut(|e| e.spans.intern(span))
}

#[derive(Debug, Clone)]
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
            "", "+", "-", "/", "*", "^", "^^", "!", "==", "!=", ">", ">=", "<", "<=", ">>", ">>=",
            "$", ".", "List", "Option", "Result", "Add", "Sub", "Mul", "Div", "Pow", "Neg", "Eq",
            "Cmp", "Number", "And", "Or", "Not", "Nil", "Cons", "Some", "None",
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

#[derive(Debug, Clone, Default)]
struct SpanInterner {
    spans: Vec<SpanData>,
}

impl SpanInterner {
    fn get(&self, span: Span) -> Option<SpanData> {
        self.spans.get(span.index()).copied()
    }

    fn intern(&mut self, span: SpanData) -> Span {
        let idx = self.spans.len();
        self.spans.push(span);
        Span::new(idx)
    }
}
