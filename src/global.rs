use std::cell::RefCell;
use std::fmt::Display;
use std::ops::Range;

use crate::IndexSet;
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
pub(crate) use symbol;

#[must_use]
pub fn intern_symbol(symbol: &str) -> Symbol {
    GLOBAL_DATA.with_borrow_mut(|e| e.symbols.intern(symbol))
}

#[must_use]
pub fn intern_span(span: SpanData) -> Span {
    GLOBAL_DATA.with_borrow_mut(|e| e.spans.intern(span))
}

#[derive(Debug, Clone)]
struct SymbolInterner {
    symbols: IndexSet<&'static str>,
}

impl Default for SymbolInterner {
    fn default() -> Self {
        let mut symbols = IndexSet::default();
        symbols.insert_full("");
        Self { symbols }
    }
}

impl SymbolInterner {
    fn get(&self, symbol: Symbol) -> Option<&'static str> {
        self.symbols.get_index(symbol.0 as usize).copied()
    }

    fn intern(&mut self, symbol: &str) -> Symbol {
        if let Some(idx) = self.symbols.get_index_of(symbol) {
            Symbol(idx.try_into().unwrap())
        } else {
            let symbol = Box::leak(Box::from(symbol));
            let (idx, _) = self.symbols.insert_full(symbol);
            Symbol(idx.try_into().unwrap())
        }
    }
}

#[derive(Debug, Clone, Default)]
struct SpanInterner {
    spans: IndexSet<SpanData>,
}

impl SpanInterner {
    fn get(&self, span: Span) -> Option<SpanData> {
        self.spans.get_index(span.index()).copied()
    }

    fn intern(&mut self, span: SpanData) -> Span {
        let (idx, _) = self.spans.insert_full(span);
        Span::new(idx)
    }
}
