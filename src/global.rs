use std::cell::RefCell;
use std::fmt::Display;

use crate::IndexSet;
use crate::index::IndexVec;
use crate::span::{Span, SpanData};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(usize);

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match GLOBAL_DATA.with_borrow(|e| e.symbols.get(*self)) {
            Some(symbol) => write!(f, "{symbol}"),
            None => write!(f, "<?{}>", self.0),
        }
    }
}

impl Symbol {
    #[must_use]
    pub fn concat(self, other: Self, sep: impl Display) -> Self {
        let symbol = format!("{self}{sep}{other}");
        intern_static_symbol(symbol.leak())
    }
}

impl Span {
    #[must_use] pub fn union(self, other: Self) -> Self {
        let (self_data, other_data) =
            GLOBAL_DATA.with_borrow(|e| (e.spans.get(self), e.spans.get(other)));
        let new_data = self_data.union(&other_data);
        intern_span(new_data)
    }
}

impl ariadne::Span for Span {
    type SourceId = ();

    fn source(&self) -> &Self::SourceId {
        &()
    }

    fn start(&self) -> usize {
        let data = GLOBAL_DATA.with_borrow(|e| e.spans.get(*self));
        data.start()
    }

    fn end(&self) -> usize {
        let data = GLOBAL_DATA.with_borrow(|e| e.spans.get(*self));
        data.end()
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

#[must_use]
pub fn intern_symbol(symbol: &str) -> Symbol {
    GLOBAL_DATA.with_borrow_mut(|e| e.symbols.intern(symbol))
}

#[must_use]
pub fn intern_span(span: SpanData) -> Span {
    GLOBAL_DATA.with_borrow_mut(|e| e.spans.intern(span))
}

#[must_use]
fn intern_static_symbol(symbol: &'static str) -> Symbol {
    GLOBAL_DATA.with_borrow_mut(|e| e.symbols.intern_static(symbol))
}

#[must_use]
pub fn symbol_count() -> usize {
    GLOBAL_DATA.with_borrow(|e| e.symbols.len())
}

#[derive(Debug, Clone, Default)]
struct SymbolInterner {
    symbols: IndexSet<&'static str>,
}

impl SymbolInterner {
    fn get(&self, symbol: Symbol) -> Option<&'static str> {
        self.symbols.get_index(symbol.0).copied()
    }

    fn len(&self) -> usize {
        self.symbols.len()
    }

    fn intern(&mut self, symbol: &str) -> Symbol {
        if let Some(idx) = self.symbols.get_index_of(symbol) {
            Symbol(idx)
        } else {
            let symbol = Box::leak::<'static>(Box::<str>::from(symbol));
            let (idx, _) = self.symbols.insert_full(symbol);
            Symbol(idx)
        }
    }

    fn intern_static(&mut self, symbol: &'static str) -> Symbol {
        let (idx, _) = self.symbols.insert_full(symbol);
        Symbol(idx)
    }
}

#[derive(Debug, Clone, Default)]
struct SpanInterner {
    spans: IndexVec<Span, SpanData>,
}

impl SpanInterner {
    fn get(&self, span: Span) -> SpanData {
        self.spans[span]
    }

    fn intern(&mut self, span: SpanData) -> Span {
        self.spans.push(span)
    }
}
