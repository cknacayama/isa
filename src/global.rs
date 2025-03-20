use std::{cell::RefCell, fmt::Display};

use crate::IndexSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(usize);

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match GLOBAL_DATA.with_borrow(|e| e.symbols.get(self)) {
            Some(symbol) => write!(f, "{symbol}"),
            None => write!(f, "<?{}>", self.0),
        }
    }
}

impl Symbol {
    pub fn concat(self, other: Self, sep: impl Display) -> Symbol {
        let symbol = format!("{self}{sep}{other}");
        intern_static_symbol(symbol.leak())
    }
}

#[derive(Debug, Default)]
struct GlobalEnv {
    symbols: SymbolEnv,
}

impl GlobalEnv {
    fn new() -> Self {
        Self::default()
    }
}

thread_local! {
    static GLOBAL_DATA: RefCell<GlobalEnv> = RefCell::new(GlobalEnv::new());
}

pub fn intern_symbol(symbol: &str) -> Symbol {
    GLOBAL_DATA.with_borrow_mut(|e| e.symbols.intern(symbol))
}

pub fn intern_static_symbol(symbol: &'static str) -> Symbol {
    GLOBAL_DATA.with_borrow_mut(|e| e.symbols.intern_static(symbol))
}

pub fn symbol_count() -> usize {
    GLOBAL_DATA.with_borrow(|e| e.symbols.len())
}

#[derive(Debug, Clone, Default)]
struct SymbolEnv {
    symbols: IndexSet<&'static str>,
}

impl SymbolEnv {
    fn get(&self, symbol: &Symbol) -> Option<&'static str> {
        self.symbols.get_index(symbol.0).copied()
    }

    fn len(&self) -> usize {
        self.symbols.len()
    }

    fn intern(&mut self, symbol: &str) -> Symbol {
        match self.symbols.get_index_of(symbol) {
            Some(idx) => Symbol(idx),
            None => {
                let symbol = Box::leak::<'static>(Box::<str>::from(symbol));
                let (idx, _) = self.symbols.insert_full(symbol);
                Symbol(idx)
            }
        }
    }

    fn intern_static(&mut self, symbol: &'static str) -> Symbol {
        let (idx, _) = self.symbols.insert_full(symbol);
        Symbol(idx)
    }
}
