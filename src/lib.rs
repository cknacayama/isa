pub mod cli;
pub(crate) mod compiler;
pub(crate) mod global;
pub(crate) mod report;
pub(crate) mod span;

use std::hash::BuildHasherDefault;

use rustc_hash::FxHasher;

pub type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasherDefault<FxHasher>>;
pub type IndexSet<V> = indexmap::IndexSet<V, BuildHasherDefault<FxHasher>>;
pub type IndexEntry<'a, K, V> = indexmap::map::Entry<'a, K, V>;
pub type IndexOccupiedEntry<'a, K, V> = indexmap::map::OccupiedEntry<'a, K, V>;
