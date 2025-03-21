#![forbid(unsafe_code)]
#![deny(clippy::enum_glob_use, clippy::pedantic, clippy::nursery)]
#![allow(clippy::missing_const_for_fn, reason = "false positive")]
#![allow(
    clippy::missing_errors_doc,
    reason = "Only returns Result with custom Error types"
)]

pub mod cli;
pub mod compiler;
pub mod global;
pub mod report;
pub mod span;

use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

pub type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasherDefault<FxHasher>>;
pub type IndexSet<V> = indexmap::IndexSet<V, BuildHasherDefault<FxHasher>>;
pub type IndexEntry<'a, K, V> = indexmap::map::Entry<'a, K, V>;
pub type IndexOccupiedEntry<'a, K, V> = indexmap::map::OccupiedEntry<'a, K, V>;
