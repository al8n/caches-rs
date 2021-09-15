use crate::{RawLRU, DefaultEvictCallback};
use core::hash::BuildHasher;

/// `LRUCache` is a fixed size LRU cache.
pub type LRUCache<K, V, S> = RawLRU<K, V, DefaultEvictCallback, S>;

