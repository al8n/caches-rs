use crate::{DefaultEvictCallback, RawLRU};

/// `LRUCache` is a fixed size LRU cache.
pub type LRUCache<K, V, S> = RawLRU<K, V, DefaultEvictCallback, S>;
