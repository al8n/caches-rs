

mod adaptive;
mod raw;
mod two_queue;

pub use raw::{
    KeysLRUIter, KeysMRUIter, LRUIter, LRUIterMut, MRUIter, MRUIterMut, RawLRU, ValuesLRUIter,
    ValuesLRUIterMut, ValuesMRUIter, ValuesMRUIterMut,
};
pub use two_queue::{DEFAULT_2Q_GHOST_RATIO, DEFAULT_2Q_RECENT_RATIO, TwoQueueCache, TwoQueueCacheBuilder};
pub use adaptive::{AdaptiveCache, AdaptiveCacheBuilder};

use crate::{DefaultEvictCallback};
use crate::lru::raw::EntryNode;
use core::mem;

/// `LRUCache` is a fixed size LRU cache.
pub type LRUCache<K, V, S> = RawLRU<K, V, DefaultEvictCallback, S>;

unsafe fn swap_value<K, V>(v: &mut V, ent: &mut EntryNode<K, V>) {
    mem::swap(v, &mut (*(*ent).val.as_mut_ptr()) as &mut V);
}