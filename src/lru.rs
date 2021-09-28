//! LRU based caches implementation.
//!
//! This module contains four LRU based caches, [`LRUCache`], [`SegmentedCache`] , [`TwoQueueCache`] and [`AdaptiveCache`].
//!
//! See [Introduction](#introduction), [Trade-Off](#trade-off) and [Usages](#usages) for more details.
//!
//! ## Introduction
//!
//! LRU based caches are `O(1)` for read, write and delete.
//!
//! - [`LRUCache`] or [`RawLRU`] is a fixed size LRU cache.
//!
//! - [`SegmentedCache`] is a fixed size Segmented LRU cache.
//!
//! - [`AdaptiveCache`] is a fixed size Adaptive Replacement Cache (ARC).
//! ARC is an enhancement over the standard LRU cache in that tracks both
//! frequency and recency of use. This avoids a burst in access to new
//! entries from evicting the frequently used older entries.
//!
//!
//! - [`TwoQueueCache`] is a fixed size 2Q cache. 2Q is an enhancement
//! over the standard LRU cache in that it tracks both frequently
//! and recently used entries separately.
//!
//! ## Trade-Off
//! In theory, [`AdaptiveCache`] and [`TwoQueueCache`] add some additional
//! tracking overhead to a [`LRUCache`] cache, computationally it is roughly **2x** the cost,
//! and the extra memory overhead is linear with the size of the cache.
//! [`AdaptiveCache`] and [`TwoQueueCache`] have similar computationally cost,
//! which has been patented by IBM, but the [`TwoQueueCache`] (2Q) need to set reasonable parameters.
//!
//! However, the implementation for the [`RawLRU`] uses [`Box`] and a
//! raw pointer for each entry to break the limitation of the
//! Rust language (It does not use [`Rc`], because [`Rc`] is slower).
//! Thus, in practice, [`TwoQueueCache`] is **2.5x** computationally
//! slower than [`LRUCache`] and [`AdaptiveCache`] is **3x** computationally slower than [`LRUCache`],
//! because [`TwoQueueCache`] and [`AdaptiveCache`] has to do more box and re-box
//! than [`LRUCache`], even though I try my best to avoid boxing and re-boxing and
//! use [`mem::swap`] to avoid memory allocating and deallocating.
//!
//! [`SegmentedCache`] is computationally **1.2-1.5x** slower to [`LRUCache`] if you set the configurations reasonable, .
//! 20% of the total size for probationary segment, and 80% of the total size for protected segment may suitable for most of situations.
//!
//! Hence, it is better to understand what is the situation is
//! (your project wants a cache with a higher hit ratio or faster computationally performance),
//! and then choose the reasonable Cache in your project.
//!
//! (For more performance details, you can clone the project and
//! run `cargo bench`. The source code for benchmark is in the
//! [benches](https://github.com/al8n/caches/tree/main/benches),
//! I am also looking forward to anyone's help for writing more
//! reasonable test cases for benchmark).
//!
//! ## Usages
//! - [**`RawLRU`** and **`LRUCache`**](#rawlru-and-lrucache)
//!     - [Default](#default-no-op-callback)
//!     - [Custom OnEvictCallback](#custom-callback)
//! - [**`SegmentedCache`**](#segmentedcache)
//! - [**`AdaptiveCache`**](#adaptivecache-adaptive-replacement-cache)
//! - [**`TwoQueueCache`**](#twoqueuecache)
//!
//! ### RawLRU and LRUCache
//! [`RawLRU`] is the basic data structure over the crate, it has a generic type [`E: OnEvictCallback`], which support users to write and apply their own callback policy.
//!
//! [`LRUCache`] is a type alias for `RawLRU<K, V, DefaultOnEvictCallback, S>`, so it does not support custom the `on_evict` callback.
//!
//! #### Default No-op Callback
//! Use [`LRUCache`] with default noop callback.
//! For basic usage, see [`LRUCacheExample`].
//!
//! #### Custom Callback
//! Use [`RawLRU`] with a custom callback.
//! For basic usage, see [`RawLRUCallbackExample`].
//! More methods and examples, please see [`RawLRU`].
//!
//! ### [`SegmentedCache`]
//! For basic usage, see [`SegmentedCacheExample`]. More methods and examples, please see [`SegmentedCache`].
//!
//! ### [`AdaptiveCache`] (Adaptive Replacement Cache)
//! For basic usage, see [`AdaptiveCacheExample`]. More methods and examples, please see [`AdaptiveCache`].
//!
//!
//! ### [`TwoQueueCache`]
//! For basic usage, see [`TwoQueueCacheExample`]. More methods and examples, please see [`TwoQueueCache`].
//!
//!
//! ## Acknowledgments
//! - The implementation of `RawLRU` is highly inspired by
//! [Jerome Froelich's LRU implementation](https://github.com/jeromefroe/lru-rs)
//! and [`std::collections`] library of Rust.
//!
//! - Thanks for [HashiCorp's golang-lru](https://github.com/hashicorp/golang-lru)
//! providing the amazing Go implementation.
//!
//! - Ramakrishna's paper: [Caching strategies to improve disk system performance]
//!
//! [Caching strategies to improve disk system performance]: https://dl.acm.org/doi/10.1109/2.268884
//! [`Rc`]: https://doc.rust-lang.org/std/rc/struct.Rc.html
//! [`Box`]: https://doc.rust-lang.org/std/boxed/struct.Box.html
//! [`mem::swap`]: https://doc.rust-lang.org/stable/std/mem/fn.swap.html
//! [`std::collections`]: https://doc.rust-lang.org/stable/std/collections/
//! [`E: OnEvictCallback`]: trait.OnEvictCallback.html
//! [`RawLRU`]: struct.RawLRU.html
//! [`RawLRUCallbackExample`]: https://github.com/al8n/caches-rs/blob/main/examples/raw_lru_custom_callback.rs
//! [`SegmentedCache`]: struct.SegmentedCache.html
//! [`SegmentedCacheExample`]: https://github.com/al8n/caches-rs/blob/main/examples/segmented_cache.rs
//! [`LRUCache`]: type.LRUCache.html
//! [`LRUCacheExample`]: https://github.com/al8n/caches-rs/blob/main/examples/lru_cache.rs
//! [`TwoQueueCache`]: struct.TwoQueueCache.html
//! [`TwoQueueCacheExample`]: https://github.com/al8n/caches-rs/blob/main/examples/two_queue_cache.rs
//! [`AdaptiveCache`]: struct.AdaptiveCache.html
//! [`AdaptiveCacheExample`]: https://github.com/al8n/caches-rs/blob/main/examples/adaptive_cache.rs
mod adaptive;
mod error;
mod raw;
mod segmented;
mod two_queue;

pub use adaptive::{AdaptiveCache, AdaptiveCacheBuilder};
pub use error::CacheError;
pub use raw::{
    KeysLRUIter, KeysMRUIter, LRUIter, LRUIterMut, MRUIter, MRUIterMut, RawLRU, ValuesLRUIter,
    ValuesLRUIterMut, ValuesMRUIter, ValuesMRUIterMut,
};
pub use segmented::{SegmentedCache, SegmentedCacheBuilder};
pub use two_queue::{
    TwoQueueCache, TwoQueueCacheBuilder, DEFAULT_2Q_GHOST_RATIO, DEFAULT_2Q_RECENT_RATIO,
};

use crate::lru::raw::EntryNode;
use crate::DefaultEvictCallback;
use alloc::boxed::Box;
use core::hash::Hash;
use core::mem;

/// `LRUCache` is a fixed size LRU cache.
pub type LRUCache<K, V, S> = RawLRU<K, V, DefaultEvictCallback, S>;

unsafe fn swap_value<K, V>(v: &mut V, ent: &mut EntryNode<K, V>) {
    mem::swap(v, &mut (*(*ent).val.as_mut_ptr()) as &mut V);
}

fn debox<K: Hash + Eq, V>(bks: &mut Box<EntryNode<K, V>>) -> *mut EntryNode<K, V> {
    let ent_ptr: *mut EntryNode<K, V> = &mut **bks;
    ent_ptr
}
