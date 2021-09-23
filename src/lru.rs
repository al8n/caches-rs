//! LRU based caches implementation.
//!
//! This is a Rust implementation for [HashiCorp's golang-lru](https://github.com/hashicorp/golang-lru).
//!
//! This crate contains three LRU based cache, [`LRUCache`], [`TwoQueueCache`] and [`AdaptiveCache`].
//!
//! See [Introduction](#introduction), [Trade-Off](#trade-off) and [Usages](#usages) for more details.
//! </div>
//!
//! ## Introduction
//! The MSRV for this crate is 1.55.0.
//!
//! LRU based caches are `O(1)` for read, write and delete.
//!
//! - [`LRUCache`] or [`RawLRU`] is a fixed size LRU cache.
//!
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
//! - [**`AdaptiveCache`**](#adaptivecache-adaptive-replacement-cache)
//! - [**`TwoQueueCache`**](#twoqueuecache)
//!
//! ### RawLRU and LRUCache
//! [`RawLRU`] is the basic data structure over the crate, it has a generic type [`E: OnEvictCallback`], which support users to write and apply their own callback policy.
//!
//! [`LRUCache`] is a type alias for `RawLRU<K, V, DefaultOnEvictCallback, S>`, so it does not support custom the `on_evict` callback.
//!
//! #### Default No-op Callback
//! Use [`RawLRU`] with default noop callback.
//!
//!   ```rust
//!   use caches::{RawLRU, PutResult};
//!
//!   fn main() {
//!       let mut cache = RawLRU::new(2).unwrap();
//!       // fill the cache
//!       assert_eq!(cache.put(1, 1), PutResult::Put);
//!       assert_eq!(cache.put(2, 2), PutResult::Put);
//!
//!       // put 3, should evict the entry (1, 1)
//!       assert_eq!(cache.put(3, 3), PutResult::Evicted {key: 1,value: 1});
//!
//!       // put 4, should evict the entry (2, 2)
//!       assert_eq!(cache.put(4, 4), PutResult::Evicted {key: 2,value: 2});
//!
//!       // get 3, should update the recent-ness
//!       assert_eq!(cache.get(&3), Some(&3));
//!
//!       // put 5, should evict the entry (4, 4)
//!       assert_eq!(cache.put(5, 5), PutResult::Evicted {key: 4,value: 4});
//!   }
//!   ```
//!
//! #### Custom Callback
//! Use [`RawLRU`] with a custom callback.
//!
//!   ```rust
//!   use std::sync::Arc;
//!   use std::sync::atomic::{AtomicU64, Ordering};
//!   use caches::{OnEvictCallback, RawLRU, PutResult};
//!
//!   // EvictedCounter is a callback which is used to record the number of evicted entries.
//!   struct EvictedCounter {
//!       ctr: Arc<AtomicU64>,
//!   }
//!
//!   impl EvictedCounter {
//!       pub fn new(ctr: Arc<AtomicU64>) -> Self {
//!           Self {
//!               ctr,
//!           }
//!       }
//!   }
//!
//!   impl OnEvictCallback for EvictedCounter {
//!       fn on_evict<K, V>(&self, _: &K, _: &V) {
//!           self.ctr.fetch_add(1, Ordering::SeqCst);
//!       }
//!   }
//!
//!   fn main() {
//!       let counter = Arc::new(AtomicU64::new(0));
//!
//!       let mut cache: RawLRU<u64, u64, EvictedCounter> = RawLRU::with_on_evict_cb(2, EvictedCounter::new(counter.clone())).unwrap();
//!
//!       // fill the cache
//!       assert_eq!(cache.put(1, 1), PutResult::Put);
//!       assert_eq!(cache.put(2, 2), PutResult::Put);
//!
//!       // put 3, should evict the entry (1, 1)
//!       assert_eq!(cache.put(3, 3), PutResult::Evicted {key: 1,value: 1});
//!
//!       // put 4, should evict the entry (2, 2)
//!       assert_eq!(cache.put(4, 4), PutResult::Evicted {key: 2,value: 2});
//!
//!       // get 3, should update the recent-ness
//!       assert_eq!(cache.get(&3), Some(&3));
//!
//!       // put 5, should evict the entry (4, 4)
//!       assert_eq!(cache.put(5, 5), PutResult::Evicted {key: 4,value: 4});
//!
//!       assert_eq!(counter.load(Ordering::SeqCst), 3);
//!   }
//!   ```
//!
//! ### [`AdaptiveCache`] (Adaptive Replacement Cache)
//! More methods and examples, please see [`AdaptiveCache`].
//!
//! ```rust
//! use caches::AdaptiveCache;
//!
//! fn main() {
//!     let mut cache = AdaptiveCache::new(4).unwrap();
//!
//!     // fill recent
//!     (0..4).for_each(|i| cache.put(i, i));
//!
//!     // move to frequent
//!     cache.get(&0);
//!     cache.get(&1);
//!     assert_eq!(cache.frequent_len(), 2);
//!
//!     // evict from recent
//!     cache.put(4, 4);
//!     assert_eq!(cache.recent_evict_len(), 1);
//!
//!     // current state
//!     // recent:          (MRU) [4, 3] (LRU)
//!     // frequent:        (MRU) [1, 0] (LRU)
//!     // recent evict:    (MRU) [2] (LRU)
//!     // frequent evict:  (MRU) [] (LRU)
//!
//!     // Add 2, should cause hit on recent_evict
//!     cache.put(2, 2);
//!     assert_eq!(cache.recent_evict_len(), 1);
//!     assert_eq!(cache.partition(), 1);
//!     assert_eq!(cache.frequent_len(), 3);
//!
//!     // Current state
//!     // recent LRU:      (MRU) [4] (LRU)
//!     // frequent LRU:    (MRU) [2, 1, 0] (LRU)
//!     // recent evict:    (MRU) [3] (LRU)
//!     // frequent evict:  (MRU) [] (LRU)
//!
//!     // Add 4, should migrate to frequent
//!     cache.put(4, 4);
//!     assert_eq!(cache.recent_len(), 0);
//!     assert_eq!(cache.frequent_len(), 4);
//!
//!     // Current state
//!     // recent LRU:      (MRU) [] (LRU)
//!     // frequent LRU:    (MRU) [4, 2, 1, 0] (LRU)
//!     // recent evict:    (MRU) [3] (LRU)
//!     // frequent evict:  (MRU) [] (LRU)
//!
//!     // Add 5, should evict to b2
//!     cache.put(5, 5);
//!     assert_eq!(cache.recent_len(), 1);
//!     assert_eq!(cache.frequent_len(), 3);
//!     assert_eq!(cache.frequent_evict_len(), 1);
//!
//!     // Current state
//!     // recent:          (MRU) [5] (LRU)
//!     // frequent:        (MRU) [4, 2, 1] (LRU)
//!     // recent evict:    (MRU) [3] (LRU)
//!     // frequent evict:  (MRU) [0] (LRU)
//!
//!     // Add 0, should decrease p
//!     cache.put(0, 0);
//!     assert_eq!(cache.recent_len(), 0);
//!     assert_eq!(cache.frequent_len(), 4);
//!     assert_eq!(cache.recent_evict_len(), 2);
//!     assert_eq!(cache.frequent_evict_len(), 0);
//!     assert_eq!(cache.partition(), 0);
//!
//!     // Current state
//!     // recent:         (MRU) [] (LRU)
//!     // frequent:       (MRU) [0, 4, 2, 1] (LRU)
//!     // recent evict:   (MRU) [5, 3] (LRU)
//!     // frequent evict: (MRU) [0] (LRU)
//! }
//! ```
//!
//! ### [`TwoQueueCache`]
//! More methods and examples, please see [`TwoQueueCache`].
//!
//! ```rust
//! use caches::{TwoQueueCache, PutResult};
//!
//! fn main() {
//!     let mut cache = TwoQueueCache::new(4).unwrap();
//!
//!     // Add 1,2,3,4,
//!     (1..=4).for_each(|i| { assert_eq!(cache.put(i, i), PutResult::Put);});
//!
//!     // Add 5 -> Evict 1 to ghost LRU
//!     assert_eq!(cache.put(5, 5), PutResult::Put);
//!
//!     // Pull in the recently evicted
//!     assert_eq!(cache.put(1, 1), PutResult::Update(1));
//!
//!     // Add 6, should cause another recent evict
//!     assert_eq!(cache.put(6, 6), PutResult::<i32, i32>::Put);
//!
//!     // Add 7, should evict an entry from ghost LRU.
//!     assert_eq!(cache.put(7, 7), PutResult::Evicted { key: 2, value: 2 });
//!
//!     // Add 2, should evict an entry from ghost LRU
//!     assert_eq!(cache.put(2, 11), PutResult::Evicted { key: 3, value: 3 });
//!
//!     // Add 4, should put the entry from ghost LRU to freq LRU
//!     assert_eq!(cache.put(4, 11), PutResult::Update(4));
//!
//!     // move all entry in recent to freq.
//!     assert_eq!(cache.put(2, 22), PutResult::Update(11));
//!     assert_eq!(cache.put(7, 77), PutResult::<i32, i32>::Update(7));
//!
//!     // Add 6, should put the entry from ghost LRU to freq LRU, and evicted one
//!     // entry
//!     assert_eq!(cache.put(6, 66), PutResult::EvictedAndUpdate { evicted: (5, 5), update: 6});
//!     assert_eq!(cache.recent_len(), 0);
//!     assert_eq!(cache.ghost_len(), 1);
//!     assert_eq!(cache.frequent_len(), 4);
//! }
//! ```
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
//! [`Rc`]: https://doc.rust-lang.org/std/rc/struct.Rc.html
//! [`Box`]: https://doc.rust-lang.org/std/boxed/struct.Box.html
//! [`mem::swap`]: https://doc.rust-lang.org/stable/std/mem/fn.swap.html
//! [`std::collections`]: https://doc.rust-lang.org/stable/std/collections/
//! [`E: OnEvictCallback`]: trait.OnEvictCallback.html
//! [`RawLRU`]: struct.RawLRU.html
//! [`LRUCache`]: type.LRUCache.html
//! [`TwoQueueCache`]: struct.TwoQueueCache.html
//! [`AdaptiveCache`]: struct.AdaptiveCache.html
mod adaptive;
mod raw;
mod segmented;
mod two_queue;

pub use adaptive::{AdaptiveCache, AdaptiveCacheBuilder};
pub use raw::{
    KeysLRUIter, KeysMRUIter, LRUIter, LRUIterMut, MRUIter, MRUIterMut, RawLRU, ValuesLRUIter,
    ValuesLRUIterMut, ValuesMRUIter, ValuesMRUIterMut,
};
pub use two_queue::{
    TwoQueueCache, TwoQueueCacheBuilder, DEFAULT_2Q_GHOST_RATIO, DEFAULT_2Q_RECENT_RATIO,
};

use crate::lru::raw::EntryNode;
use crate::DefaultEvictCallback;
use core::mem;

/// `LRUCache` is a fixed size LRU cache.
pub type LRUCache<K, V, S> = RawLRU<K, V, DefaultEvictCallback, S>;

unsafe fn swap_value<K, V>(v: &mut V, ent: &mut EntryNode<K, V>) {
    mem::swap(v, &mut (*(*ent).val.as_mut_ptr()) as &mut V);
}
