// The code in this file is modified based on [Jerome Froelich's LRU implementation](https://github.com/jeromefroe/lru-rs).
//
// MIT License
//
// Copyright (c) 2021 Al Liu (https://github.com/al8n/caches)
//
// Copyright (c) 2016 Jerome Froelich (https://github.com/jeromefroe/lru-rs)
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
use alloc::borrow::Borrow;
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
use alloc::vec::Vec;
use core::fmt;
use core::hash::{BuildHasher, Hash};
use core::iter::{FromIterator, FusedIterator};
use core::marker::PhantomData;
use core::mem;
use core::ptr;
use core::usize;

use crate::cache_api::ResizableCache;
use crate::lru::CacheError;
use crate::{
    import_hashbrown, import_std, Cache, DefaultEvictCallback, DefaultHashBuilder, KeyRef,
    OnEvictCallback, PutResult,
};

import_hashbrown!(HashSet, HashMap);
import_std!(HashSet, HashMap);

// Struct used to hold a key value pair. Also contains references to previous and next entries
// so we can maintain the entries in a linked list ordered by their use.
pub(crate) struct EntryNode<K, V> {
    pub(crate) key: mem::MaybeUninit<K>,
    pub(crate) val: mem::MaybeUninit<V>,
    prev: *mut EntryNode<K, V>,
    next: *mut EntryNode<K, V>,
}

impl<K, V> EntryNode<K, V> {
    pub(crate) fn new(key: K, val: V) -> Self {
        EntryNode {
            key: mem::MaybeUninit::new(key),
            val: mem::MaybeUninit::new(val),
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        }
    }

    fn new_sigil() -> Self {
        EntryNode {
            key: mem::MaybeUninit::uninit(),
            val: mem::MaybeUninit::uninit(),
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        }
    }
}

fn check_size(size: usize) -> Result<(), CacheError> {
    if size == 0 {
        Err(CacheError::InvalidSize(0))
    } else {
        Ok(())
    }
}

/// A fixed size RawLRU Cache
///
/// # Example
/// - Use [`RawLRU`] with default noop callback.
/// ```rust
/// use caches::{RawLRU, PutResult, Cache};
///
/// let mut cache = RawLRU::new(2).unwrap();
/// // fill the cache
/// assert_eq!(cache.put(1, 1), PutResult::Put);
/// assert_eq!(cache.put(2, 2), PutResult::Put);
///
/// // put 3, should evict the entry (1, 1)
/// assert_eq!(cache.put(3, 3), PutResult::Evicted {key: 1,value: 1});
///
/// // put 4, should evict the entry (2, 2)
/// assert_eq!(cache.put(4, 4), PutResult::Evicted {key: 2,value: 2});
///
/// // get 3, should update the recent-ness
/// assert_eq!(cache.get(&3), Some(&3));
///
/// // put 5, should evict the entry (4, 4)
/// assert_eq!(cache.put(5, 5), PutResult::Evicted {key: 4,value: 4});
/// ```
///
/// - Use [`RawLRU`] with a custom callback.
/// ```rust
/// use std::sync::Arc;
/// use std::sync::atomic::{AtomicU64, Ordering};
/// use caches::{OnEvictCallback, RawLRU, PutResult, Cache};
///
/// // EvictedCounter is a callback which is used to record the number of evicted entries.
/// struct EvictedCounter {
///     ctr: Arc<AtomicU64>,
/// }
///
/// impl EvictedCounter {
///     pub fn new(ctr: Arc<AtomicU64>) -> Self {
///         Self {
///             ctr,
///         }
///     }
/// }
///
/// impl OnEvictCallback for EvictedCounter {
///     fn on_evict<K, V>(&self, _: &K, _: &V) {
///         self.ctr.fetch_add(1, Ordering::SeqCst);
///     }
/// }
///
/// let counter = Arc::new(AtomicU64::new(0));
///
/// let mut cache: RawLRU<u64, u64, EvictedCounter> = RawLRU::with_on_evict_cb(2, EvictedCounter::new(counter.clone())).unwrap();
///
/// // fill the cache
/// assert_eq!(cache.put(1, 1), PutResult::Put);
/// assert_eq!(cache.put(2, 2), PutResult::Put);
///
/// // put 3, should evict the entry (1, 1)
/// assert_eq!(cache.put(3, 3), PutResult::Evicted {key: 1,value: 1});
///
/// // put 4, should evict the entry (2, 2)
/// assert_eq!(cache.put(4, 4), PutResult::Evicted {key: 2,value: 2});
///
/// // get 3, should update the recent-ness
/// assert_eq!(cache.get(&3), Some(&3));
///
/// // put 5, should evict the entry (4, 4)
/// assert_eq!(cache.put(5, 5), PutResult::Evicted {key: 4,value: 4});
///
/// assert_eq!(counter.load(Ordering::SeqCst), 3);
/// ```
pub struct RawLRU<K, V, E = DefaultEvictCallback, S = DefaultHashBuilder> {
    pub(crate) map: HashMap<KeyRef<K>, Box<EntryNode<K, V>>, S>,
    cap: usize,
    on_evict: Option<E>,

    // head and tail are sigil nodes to faciliate inserting entries
    head: *mut EntryNode<K, V>,
    tail: *mut EntryNode<K, V>,
}

impl<K: Hash + Eq, V> RawLRU<K, V> {
    /// Creates a new LRU Cache that holds at most `cap` items.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache: RawLRU<isize, &str> = RawLRU::new(10).unwrap();
    /// ```
    pub fn new(cap: usize) -> Result<Self, CacheError> {
        check_size(cap).map(|_| {
            Self::construct(
                cap,
                HashMap::with_capacity_and_hasher(cap, DefaultHashBuilder::default()),
                None,
            )
        })
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> RawLRU<K, V, DefaultEvictCallback, S> {
    /// Creates a new LRU Cache that holds at most `cap` items and
    /// uses the provided hash builder to hash keys.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{RawLRU, DefaultHashBuilder};
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut cache: RawLRU<isize, &str> = RawLRU::with_hasher(10, s).unwrap();
    /// ```
    pub fn with_hasher(cap: usize, hash_builder: S) -> Result<Self, CacheError> {
        check_size(cap).map(|_| {
            Self::construct(
                cap,
                HashMap::with_capacity_and_hasher(cap, hash_builder),
                None,
            )
        })
    }
}

impl<K: Hash + Eq, V, E: OnEvictCallback> RawLRU<K, V, E, DefaultHashBuilder> {
    /// Creates a new LRU Cache that holds at most `cap` items and
    /// uses the provided evict callback.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{RawLRU, OnEvictCallback};
    /// use std::sync::atomic::{AtomicU64, Ordering};
    ///
    /// struct EvictedCounter {
    ///     ctr: AtomicU64,
    /// }
    ///
    /// impl Default for EvictedCounter {
    ///     fn default() -> Self {
    ///         Self {
    ///             ctr: AtomicU64::new(0),
    ///         }
    ///     }
    /// }
    ///
    /// impl OnEvictCallback for EvictedCounter {
    ///     fn on_evict<K, V>(&self, _: &K, _: &V) {
    ///         self.ctr.fetch_add(1, Ordering::SeqCst);
    ///     }
    /// }
    ///
    /// let mut cache: RawLRU<isize, &str, EvictedCounter> = RawLRU::with_on_evict_cb(10, EvictedCounter::default()).unwrap();
    /// ```
    pub fn with_on_evict_cb(cap: usize, cb: E) -> Result<Self, CacheError> {
        check_size(cap).map(|_| {
            Self::construct(
                cap,
                HashMap::with_capacity_and_hasher(cap, DefaultHashBuilder::default()),
                Some(cb),
            )
        })
    }
}

impl<K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> Cache<K, V> for RawLRU<K, V, E, S> {
    /// Puts a key-value pair into cache, returns a [`PutResult`].
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{RawLRU, PutResult, Cache};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// assert_eq!(PutResult::Put, cache.put(1, "a"));
    /// assert_eq!(PutResult::Put, cache.put(2, "b"));
    /// assert_eq!(PutResult::Update("b"), cache.put(2, "beta"));
    /// assert_eq!(PutResult::Evicted{ key: 1, value: "a"}, cache.put(3, "c"));
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"beta"));
    /// ```
    ///
    /// [`PutResult`]: struct.PutResult.html
    fn put(&mut self, k: K, mut v: V) -> PutResult<K, V> {
        let node_ptr = self.map.get_mut(&KeyRef { k: &k }).map(|node| {
            let node_ptr: *mut EntryNode<K, V> = &mut **node;
            node_ptr
        });

        match node_ptr {
            Some(node_ptr) => {
                self.update(&mut v, node_ptr);
                PutResult::Update(v)
            }
            None => self.put_in(k, v),
        }
    }

    /// Returns a reference to the value of the key in the cache or `None` if it is not
    /// present in the cache. Moves the key to the head of the LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(2, "c");
    /// cache.put(3, "d");
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"c"));
    /// assert_eq!(cache.get(&3), Some(&"d"));
    /// ```
    fn get<'a, Q>(&'_ mut self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(node) = self.map.get_mut(k) {
            let node_ptr: *mut EntryNode<K, V> = &mut **node;

            self.detach(node_ptr);
            self.attach(node_ptr);

            Some(unsafe { &(*(*node_ptr).val.as_ptr()) as &V })
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Moves the key to the head of the LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get_mut(&"apple"), None);
    /// assert_eq!(cache.get_mut(&"banana"), Some(&mut 6));
    /// assert_eq!(cache.get_mut(&"pear"), Some(&mut 2));
    /// ```
    fn get_mut<'a, Q>(&'_ mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(node) = self.map.get_mut(k) {
            let node_ptr: *mut EntryNode<K, V> = &mut **node;

            self.detach(node_ptr);
            self.attach(node_ptr);

            Some(unsafe { &mut (*(*node_ptr).val.as_mut_ptr()) as &mut V })
        } else {
            None
        }
    }

    /// Returns a reference to the value corresponding to the key in the cache or `None` if it is
    /// not present in the cache. Unlike `get`, `peek` does not update the LRU list so the key's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek(&1), Some(&"a"));
    /// assert_eq!(cache.peek(&2), Some(&"b"));
    /// ```
    fn peek<'a, Q>(&'_ self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map
            .get(k)
            .map(|node| unsafe { &(*(*node).val.as_ptr()) as &V })
    }

    /// Returns a mutable reference to the value corresponding to the key in the cache or `None`
    /// if it is not present in the cache. Unlike `get_mut`, `peek_mut` does not update the LRU
    /// list so the key's position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.peek_mut(&2), Some(&mut "b"));
    /// ```
    fn peek_mut<'a, Q>(&'_ mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.map.get_mut(k) {
            None => None,
            Some(node) => Some(unsafe { &mut (*(*node).val.as_mut_ptr()) as &mut V }),
        }
    }

    /// Returns a bool indicating whether the given key is in the cache. Does not update the
    /// LRU list.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    ///
    /// assert!(!cache.contains(&1));
    /// assert!(cache.contains(&2));
    /// assert!(cache.contains(&3));
    /// ```
    #[inline]
    fn contains<Q>(&self, k: &Q) -> bool
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.contains_key(k)
    }

    /// Removes and returns the value corresponding to the key from the cache or
    /// `None` if it does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(2, "a");
    ///
    /// assert_eq!(cache.remove(&1), None);
    /// assert_eq!(cache.remove(&2), Some("a"));
    /// assert_eq!(cache.remove(&2), None);
    /// assert_eq!(cache.len(), 0);
    /// ```
    fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.map.remove(k) {
            None => None,
            Some(mut old_node) => {
                let node_ptr: *mut EntryNode<K, V> = &mut *old_node;
                self.detach(node_ptr);
                unsafe {
                    let val = old_node.val.assume_init();
                    self.cb(&*old_node.key.as_ptr(), &val);
                    ptr::drop_in_place(old_node.key.as_mut_ptr());
                    Some(val)
                }
            }
        }
    }

    /// Clears the contents of the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache: RawLRU<isize, &str> = RawLRU::new(2).unwrap();
    /// assert_eq!(cache.len(), 0);
    ///
    /// cache.put(1, "a");
    /// assert_eq!(cache.len(), 1);
    ///
    /// cache.put(2, "b");
    /// assert_eq!(cache.len(), 2);
    ///
    /// cache.purge();
    /// assert_eq!(cache.len(), 0);
    /// ```
    fn purge(&mut self) {
        while self.remove_lru().is_some() {}
    }

    /// Returns the number of key-value pairs that are currently in the the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    /// assert_eq!(cache.len(), 0);
    ///
    /// cache.put(1, "a");
    /// assert_eq!(cache.len(), 1);
    ///
    /// cache.put(2, "b");
    /// assert_eq!(cache.len(), 2);
    ///
    /// cache.put(3, "c");
    /// assert_eq!(cache.len(), 2);
    /// ```
    fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns the maximum number of key-value pairs the cache can hold.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache: RawLRU<isize, &str> = RawLRU::new(2).unwrap();
    /// assert_eq!(cache.cap(), 2);
    /// ```
    fn cap(&self) -> usize {
        self.cap
    }

    /// Returns a bool indicating whether the cache is empty or not.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    /// assert!(cache.is_empty());
    ///
    /// cache.put(1, "a");
    /// assert!(!cache.is_empty());
    /// ```
    #[inline]
    fn is_empty(&self) -> bool {
        self.map.len() == 0
    }
}

impl<K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> ResizableCache for RawLRU<K, V, E, S> {
    /// Resizes the cache. If the new capacity is smaller than the size of the current
    /// cache any entries past the new capacity are discarded.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU, ResizableCache};
    /// let mut cache: RawLRU<isize, &str> = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.resize(4);
    /// cache.put(3, "c");
    /// cache.put(4, "d");
    ///
    /// assert_eq!(cache.len(), 4);
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    /// assert_eq!(cache.get(&4), Some(&"d"));
    /// ```
    fn resize(&mut self, cap: usize) -> u64 {
        let mut evicted = 0u64;
        // return early if capacity doesn't change
        if cap == self.cap {
            return evicted;
        }

        while self.map.len() > cap {
            self.remove_lru();
            evicted += 1;
        }
        self.map.shrink_to_fit();

        self.cap = cap;
        evicted
    }
}

impl<K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> RawLRU<K, V, E, S> {
    /// Creates a new LRU Cache that holds at most `cap` items and
    /// uses the provided evict callback and the provided hash builder to hash keys.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{RawLRU, OnEvictCallback, DefaultHashBuilder};
    /// use std::sync::atomic::{AtomicU64, Ordering};
    ///
    /// struct EvictedCounter {
    ///     ctr: AtomicU64,
    /// }
    ///
    /// impl Default for EvictedCounter {
    ///     fn default() -> Self {
    ///         Self {
    ///             ctr: AtomicU64::new(0),
    ///         }
    ///     }
    /// }
    ///
    /// impl OnEvictCallback for EvictedCounter {
    ///     fn on_evict<K, V>(&self, _: &K, _: &V) {
    ///         self.ctr.fetch_add(1, Ordering::SeqCst);
    ///     }
    /// }
    ///
    /// let cache: RawLRU<isize, &str, EvictedCounter, DefaultHashBuilder> = RawLRU::with_on_evict_cb_and_hasher(10, EvictedCounter::default(), DefaultHashBuilder::default()).unwrap();
    /// ```
    pub fn with_on_evict_cb_and_hasher(cap: usize, cb: E, hasher: S) -> Result<Self, CacheError> {
        check_size(cap).map(|_| {
            Self::construct(
                cap,
                HashMap::with_capacity_and_hasher(cap, hasher),
                Some(cb),
            )
        })
    }

    /// Creates a new LRU Cache with the given capacity.
    fn construct(
        cap: usize,
        map: HashMap<KeyRef<K>, Box<EntryNode<K, V>>, S>,
        cb: Option<E>,
    ) -> Self {
        // NB: The compiler warns that cache does not need to be marked as mutable if we
        // declare it as such since we only mutate it inside the unsafe block.
        let cache = Self {
            map,
            cap,
            on_evict: cb,
            head: Box::into_raw(Box::new(EntryNode::new_sigil())),
            tail: Box::into_raw(Box::new(EntryNode::new_sigil())),
        };

        unsafe {
            (*cache.head).next = cache.tail;
            (*cache.tail).prev = cache.head;
        }

        cache
    }

    /// Returns the least recent used entry(&K, &V) in the cache or `None` if the cache is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get_lru(), Some((&"banana", &6)));
    /// ```
    pub fn get_lru(&mut self) -> Option<(&K, &V)> {
        if self.is_empty() {
            return None;
        }

        unsafe {
            let node = (*self.tail).prev;
            self.detach(node);
            self.attach(node);

            let val = &(*(*node).val.as_ptr()) as &V;
            let key = &(*(*node).key.as_ptr()) as &K;
            Some((key, val))
        }
    }

    /// Returns the most recent used entry(&K, &V) in the cache or `None` if the cache is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get_mru(), Some((&"pear", &2)));
    /// ```
    pub fn get_mru(&self) -> Option<(&K, &V)> {
        if self.is_empty() {
            return None;
        }

        unsafe {
            let node = (*self.head).next;

            let val = &(*(*node).val.as_ptr()) as &V;
            let key = &(*(*node).key.as_ptr()) as &K;
            Some((key, val))
        }
    }

    /// Returns the least recent used entry(&K, &mut V) in the cache or `None` if the cache is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get_lru_mut(), Some((&"banana", &mut 6)));
    /// ```
    pub fn get_lru_mut(&mut self) -> Option<(&K, &mut V)> {
        if self.is_empty() {
            return None;
        }

        unsafe {
            let node = (*self.tail).prev;
            self.detach(node);
            self.attach(node);
            let key = &(*(*node).key.as_ptr()) as &K;
            let val = &mut (*(*node).val.as_mut_ptr()) as &mut V;
            Some((key, val))
        }
    }

    /// Returns the most recent used entry (&K, &mut V) in the cache or `None` if the cache is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get_mru_mut(), Some((&"pear", &mut 2)));
    /// ```
    pub fn get_mru_mut(&mut self) -> Option<(&K, &mut V)> {
        if self.is_empty() {
            return None;
        }

        unsafe {
            let node = (*self.head).next;
            let key = &(*(*node).key.as_ptr()) as &K;
            let val = &mut (*(*node).val.as_mut_ptr()) as &mut V;
            Some((key, val))
        }
    }

    /// `peek_or_put` peeks if a key is in the cache without updating the
    /// recent-ness or deleting it for being stale, and if not, adds the value.
    /// Returns whether found and whether a [`PutResult`].
    ///
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{RawLRU, PutResult, Cache};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    ///
    /// assert_eq!(cache.peek_or_put(2, "B"), (Some(&"b"), None));
    /// assert_eq!(cache.peek_or_put(1, "A"), (None, Some(PutResult::Evicted { key: 2, value: "b",})));
    /// ```
    ///
    /// [`PutResult`]: struct.PutResult.html
    pub fn peek_or_put(&mut self, k: K, v: V) -> (Option<&V>, Option<PutResult<K, V>>) {
        match self.map.get(&KeyRef { k: &k }) {
            None => (None, Some(self.put_in(k, v))),
            Some(ent) => unsafe { (Some(&*(**ent).val.as_ptr() as &V), None) },
        }
    }

    /// `peek_mut_or_put` peeks if a key is in the cache without updating the
    /// recent-ness or deleting it for being stale, and if not, adds the value.
    /// Returns whether found and whether a [`PutResult`].
    ///
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{RawLRU, PutResult, Cache};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    ///
    /// assert_eq!(cache.peek_mut_or_put(2, "B"), (Some(&mut "b"), None));
    /// assert_eq!(cache.peek_mut_or_put(1, "A"), (None, Some(PutResult::Evicted { key: 2, value: "b",})));
    /// ```
    ///
    /// [`PutResult`]: struct.PutResult.html
    pub fn peek_mut_or_put(&mut self, k: K, v: V) -> (Option<&mut V>, Option<PutResult<K, V>>) {
        let k_ref = KeyRef { k: &k };
        match self.map.get_mut(&k_ref) {
            None => (None, Some(self.put_in(k, v))),
            Some(v) => unsafe { (Some(&mut *(&mut **v).val.as_mut_ptr() as &mut V), None) },
        }
    }

    /// Returns the value corresponding to the least recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_lru` does not update the LRU list so the item's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_lru(), Some((&1, &"a")));
    /// ```
    pub fn peek_lru(&self) -> Option<(&K, &V)> {
        if self.is_empty() {
            return None;
        }

        let (key, val);
        unsafe {
            let node = (*self.tail).prev;
            key = &(*(*node).key.as_ptr()) as &K;
            val = &(*(*node).val.as_ptr()) as &V;
        }

        Some((key, val))
    }

    /// Returns the value corresponding to the least recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_lru` does not update the LRU list so the item's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_lru_mut(), Some((&1, &mut "a")));
    /// ```
    pub fn peek_lru_mut<'a>(&'_ mut self) -> Option<(&'a K, &'a mut V)> {
        if self.is_empty() {
            return None;
        }

        let (key, val);
        unsafe {
            let node = (*self.tail).prev;
            key = &(*(*node).key.as_ptr()) as &K;
            val = &mut (*(*node).val.as_mut_ptr()) as &mut V;
        }

        Some((key, val))
    }

    /// Returns the value corresponding to the most recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_lru` does not update the LRU list so the item's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_mru(), Some((&2, &"b")));
    /// ```
    pub fn peek_mru(&self) -> Option<(&K, &V)> {
        if self.is_empty() {
            return None;
        }

        let (key, val);
        unsafe {
            let node = (*self.head).next;
            key = &(*(*node).key.as_ptr()) as &K;
            val = &(*(*node).val.as_ptr()) as &V;
        }

        Some((key, val))
    }

    /// Returns the mutable value corresponding to the most recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_lru` does not update the LRU list so the item's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_mru_mut(), Some((&2, &mut "b")));
    /// ```
    pub fn peek_mru_mut(&mut self) -> Option<(&K, &mut V)> {
        if self.is_empty() {
            return None;
        }

        let (key, val);
        unsafe {
            let node = (*self.head).next;
            key = &(*(*node).key.as_ptr()) as &K;
            val = &mut (*(*node).val.as_mut_ptr()) as &mut V;
        }

        Some((key, val))
    }

    /// `contains_or_put` checks if a key is in the cache without updating the
    /// recent-ness or deleting it for being stale, and if not, adds the value.
    /// Returns whether found and whether a [`PutResult`].
    ///
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{RawLRU, PutResult, Cache};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    ///
    /// assert_eq!(cache.contains_or_put(2, "B"), (true, None));
    /// assert_eq!(cache.contains_or_put(1, "A"), (false, Some(PutResult::Evicted { key: 2, value: "b",})));
    /// ```
    ///
    /// [`PutResult`]: struct.PutResult.html
    pub fn contains_or_put(&mut self, k: K, v: V) -> (bool, Option<PutResult<K, V>>) {
        if !self.map.contains_key(&KeyRef { k: &k }) {
            (false, Some(self.put_in(k, v)))
        } else {
            (true, None)
        }
    }

    /// Removes and returns the key and value corresponding to the least recently
    /// used item or `None` if the cache is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    /// let mut cache = RawLRU::new(2).unwrap();
    ///
    /// cache.put(2, "a");
    /// cache.put(3, "b");
    /// cache.put(4, "c");
    /// cache.get(&3);
    ///
    /// assert_eq!(cache.remove_lru(), Some((4, "c")));
    /// assert_eq!(cache.remove_lru(), Some((3, "b")));
    /// assert_eq!(cache.remove_lru(), None);
    /// assert_eq!(cache.len(), 0);
    /// ```
    pub fn remove_lru(&mut self) -> Option<(K, V)> {
        let node = self.remove_lru_in()?;
        // N.B.: Can't destructure directly because of https://github.com/rust-lang/rust/issues/28536
        let node = *node;
        let EntryNode { key, val, .. } = node;
        unsafe {
            let key = key.assume_init();
            let val = val.assume_init();
            self.cb(&key, &val);
            Some((key, val))
        }
    }

    /// An iterator visiting all keys in most-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.keys() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn keys(&self) -> KeysMRUIter<'_, K, V> {
        KeysMRUIter { inner: self.iter() }
    }

    /// An iterator visiting all keys in less-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.keys_lru() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn keys_lru(&self) -> KeysLRUIter<'_, K, V> {
        KeysLRUIter {
            inner: self.iter_lru(),
        }
    }

    /// An iterator visiting all values in most-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.values() {
    ///     println!("val: {}",  val);
    /// }
    /// ```
    pub fn values(&self) -> ValuesMRUIter<'_, K, V> {
        ValuesMRUIter { inner: self.iter() }
    }

    /// An iterator visiting all values in less-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.values_lru() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn values_lru<'a>(&'_ self) -> ValuesLRUIter<'a, K, V> {
        ValuesLRUIter {
            inner: self.iter_lru(),
        }
    }

    /// An iterator visiting all values in most-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.values_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn values_mut<'a>(&'_ mut self) -> ValuesMRUIterMut<'a, K, V> {
        ValuesMRUIterMut {
            inner: self.iter_mut(),
        }
    }

    /// An iterator visiting all values in less-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.values_lru_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn values_lru_mut<'a>(&'_ mut self) -> ValuesLRUIterMut<'a, K, V> {
        ValuesLRUIterMut {
            inner: self.iter_lru_mut(),
        }
    }

    /// An iterator visiting all entries in most-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter<'a>(&'_ self) -> MRUIter<'a, K, V> {
        MRUIter {
            len: self.len(),
            ptr: unsafe { (*self.head).next },
            end: unsafe { (*self.tail).prev },
            phantom: PhantomData,
        }
    }

    /// An iterator visiting all entries in less-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.iter_lru() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter_lru<'a>(&'_ self) -> LRUIter<'a, K, V> {
        LRUIter {
            len: self.len(),
            ptr: unsafe { (*self.head).next },
            end: unsafe { (*self.tail).prev },
            phantom: PhantomData,
        }
    }

    /// An iterator visiting all entries in most-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// struct HddBlock {
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put(0, HddBlock { dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { dirty: true,  data: [0x77; 512]});
    ///
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.iter_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    /// }
    /// ```
    pub fn iter_mut<'a>(&'_ mut self) -> MRUIterMut<'a, K, V> {
        MRUIterMut {
            len: self.len(),
            ptr: unsafe { (*self.head).next },
            end: unsafe { (*self.tail).prev },
            phantom: PhantomData,
        }
    }

    /// An iterator visiting all entries in less-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, RawLRU};
    ///
    /// struct HddBlock {
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = RawLRU::new(3).unwrap();
    /// cache.put(0, HddBlock { dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { dirty: true,  data: [0x77; 512]});
    ///
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.iter_lru_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    /// }
    /// ```
    pub fn iter_lru_mut<'a>(&'_ mut self) -> LRUIterMut<'a, K, V> {
        LRUIterMut {
            len: self.len(),
            ptr: unsafe { (*self.head).next },
            end: unsafe { (*self.tail).prev },
            phantom: PhantomData,
        }
    }

    pub(crate) fn put_box(&mut self, mut bks: Box<EntryNode<K, V>>) -> PutResult<K, V> {
        if self.len() >= self.cap() {
            unsafe {
                // Safety: the cache length is not zero, so the cache must have a tail node.
                let node = ((*self.tail).prev).as_mut().unwrap();
                self.detach(node);

                // Safety: the node is in cache, so the cache map must have the node.
                let node = self
                    .map
                    .remove(&KeyRef {
                        k: node.key.as_ptr(),
                    })
                    .unwrap();

                self.attach(bks.as_mut());
                self.map.insert(
                    KeyRef {
                        k: bks.key.as_ptr(),
                    },
                    bks,
                );

                PutResult::Evicted {
                    key: node.key.assume_init(),
                    value: node.val.assume_init(),
                }
            }
        } else {
            let node_ptr: *mut EntryNode<K, V> = &mut *bks;
            self.attach(node_ptr);

            let keyref = unsafe { (*node_ptr).key.as_ptr() };
            self.map.insert(KeyRef { k: keyref }, bks);
            PutResult::Put
        }
    }

    #[inline]
    pub(crate) fn update(&mut self, v: &mut V, ent_ptr: *mut EntryNode<K, V>) {
        // if the key is already in the cache just update its value and move it to the
        // front of the list
        unsafe { mem::swap(v, &mut (*(*ent_ptr).val.as_mut_ptr()) as &mut V) }
        self.detach(ent_ptr);
        self.attach(ent_ptr);
    }

    #[inline]
    pub(crate) fn put_in(&mut self, mut k: K, mut v: V) -> PutResult<K, V> {
        if self.len() >= self.cap() {
            // if the cache is full, remove the last entry so we can use it for the new key
            let old_key = KeyRef {
                k: unsafe { &(*(*(*self.tail).prev).key.as_ptr()) },
            };
            let mut old_node = self.map.remove(&old_key).unwrap();
            let old_node_ptr = old_node.as_mut();

            // if the key and value with the least recent used entry
            unsafe {
                mem::swap(&mut v, &mut (*(*old_node_ptr).val.as_mut_ptr()) as &mut V);
                mem::swap(&mut k, &mut (*(*old_node_ptr).key.as_mut_ptr()) as &mut K);
            }

            let node_ptr: *mut EntryNode<K, V> = &mut *old_node;
            self.detach(node_ptr);
            self.attach(node_ptr);

            let keyref = unsafe { (*node_ptr).key.as_ptr() };
            self.map.insert(KeyRef { k: keyref }, old_node);
            self.cb(&k, &v);
            PutResult::Evicted { key: k, value: v }
        } else {
            // if the cache is not full allocate a new EntryNode
            let mut node = Box::new(EntryNode::new(k, v));
            let node_ptr: *mut EntryNode<K, V> = &mut *node;
            self.attach(node_ptr);

            let keyref = unsafe { (*node_ptr).key.as_ptr() };
            self.map.insert(KeyRef { k: keyref }, node);
            PutResult::Put
        }
    }

    pub(crate) fn put_or_evict_box(
        &mut self,
        mut bks: Box<EntryNode<K, V>>,
    ) -> Option<Box<EntryNode<K, V>>> {
        if self.len() >= self.cap() {
            unsafe {
                // Safety: the cache length is not zero, so the cache must have a tail node.
                let node = ((*self.tail).prev).as_mut().unwrap();
                self.detach(node);

                // Safety: the node is in cache, so the cache map must have the node.
                let node = self
                    .map
                    .remove(&KeyRef {
                        k: node.key.as_ptr(),
                    })
                    .unwrap();

                self.attach(bks.as_mut());
                self.map.insert(
                    KeyRef {
                        k: bks.key.as_ptr(),
                    },
                    bks,
                );
                Some(node)
            }
        } else {
            let node_ptr: *mut EntryNode<K, V> = &mut *bks;
            self.attach(node_ptr);

            let keyref = unsafe { (*node_ptr).key.as_ptr() };
            self.map.insert(KeyRef { k: keyref }, bks);
            None
        }
    }

    pub(crate) fn remove_and_return_ent<Q>(&mut self, k: &Q) -> Option<Box<EntryNode<K, V>>>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.map.remove(k) {
            None => None,
            Some(mut old_node) => {
                let node_ptr: *mut EntryNode<K, V> = &mut *old_node;
                self.detach(node_ptr);
                Some(old_node)
            }
        }
    }

    pub(crate) fn remove_lru_in(&mut self) -> Option<Box<EntryNode<K, V>>> {
        let prev;
        unsafe { prev = (*self.tail).prev }
        if prev != self.head {
            let old_key = KeyRef {
                k: unsafe { &(*(*(*self.tail).prev).key.as_ptr()) },
            };
            let old_node = self.map.remove(&old_key);
            match old_node {
                None => None,
                Some(mut old_node) => {
                    let node_ptr: *mut EntryNode<K, V> = &mut *old_node;
                    self.detach(node_ptr);
                    Some(old_node)
                }
            }
        } else {
            None
        }
    }

    pub(crate) fn detach(&mut self, node: *mut EntryNode<K, V>) {
        unsafe {
            (*(*node).prev).next = (*node).next;
            (*(*node).next).prev = (*node).prev;
        }
    }

    pub(crate) fn attach(&mut self, node: *mut EntryNode<K, V>) {
        unsafe {
            (*node).next = (*self.head).next;
            (*node).prev = self.head;
            (*self.head).next = node;
            (*(*node).next).prev = node;
        }
    }

    #[inline]
    fn cb(&self, k: &K, v: &V) {
        if let Some(ref cb) = self.on_evict {
            cb.on_evict(k, v);
        }
    }
}

impl<K, V, E, S> Drop for RawLRU<K, V, E, S> {
    fn drop(&mut self) {
        self.map.values_mut().for_each(|e| unsafe {
            ptr::drop_in_place(e.key.as_mut_ptr());
            ptr::drop_in_place(e.val.as_mut_ptr());
        });
        // We rebox the head/tail, and because these are maybe-uninit
        // they do not have the absent k/v dropped.
        unsafe {
            let _head = *Box::from_raw(self.head);
            let _tail = *Box::from_raw(self.tail);
        }
    }
}

impl<'a, K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> IntoIterator
    for &'a RawLRU<K, V, E, S>
{
    type Item = (&'a K, &'a V);
    type IntoIter = MRUIter<'a, K, V>;

    fn into_iter(self) -> MRUIter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> IntoIterator
    for &'a mut RawLRU<K, V, E, S>
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = MRUIterMut<'a, K, V>;

    fn into_iter(self) -> MRUIterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<K: Hash + Eq, V> FromIterator<(K, V)> for RawLRU<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut this = Self::new(iter.size_hint().0).unwrap();
        iter.for_each(|(k, v)| {
            this.put(k, v);
        });
        this
    }
}

impl<K: Hash + Eq + Clone, V: Clone> From<&[(K, V)]> for RawLRU<K, V> {
    fn from(vals: &[(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

impl<K: Hash + Eq + Clone, V: Clone> From<&mut [(K, V)]> for RawLRU<K, V> {
    fn from(vals: &mut [(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

#[cfg(feature = "nightly")]
impl<K: Hash + Eq + Clone, V: Clone, const N: usize> From<[(K, V); N]> for RawLRU<K, V> {
    fn from(vals: [(K, V); N]) -> Self {
        vals.to_vec().into_iter().collect()
    }
}

macro_rules! impl_rawlru_from_kv_collections {
    ($($t:ty),*) => {
        $(
        impl<K: Hash + Eq, V> From<$t> for RawLRU<K, V>
        {
            fn from(vals: $t) -> Self {
                vals.into_iter().collect()
            }
        }
        )*
    }
}

impl_rawlru_from_kv_collections! (
    Vec<(K, V)>,
    VecDeque<(K, V)>,
    LinkedList<(K, V)>,
    HashSet<(K, V)>,
    BTreeSet<(K, V)>,
    BinaryHeap<(K, V)>,
    HashMap<K, V>,
    BTreeMap<K, V>
);

// The compiler does not automatically derive Send and Sync for RawLRU because it contains
// raw pointers. The raw pointers are safely encapsulated by RawLRU though so we can
// implement Send and Sync for it below.
unsafe impl<K: Send, V: Send, E: Send, S: Send> Send for RawLRU<K, V, E, S> {}
unsafe impl<K: Sync, V: Sync, E: Send, S: Sync> Sync for RawLRU<K, V, E, S> {}

impl<K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> fmt::Debug for RawLRU<K, V, E, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("RawLRU")
            .field("len", &self.len())
            .field("cap", &self.cap())
            .finish()
    }
}

///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// Iterators implementation ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////

/// An iterator over the entries, from most recent used to less recent used.
pub struct MRUIter<'a, K: 'a, V: 'a> {
    len: usize,

    ptr: *const EntryNode<K, V>,
    end: *const EntryNode<K, V>,

    phantom: PhantomData<&'a K>,
}

impl<'a, K, V> Iterator for MRUIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            return None;
        }

        let key = unsafe { &(*(*self.ptr).key.as_ptr()) as &K };
        let val = unsafe { &(*(*self.ptr).val.as_ptr()) as &V };

        self.len -= 1;
        self.ptr = unsafe { (*self.ptr).next };

        Some((key, val))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn count(self) -> usize {
        self.len
    }
}

impl<'a, K, V> DoubleEndedIterator for MRUIter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            return None;
        }

        let key = unsafe { &(*(*self.end).key.as_ptr()) as &K };
        let val = unsafe { &(*(*self.end).val.as_ptr()) as &V };

        self.len -= 1;
        self.end = unsafe { (*self.end).prev };

        Some((key, val))
    }
}

/// An iterator over the entries from less recent used to most recent used.
pub struct LRUIter<'a, K: 'a, V: 'a> {
    len: usize,

    ptr: *const EntryNode<K, V>,
    end: *const EntryNode<K, V>,

    phantom: PhantomData<&'a K>,
}

impl<'a, K, V> Iterator for LRUIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            return None;
        }

        let key = unsafe { &(*(*self.end).key.as_ptr()) as &K };
        let val = unsafe { &(*(*self.end).val.as_ptr()) as &V };

        self.len -= 1;
        self.end = unsafe { (*self.end).prev };

        Some((key, val))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn count(self) -> usize {
        self.len
    }
}

impl<'a, K, V> DoubleEndedIterator for LRUIter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            return None;
        }

        let key = unsafe { &(*(*self.ptr).key.as_ptr()) as &K };
        let val = unsafe { &(*(*self.ptr).val.as_ptr()) as &V };

        self.len -= 1;
        self.ptr = unsafe { (*self.ptr).next };

        Some((key, val))
    }
}

/// An iterator over mutable entries, from most recent used to less recent used.
pub struct MRUIterMut<'a, K: 'a, V: 'a> {
    len: usize,

    ptr: *mut EntryNode<K, V>,
    end: *mut EntryNode<K, V>,

    phantom: PhantomData<&'a K>,
}

impl<'a, K, V> Iterator for MRUIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        let key = unsafe { &mut (*(*self.ptr).key.as_mut_ptr()) as &mut K };
        let val = unsafe { &mut (*(*self.ptr).val.as_mut_ptr()) as &mut V };

        self.len -= 1;
        self.ptr = unsafe { (*self.ptr).next };

        Some((key, val))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn count(self) -> usize {
        self.len
    }
}

impl<'a, K, V> DoubleEndedIterator for MRUIterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        let key = unsafe { &mut (*(*self.end).key.as_mut_ptr()) as &mut K };
        let val = unsafe { &mut (*(*self.end).val.as_mut_ptr()) as &mut V };

        self.len -= 1;
        self.end = unsafe { (*self.end).prev };

        Some((key, val))
    }
}

/// An iterator over mutable entries, from less recent used to most recent used.
pub struct LRUIterMut<'a, K: 'a, V: 'a> {
    len: usize,

    ptr: *mut EntryNode<K, V>,
    end: *mut EntryNode<K, V>,

    phantom: PhantomData<&'a K>,
}

impl<'a, K, V> Iterator for LRUIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        let key = unsafe { &mut (*(*self.end).key.as_mut_ptr()) as &mut K };
        let val = unsafe { &mut (*(*self.end).val.as_mut_ptr()) as &mut V };

        self.len -= 1;
        self.end = unsafe { (*self.end).prev };

        Some((key, val))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn count(self) -> usize {
        self.len
    }
}

impl<'a, K, V> DoubleEndedIterator for LRUIterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        let key = unsafe { &mut (*(*self.ptr).key.as_mut_ptr()) as &mut K };
        let val = unsafe { &mut (*(*self.ptr).val.as_mut_ptr()) as &mut V };

        self.len -= 1;
        self.ptr = unsafe { (*self.ptr).next };

        Some((key, val))
    }
}

/// An iterator over entries, from most recent used to less recent used.
pub struct KeysMRUIter<'a, K, V> {
    inner: MRUIter<'a, K, V>,
}

/// An iterator over entries, from less recent used to most recent used.
pub struct KeysLRUIter<'a, K, V> {
    inner: LRUIter<'a, K, V>,
}

/// An iterator over entries, from most recent used to less recent used.
pub struct ValuesMRUIter<'a, K, V> {
    inner: MRUIter<'a, K, V>,
}

/// An iterator over mutable entries, from most recent used to less recent used.
pub struct ValuesMRUIterMut<'a, K: 'a, V: 'a> {
    inner: MRUIterMut<'a, K, V>,
}

/// An iterator over entries, from less recent used to most recent used.
pub struct ValuesLRUIter<'a, K: 'a, V: 'a> {
    inner: LRUIter<'a, K, V>,
}

/// An iterator over mutable entries, from less recent used to most recent used.
pub struct ValuesLRUIterMut<'a, K: 'a, V: 'a> {
    inner: LRUIterMut<'a, K, V>,
}

macro_rules! impl_clone_for_basic_iterator {
    ($($t:ty),*) => {
        $(
            impl<'a, K, V> Clone for $t {
                fn clone(&self) -> Self {
                    Self {
                        len: self.len,
                        ptr: self.ptr,
                        end: self.end,
                        phantom: PhantomData,
                    }
                }
            }
        )*
    }
}

macro_rules! impl_clone_for_kv_iterator {
    ($($t:ty),*) => {
        $(
            impl<K: Clone, V: Clone> Clone for $t {
                fn clone(&self) -> Self {
                    Self {
                        inner: self.inner.clone(),
                    }
                }
            }
        )*
    }
}

macro_rules! impl_keys_iterator {
    ($($t:ty),*) => {
        $(
            impl<'a, K, V> Iterator for $t {
                type Item = &'a K;

                fn next(&mut self) -> Option<Self::Item> {
                    self.inner.next().map(|(k, _)| k)
                }

                fn size_hint(&self) -> (usize, Option<usize>) {
                    (self.inner.len, Some(self.inner.len))
                }

                fn count(self) -> usize {
                    self.inner.len
                }
            }

            impl<'a, K, V> DoubleEndedIterator for $t {
                fn next_back(&mut self) -> Option<Self::Item> {
                    self.inner.next_back().map(|(k, _)| k)
                }
            }
        )*
    }
}

macro_rules! impl_values_iterator {
    ($($t:ty),*) => {
        $(
            impl<'a, K, V> Iterator for $t {
                type Item = &'a V;

                fn next(&mut self) -> Option<Self::Item> {
                    self.inner.next().map(|(_, v)| v)
                }

                fn size_hint(&self) -> (usize, Option<usize>) {
                    (self.inner.len, Some(self.inner.len))
                }

                fn count(self) -> usize {
                    self.inner.len
                }
            }

            impl<'a, K, V> DoubleEndedIterator for $t {
                fn next_back(&mut self) -> Option<Self::Item> {
                    self.inner.next_back().map(|(_, v)| v)
                }
            }
        )*
    }
}

macro_rules! impl_values_mut_iterator {
    ($($t:ty),*) => {
        $(
            impl<'a, K, V> Iterator for $t {
                type Item = &'a mut V;

                fn next(&mut self) -> Option<Self::Item> {
                    self.inner.next().map(|(_, v)| v)
                }

                fn size_hint(&self) -> (usize, Option<usize>) {
                    (self.inner.len, Some(self.inner.len))
                }

                fn count(self) -> usize {
                    self.inner.len
                }
            }

            impl<'a, K, V> DoubleEndedIterator for $t {
                fn next_back(&mut self) -> Option<Self::Item> {
                    self.inner.next_back().map(|(_, v)| v)
                }
            }
        )*
    }
}

macro_rules! impl_exact_size_and_fused_iterator {
    ($($t:ty),*) => {
        $(
            impl<'a, K, V> ExactSizeIterator for $t {}
            impl<'a, K, V> FusedIterator for $t {}
        )*
    }
}

macro_rules! impl_send_and_sync_for_iterator {
    ($($t:ty),*) => {
        $(
            // The compiler does not automatically derive Send and Sync for Iter because it contains
            // raw pointers.
            unsafe impl<'a, K: Send, V: Send> Send for $t {}
            unsafe impl<'a, K: Sync, V: Sync> Sync for $t {}
        )*
    }
}

impl_clone_for_basic_iterator! {
    MRUIter<'a, K, V>,
    LRUIter<'a, K, V>
}

impl_clone_for_kv_iterator! {
    KeysMRUIter<'_, K, V>,
    KeysLRUIter<'_, K, V>,
    ValuesMRUIter<'_, K, V>,
    ValuesLRUIter<'_, K, V>
}

impl_keys_iterator! {
    KeysMRUIter<'a, K, V>,
    KeysLRUIter<'a, K, V>
}

impl_values_iterator! {
    ValuesMRUIter<'a, K, V>,
    ValuesLRUIter<'a, K, V>
}

impl_values_mut_iterator! {
    ValuesMRUIterMut<'a, K, V>,
    ValuesLRUIterMut<'a, K, V>
}

impl_exact_size_and_fused_iterator! {
    MRUIter<'a, K, V>,
    LRUIter<'a, K, V>,
    MRUIterMut<'a, K, V>,
    LRUIterMut<'a, K, V>,
    KeysMRUIter<'a, K, V>,
    KeysLRUIter<'a, K, V>,
    ValuesMRUIter<'a, K, V>,
    ValuesMRUIterMut<'a, K, V>,
    ValuesLRUIter<'a, K, V>,
    ValuesLRUIterMut<'a, K, V>
}

impl_send_and_sync_for_iterator! {
    MRUIter<'a, K, V>,
    LRUIter<'a, K, V>,
    MRUIterMut<'a, K, V>,
    LRUIterMut<'a, K, V>,
    KeysMRUIter<'a, K, V>,
    KeysLRUIter<'a, K, V>,
    ValuesMRUIter<'a, K, V>,
    ValuesMRUIterMut<'a, K, V>,
    ValuesLRUIter<'a, K, V>,
    ValuesLRUIterMut<'a, K, V>
}

#[cfg(test)]
mod tests {
    use super::RawLRU;
    use crate::lru::CacheError;
    use crate::{Cache, PutResult, ResizableCache};
    use alloc::collections::BTreeMap;
    use core::fmt::Debug;
    use scoped_threadpool::Pool;
    use std::collections::HashMap;
    use std::sync::atomic::{AtomicUsize, Ordering};

    fn assert_opt_eq<V: PartialEq + Debug>(opt: Option<&V>, v: V) {
        assert!(opt.is_some());
        assert_eq!(opt.unwrap(), &v);
    }

    fn assert_opt_eq_mut<V: PartialEq + Debug>(opt: Option<&mut V>, v: V) {
        assert!(opt.is_some());
        assert_eq!(opt.unwrap(), &v);
    }

    fn assert_opt_eq_tuple<K: PartialEq + Debug, V: PartialEq + Debug>(
        opt: Option<(&K, &V)>,
        kv: (K, V),
    ) {
        assert!(opt.is_some());
        let res = opt.unwrap();
        assert_eq!(res.0, &kv.0);
        assert_eq!(res.1, &kv.1);
    }

    fn assert_opt_eq_mut_tuple<K: PartialEq + Debug, V: PartialEq + Debug>(
        opt: Option<(&K, &mut V)>,
        kv: (K, V),
    ) {
        assert!(opt.is_some());
        let res = opt.unwrap();
        assert_eq!(res.0, &kv.0);
        assert_eq!(res.1, &kv.1);
    }

    #[test]
    #[cfg(feature = "hashbrown")]
    fn test_with_hasher() {
        use hashbrown::hash_map::DefaultHashBuilder;

        let s = DefaultHashBuilder::default();
        let mut cache = RawLRU::with_hasher(16, s).unwrap();

        for i in 0..13370 {
            cache.put(i, ());
        }
        assert_eq!(cache.len(), 16);
    }

    #[test]
    fn test_from_iter() {
        let mut map = HashMap::new();
        map.insert(1, "a");
        map.insert(2, "b");
        map.insert(3, "c");

        let cache: RawLRU<u64, &str> = map.into_iter().collect();

        assert_eq!(cache.cap(), 3);
        assert_opt_eq(cache.peek(&1), &"a");
        assert_opt_eq(cache.peek(&2), &"b");
        assert_opt_eq(cache.peek(&3), &"c");

        let mut map = BTreeMap::new();
        map.insert(1, "a");
        map.insert(2, "b");
        map.insert(3, "c");

        let cache: RawLRU<u64, &str> = map.into_iter().collect();

        assert_eq!(cache.cap(), 3);
        assert_opt_eq(cache.peek(&1), &"a");
        assert_opt_eq(cache.peek(&2), &"b");
        assert_opt_eq(cache.peek(&3), &"c");
    }

    #[test]
    fn test_put_and_get() {
        let mut cache = RawLRU::new(2).unwrap();
        assert!(cache.is_empty());

        assert_eq!(cache.put("apple", "red"), PutResult::Put);
        assert_eq!(cache.put("banana", "yellow"), PutResult::Put);

        assert_eq!(cache.cap(), 2);
        assert_eq!(cache.len(), 2);
        assert!(!cache.is_empty());
        assert_opt_eq(cache.get(&"apple"), "red");
        assert_opt_eq(cache.get(&"banana"), "yellow");
    }

    #[test]
    fn test_put_and_get_mut() {
        let mut cache = RawLRU::new(2).unwrap();

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_eq!(cache.cap(), 2);
        assert_eq!(cache.len(), 2);
        assert_opt_eq_mut(cache.get_mut(&"apple"), "red");
        assert_opt_eq_mut(cache.get_mut(&"banana"), "yellow");
    }

    #[test]
    fn test_get_mut_and_update() {
        let mut cache = RawLRU::new(2).unwrap();

        cache.put("apple", 1);
        cache.put("banana", 3);

        {
            let v = cache.get_mut(&"apple").unwrap();
            *v = 4;
        }

        assert_eq!(cache.cap(), 2);
        assert_eq!(cache.len(), 2);
        assert_opt_eq_mut(cache.get_mut(&"apple"), 4);
        assert_opt_eq_mut(cache.get_mut(&"banana"), 3);
    }

    #[test]
    fn test_put_update() {
        let mut cache = RawLRU::new(1).unwrap();

        assert_eq!(cache.put("apple", "red"), PutResult::Put);
        assert_eq!(cache.put("apple", "green"), PutResult::Update("red"));

        assert_eq!(cache.len(), 1);
        assert_opt_eq(cache.get(&"apple"), "green");
    }

    #[test]
    fn test_put_removes_oldest() {
        let mut cache = RawLRU::new(2).unwrap();

        assert_eq!(cache.put("apple", "red"), PutResult::Put);
        assert_eq!(cache.put("banana", "yellow"), PutResult::Put);
        assert_eq!(
            cache.put("pear", "green"),
            PutResult::Evicted {
                key: "apple",
                value: "red"
            }
        );

        assert!(cache.get(&"apple").is_none());
        assert_opt_eq(cache.get(&"banana"), "yellow");
        assert_opt_eq(cache.get(&"pear"), "green");

        // Even though we inserted "apple" into the cache earlier it has since been removed from
        // the cache so there is no current value for `put` to return.
        assert_eq!(
            cache.put("apple", "green"),
            PutResult::Evicted {
                key: "banana",
                value: "yellow"
            }
        );
        assert_eq!(
            cache.put("tomato", "red"),
            PutResult::Evicted {
                key: "pear",
                value: "green"
            }
        );

        assert!(cache.get(&"pear").is_none());
        assert_opt_eq(cache.get(&"apple"), "green");
        assert_opt_eq(cache.get(&"tomato"), "red");
    }

    #[test]
    fn test_peek() {
        let mut cache = RawLRU::new(2).unwrap();

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_opt_eq(cache.peek(&"banana"), "yellow");
        assert_opt_eq(cache.peek(&"apple"), "red");

        cache.put("pear", "green");

        assert!(cache.peek(&"apple").is_none());
        assert_opt_eq(cache.peek(&"banana"), "yellow");
        assert_opt_eq(cache.peek(&"pear"), "green");
    }

    #[test]
    fn test_peek_mut() {
        let mut cache = RawLRU::new(2).unwrap();

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_opt_eq_mut(cache.peek_mut(&"banana"), "yellow");
        assert_opt_eq_mut(cache.peek_mut(&"apple"), "red");
        assert!(cache.peek_mut(&"pear").is_none());

        cache.put("pear", "green");

        assert!(cache.peek_mut(&"apple").is_none());
        assert_opt_eq_mut(cache.peek_mut(&"banana"), "yellow");
        assert_opt_eq_mut(cache.peek_mut(&"pear"), "green");

        {
            let v = cache.peek_mut(&"banana").unwrap();
            *v = "green";
        }

        assert_opt_eq_mut(cache.peek_mut(&"banana"), "green");
    }

    #[test]
    fn test_peek_lru() {
        let mut cache = RawLRU::new(2).unwrap();

        assert!(cache.peek_lru().is_none());

        cache.put("apple", "red");
        cache.put("banana", "yellow");
        assert_opt_eq_tuple(cache.peek_lru(), ("apple", "red"));

        cache.get(&"apple");
        assert_opt_eq_tuple(cache.peek_lru(), ("banana", "yellow"));

        cache.purge();
        assert!(cache.peek_lru().is_none());
    }

    #[test]
    fn test_contains() {
        let mut cache = RawLRU::new(2).unwrap();

        cache.put("apple", "red");
        cache.put("banana", "yellow");
        cache.put("pear", "green");

        assert!(!cache.contains(&"apple"));
        assert!(cache.contains(&"banana"));
        assert!(cache.contains(&"pear"));
    }

    #[test]
    fn test_remove() {
        let mut cache = RawLRU::new(2).unwrap();

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_eq!(cache.len(), 2);
        assert_opt_eq(cache.get(&"apple"), "red");
        assert_opt_eq(cache.get(&"banana"), "yellow");

        let popped = cache.remove(&"apple");
        assert!(popped.is_some());
        assert_eq!(popped.unwrap(), "red");
        assert_eq!(cache.len(), 1);
        assert!(cache.get(&"apple").is_none());
        assert_opt_eq(cache.get(&"banana"), "yellow");
    }

    #[test]
    fn test_remove_lru() {
        let mut cache = RawLRU::new(200).unwrap();

        for i in 0..75 {
            cache.put(i, "A");
        }
        for i in 0..75 {
            cache.put(i + 100, "B");
        }
        for i in 0..75 {
            cache.put(i + 200, "C");
        }
        assert_eq!(cache.len(), 200);

        for i in 0..75 {
            assert_opt_eq(cache.get(&(74 - i + 100)), "B");
        }
        assert_opt_eq(cache.get(&25), "A");

        for i in 26..75 {
            assert_eq!(cache.remove_lru(), Some((i, "A")));
        }
        for i in 0..75 {
            assert_eq!(cache.remove_lru(), Some((i + 200, "C")));
        }
        for i in 0..75 {
            assert_eq!(cache.remove_lru(), Some((74 - i + 100, "B")));
        }
        assert_eq!(cache.remove_lru(), Some((25, "A")));
        for _ in 0..50 {
            assert_eq!(cache.remove_lru(), None);
        }
    }

    #[test]
    fn test_purge() {
        let mut cache = RawLRU::new(2).unwrap();

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_eq!(cache.len(), 2);
        assert_opt_eq(cache.get(&"apple"), "red");
        assert_opt_eq(cache.get(&"banana"), "yellow");

        cache.purge();
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_resize_larger() {
        let mut cache = RawLRU::new(2).unwrap();

        cache.put(1, "a");
        cache.put(2, "b");
        cache.resize(4);
        cache.put(3, "c");
        cache.put(4, "d");

        assert_eq!(cache.len(), 4);
        assert_eq!(cache.get(&1), Some(&"a"));
        assert_eq!(cache.get(&2), Some(&"b"));
        assert_eq!(cache.get(&3), Some(&"c"));
        assert_eq!(cache.get(&4), Some(&"d"));
    }

    #[test]
    fn test_resize_smaller() {
        let mut cache = RawLRU::new(4).unwrap();

        cache.put(1, "a");
        cache.put(2, "b");
        cache.put(3, "c");
        cache.put(4, "d");

        cache.resize(2);

        assert_eq!(cache.len(), 2);
        assert!(cache.get(&1).is_none());
        assert!(cache.get(&2).is_none());
        assert_eq!(cache.get(&3), Some(&"c"));
        assert_eq!(cache.get(&4), Some(&"d"));
    }

    #[test]
    fn test_send() {
        use std::thread;

        let mut cache = RawLRU::new(4).unwrap();
        cache.put(1, "a");

        let handle = thread::spawn(move || {
            assert_eq!(cache.get(&1), Some(&"a"));
        });

        assert!(handle.join().is_ok());
    }

    #[test]
    fn test_multiple_threads() {
        let mut pool = Pool::new(1);
        let mut cache = RawLRU::new(4).unwrap();
        cache.put(1, "a");

        let cache_ref = &cache;
        pool.scoped(|scoped| {
            scoped.execute(move || {
                assert_eq!(cache_ref.peek(&1), Some(&"a"));
            });
        });

        assert_eq!((cache_ref).peek(&1), Some(&"a"));
    }

    #[test]
    fn test_keys_and_keys_lru_forwards() {
        let mut cache = RawLRU::new(3).unwrap();
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        {
            // keys mru
            let mut iter = cache.keys();
            assert_eq!(iter.len(), 3);
            assert_opt_eq(iter.next(), "c");

            assert_eq!(iter.len(), 2);
            assert_opt_eq(iter.next(), "b");

            assert_eq!(iter.len(), 1);
            assert_opt_eq(iter.next(), "a");

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
        {
            // keys lru
            let mut iter = cache.keys_lru();
            assert_eq!(iter.len(), 3);
            assert_opt_eq(iter.next(), "a");

            assert_eq!(iter.len(), 2);
            assert_opt_eq(iter.next(), "b");

            assert_eq!(iter.len(), 1);
            assert_opt_eq(iter.next(), "c");

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn test_values_and_values_lru_forwards() {
        let mut cache = RawLRU::new(3).unwrap();
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        {
            // values mru
            let mut iter = cache.values();
            assert_eq!(iter.len(), 3);
            assert_opt_eq(iter.next(), 3);

            assert_eq!(iter.len(), 2);
            assert_opt_eq(iter.next(), 2);

            assert_eq!(iter.len(), 1);
            assert_opt_eq(iter.next(), 1);

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
        {
            // values lru
            let mut iter = cache.values_lru();
            assert_eq!(iter.len(), 3);
            assert_opt_eq(iter.next(), 1);

            assert_eq!(iter.len(), 2);
            assert_opt_eq(iter.next(), 2);

            assert_eq!(iter.len(), 1);
            assert_opt_eq(iter.next(), 3);

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
        {
            // values mut mru
            let mut iter = cache.values_mut();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_mut(iter.next(), 3);

            assert_eq!(iter.len(), 2);
            assert_opt_eq_mut(iter.next(), 2);

            assert_eq!(iter.len(), 1);
            assert_opt_eq_mut(iter.next(), 1);

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
        {
            // values mut lru
            let mut iter = cache.values_lru_mut();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_mut(iter.next(), 1);

            assert_eq!(iter.len(), 2);
            assert_opt_eq_mut(iter.next(), 2);

            assert_eq!(iter.len(), 1);
            assert_opt_eq_mut(iter.next(), 3);

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn test_keys_and_keys_lru_backwards() {
        let mut cache = RawLRU::new(3).unwrap();
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        {
            // keys mru
            let mut iter = cache.keys();
            assert_eq!(iter.len(), 3);
            assert_opt_eq(iter.next_back(), "a");

            assert_eq!(iter.len(), 2);
            assert_opt_eq(iter.next_back(), "b");

            assert_eq!(iter.len(), 1);
            assert_opt_eq(iter.next_back(), "c");

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }
        {
            // keys lru
            let mut iter = cache.keys_lru();
            assert_eq!(iter.len(), 3);
            assert_opt_eq(iter.next_back(), "c");

            assert_eq!(iter.len(), 2);
            assert_opt_eq(iter.next_back(), "b");

            assert_eq!(iter.len(), 1);
            assert_opt_eq(iter.next_back(), "a");

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }
    }

    #[test]
    fn test_values_and_values_lru_backwards() {
        let mut cache = RawLRU::new(3).unwrap();
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        {
            // values mru
            let mut iter = cache.values();
            assert_eq!(iter.len(), 3);
            assert_opt_eq(iter.next_back(), 1);

            assert_eq!(iter.len(), 2);
            assert_opt_eq(iter.next_back(), 2);

            assert_eq!(iter.len(), 1);
            assert_opt_eq(iter.next_back(), 3);

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }
        {
            // values lru
            let mut iter = cache.values_lru();
            assert_eq!(iter.len(), 3);
            assert_opt_eq(iter.next_back(), 3);

            assert_eq!(iter.len(), 2);
            assert_opt_eq(iter.next_back(), 2);

            assert_eq!(iter.len(), 1);
            assert_opt_eq(iter.next_back(), 1);

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }
        {
            // values mut mru
            let mut iter = cache.values_mut();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_mut(iter.next_back(), 1);

            assert_eq!(iter.len(), 2);
            assert_opt_eq_mut(iter.next_back(), 2);

            assert_eq!(iter.len(), 1);
            assert_opt_eq_mut(iter.next_back(), 3);

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }
        {
            // values mut lru
            let mut iter = cache.values_lru_mut();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_mut(iter.next_back(), 3);

            assert_eq!(iter.len(), 2);
            assert_opt_eq_mut(iter.next_back(), 2);

            assert_eq!(iter.len(), 1);
            assert_opt_eq_mut(iter.next_back(), 1);

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }
    }

    #[test]
    fn test_iter_forwards() {
        let mut cache = RawLRU::new(3).unwrap();
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        {
            // iter const
            let mut iter = cache.iter();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_tuple(iter.next(), ("c", 3));

            assert_eq!(iter.len(), 2);
            assert_opt_eq_tuple(iter.next(), ("b", 2));

            assert_eq!(iter.len(), 1);
            assert_opt_eq_tuple(iter.next(), ("a", 1));

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
        {
            // iter mut
            let mut iter = cache.iter_mut();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_mut_tuple(iter.next(), ("c", 3));

            assert_eq!(iter.len(), 2);
            assert_opt_eq_mut_tuple(iter.next(), ("b", 2));

            assert_eq!(iter.len(), 1);
            assert_opt_eq_mut_tuple(iter.next(), ("a", 1));

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
        {
            // iter lru const
            let mut iter = cache.iter_lru();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_tuple(iter.next(), ("a", 1));

            assert_eq!(iter.len(), 2);
            assert_opt_eq_tuple(iter.next(), ("b", 2));

            assert_eq!(iter.len(), 1);
            assert_opt_eq_tuple(iter.next(), ("c", 3));

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
        {
            // iter lru mut
            let mut iter = cache.iter_lru_mut();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_mut_tuple(iter.next(), ("a", 1));

            assert_eq!(iter.len(), 2);
            assert_opt_eq_mut_tuple(iter.next(), ("b", 2));

            assert_eq!(iter.len(), 1);
            assert_opt_eq_mut_tuple(iter.next(), ("c", 3));

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn test_iter_backwards() {
        let mut cache = RawLRU::new(3).unwrap();
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        {
            // iter const
            let mut iter = cache.iter();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_tuple(iter.next_back(), ("a", 1));

            assert_eq!(iter.len(), 2);
            assert_opt_eq_tuple(iter.next_back(), ("b", 2));

            assert_eq!(iter.len(), 1);
            assert_opt_eq_tuple(iter.next_back(), ("c", 3));

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }

        {
            // iter mut
            let mut iter = cache.iter_mut();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_mut_tuple(iter.next_back(), ("a", 1));

            assert_eq!(iter.len(), 2);
            assert_opt_eq_mut_tuple(iter.next_back(), ("b", 2));

            assert_eq!(iter.len(), 1);
            assert_opt_eq_mut_tuple(iter.next_back(), ("c", 3));

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }
    }

    #[test]
    fn test_iter_forwards_and_backwards() {
        let mut cache = RawLRU::new(3).unwrap();
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        {
            // iter const
            let mut iter = cache.iter();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_tuple(iter.next(), ("c", 3));

            assert_eq!(iter.len(), 2);
            assert_opt_eq_tuple(iter.next_back(), ("a", 1));

            assert_eq!(iter.len(), 1);
            assert_opt_eq_tuple(iter.next(), ("b", 2));

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }
        {
            // iter mut
            let mut iter = cache.iter_mut();
            assert_eq!(iter.len(), 3);
            assert_opt_eq_mut_tuple(iter.next(), ("c", 3));

            assert_eq!(iter.len(), 2);
            assert_opt_eq_mut_tuple(iter.next_back(), ("a", 1));

            assert_eq!(iter.len(), 1);
            assert_opt_eq_mut_tuple(iter.next(), ("b", 2));

            assert_eq!(iter.len(), 0);
            assert_eq!(iter.next_back(), None);
        }
    }

    #[test]
    fn test_iter_multiple_threads() {
        let mut pool = Pool::new(1);
        let mut cache = RawLRU::new(3).unwrap();
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        let mut iter = cache.iter();
        assert_eq!(iter.len(), 3);
        assert_opt_eq_tuple(iter.next(), ("c", 3));

        {
            let iter_ref = &mut iter;
            pool.scoped(|scoped| {
                scoped.execute(move || {
                    assert_eq!(iter_ref.len(), 2);
                    assert_opt_eq_tuple(iter_ref.next(), ("b", 2));
                });
            });
        }

        assert_eq!(iter.len(), 1);
        assert_opt_eq_tuple(iter.next(), ("a", 1));

        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_clone() {
        let mut cache = RawLRU::new(3).unwrap();
        cache.put("a", 1);
        cache.put("b", 2);

        let mut iter = cache.iter();
        let mut iter_clone = iter.clone();

        assert_eq!(iter.len(), 2);
        assert_opt_eq_tuple(iter.next(), ("b", 2));
        assert_eq!(iter_clone.len(), 2);
        assert_opt_eq_tuple(iter_clone.next(), ("b", 2));

        assert_eq!(iter.len(), 1);
        assert_opt_eq_tuple(iter.next(), ("a", 1));
        assert_eq!(iter_clone.len(), 1);
        assert_opt_eq_tuple(iter_clone.next(), ("a", 1));

        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next(), None);
        assert_eq!(iter_clone.len(), 0);
        assert_eq!(iter_clone.next(), None);
    }

    #[test]
    fn test_that_pop_actually_detaches_node() {
        let mut cache = RawLRU::new(5).unwrap();

        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);
        cache.put("d", 4);
        cache.put("e", 5);

        assert_eq!(cache.remove(&"c"), Some(3));

        cache.put("f", 6);

        let mut iter = cache.iter();
        assert_opt_eq_tuple(iter.next(), ("f", 6));
        assert_opt_eq_tuple(iter.next(), ("e", 5));
        assert_opt_eq_tuple(iter.next(), ("d", 4));
        assert_opt_eq_tuple(iter.next(), ("b", 2));
        assert_opt_eq_tuple(iter.next(), ("a", 1));
        assert!(iter.next().is_none());
    }

    #[test]
    #[cfg(feature = "nightly")]
    fn test_get_with_borrow() {
        use alloc::string::String;

        let mut cache = RawLRU::new(2).unwrap();

        let key = String::from("apple");
        cache.put(key, "red");

        assert_opt_eq(cache.get("apple"), "red");
    }

    #[test]
    #[cfg(feature = "nightly")]
    fn test_get_mut_with_borrow() {
        use alloc::string::String;

        let mut cache = RawLRU::new(2).unwrap();

        let key = String::from("apple");
        cache.put(key, "red");

        assert_opt_eq_mut(cache.get_mut("apple"), "red");
    }

    #[test]
    fn test_no_memory_leaks() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct DropCounter;

        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        let n = 100;
        for _ in 0..n {
            let mut cache = RawLRU::new(1).unwrap();
            for i in 0..n {
                cache.put(i, DropCounter {});
            }
        }
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), n * n);
    }

    #[test]
    fn test_no_memory_leaks_with_clear() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct DropCounter;

        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        let n = 100;
        for _ in 0..n {
            let mut cache = RawLRU::new(1).unwrap();
            for i in 0..n {
                cache.put(i, DropCounter {});
            }
            cache.purge();
        }
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), n * n);
    }

    #[test]
    fn test_no_memory_leaks_with_resize() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct DropCounter;

        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        let n = 100;
        for _ in 0..n {
            let mut cache = RawLRU::new(1).unwrap();
            for i in 0..n {
                cache.put(i, DropCounter {});
            }
            cache.resize(0);
        }
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), n * n);
    }

    #[test]
    fn test_no_memory_leaks_with_remove() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[derive(Hash, Eq)]
        struct KeyDropCounter(usize);

        impl PartialEq for KeyDropCounter {
            fn eq(&self, other: &Self) -> bool {
                self.0.eq(&other.0)
            }
        }

        impl Drop for KeyDropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        let n = 100;
        for _ in 0..n {
            let mut cache = RawLRU::new(1).unwrap();

            for i in 0..n {
                cache.put(KeyDropCounter(i), i);
                cache.remove(&KeyDropCounter(i));
            }
        }

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), n * n * 2);
    }

    #[test]
    fn test_zero_cap_no_crash() {
        let cache = RawLRU::<u64, u64>::new(0);
        assert_eq!(cache.unwrap_err(), CacheError::InvalidSize(0))
    }
}
