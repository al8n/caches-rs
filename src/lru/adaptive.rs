use crate::lru::raw::EntryNode;
use crate::lru::raw::{
    KeysLRUIter, KeysMRUIter, LRUIter, LRUIterMut, MRUIter, MRUIterMut, RawLRU, ValuesLRUIter,
    ValuesLRUIterMut, ValuesMRUIter, ValuesMRUIterMut,
};
use crate::lru::{swap_value, CacheError};
use crate::{Cache, DefaultEvictCallback, DefaultHashBuilder, KeyRef, PutResult};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};

/// `AdaptiveCacheBuilder` is used to help build a [`AdaptiveCache`] with custom configuration.
///
/// [`AdaptiveCache`]: struct.AdaptiveCache.html
pub struct AdaptiveCacheBuilder<
    RH = DefaultHashBuilder,
    REH = DefaultHashBuilder,
    FH = DefaultHashBuilder,
    FEH = DefaultHashBuilder,
> {
    size: usize,
    recent_hasher: Option<RH>,
    recent_evict_hasher: Option<REH>,
    freq_hasher: Option<FH>,
    freq_evict_hasher: Option<FEH>,
}

impl Default for AdaptiveCacheBuilder {
    /// Create a default `AdaptiveCacheBuilder`.
    ///
    /// # Example
    /// ```rust
    /// use caches::{AdaptiveCacheBuilder, AdaptiveCache, Cache};
    /// let mut cache: AdaptiveCache<u64, u64> = AdaptiveCacheBuilder::default()
    ///     .set_size(5)
    ///     .finalize()
    ///     .unwrap();
    ///
    /// cache.put(1, 1);
    /// ```
    fn default() -> Self {
        Self {
            size: 0,
            recent_hasher: Some(DefaultHashBuilder::default()),
            recent_evict_hasher: Some(DefaultHashBuilder::default()),
            freq_hasher: Some(DefaultHashBuilder::default()),
            freq_evict_hasher: Some(DefaultHashBuilder::default()),
        }
    }
}

impl AdaptiveCacheBuilder {
    /// Returns a default [`AdaptiveCacheBuilder`].
    ///
    /// # Example
    /// ```rust
    ///
    /// use rustc_hash::FxHasher;
    /// use std::hash::BuildHasherDefault;
    /// use caches::{Cache, AdaptiveCacheBuilder};
    ///
    /// let mut cache = AdaptiveCacheBuilder::new(3)
    ///     .set_recent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_recent_evict_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_frequent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_frequent_evict_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .finalize::<u64, u64>()
    ///     .unwrap();
    ///
    /// cache.put(1, 1);
    /// ```
    ///
    /// [`AdaptiveCacheBuilder`]: struct.AdaptiveCacheBuilder.html
    pub fn new(size: usize) -> Self {
        Self::default().set_size(size)
    }
}

impl<RH: BuildHasher, REH: BuildHasher, FH: BuildHasher, FEH: BuildHasher>
    AdaptiveCacheBuilder<RH, REH, FH, FEH>
{
    /// Set the cache size
    pub fn set_size(self, size: usize) -> Self {
        Self {
            size,
            recent_hasher: self.recent_hasher,
            recent_evict_hasher: self.recent_evict_hasher,
            freq_hasher: self.freq_hasher,
            freq_evict_hasher: self.freq_evict_hasher,
        }
    }

    /// Set the recent LRU's hash builder
    pub fn set_recent_hasher<NRH: BuildHasher>(
        self,
        hasher: NRH,
    ) -> AdaptiveCacheBuilder<NRH, REH, FH, FEH> {
        AdaptiveCacheBuilder {
            size: self.size,
            recent_hasher: Some(hasher),
            recent_evict_hasher: self.recent_evict_hasher,
            freq_hasher: self.freq_hasher,
            freq_evict_hasher: self.freq_evict_hasher,
        }
    }

    /// Set the frequent LRU's hash builder
    pub fn set_frequent_hasher<NFH: BuildHasher>(
        self,
        hasher: NFH,
    ) -> AdaptiveCacheBuilder<RH, REH, NFH, FEH> {
        AdaptiveCacheBuilder {
            size: self.size,
            recent_hasher: self.recent_hasher,
            recent_evict_hasher: self.recent_evict_hasher,
            freq_hasher: Some(hasher),
            freq_evict_hasher: self.freq_evict_hasher,
        }
    }

    /// Set the recent evict LRU's hash builder
    pub fn set_recent_evict_hasher<NREH: BuildHasher>(
        self,
        hasher: NREH,
    ) -> AdaptiveCacheBuilder<RH, NREH, FH, FEH> {
        AdaptiveCacheBuilder {
            size: self.size,
            recent_hasher: self.recent_hasher,
            recent_evict_hasher: Some(hasher),
            freq_hasher: self.freq_hasher,
            freq_evict_hasher: self.freq_evict_hasher,
        }
    }

    /// Set the frequent evict LRU's hash builder
    pub fn set_frequent_evict_hasher<NFEH: BuildHasher>(
        self,
        hasher: NFEH,
    ) -> AdaptiveCacheBuilder<RH, REH, FH, NFEH> {
        AdaptiveCacheBuilder {
            size: self.size,
            recent_hasher: self.recent_hasher,
            recent_evict_hasher: self.recent_evict_hasher,
            freq_hasher: self.freq_hasher,
            freq_evict_hasher: Some(hasher),
        }
    }

    /// Finalize the builder to [`TwoQueueCache`]
    ///
    /// [`TwoQueueCache`]: struct.TwoQueueCache.html
    pub fn finalize<K: Hash + Eq, V>(
        self,
    ) -> Result<AdaptiveCache<K, V, RH, REH, FH, FEH>, CacheError> {
        let size = self.size;
        if size == 0 {
            return Err(CacheError::InvalidSize(0));
        }

        // allocate the lrus
        let recent = RawLRU::with_hasher(size, self.recent_hasher.unwrap()).unwrap();
        let recent_evict = RawLRU::with_hasher(size, self.recent_evict_hasher.unwrap()).unwrap();
        let freq = RawLRU::with_hasher(size, self.freq_hasher.unwrap()).unwrap();
        let freq_evict = RawLRU::with_hasher(size, self.freq_evict_hasher.unwrap()).unwrap();

        Ok(AdaptiveCache {
            size,
            p: 0,
            recent,
            recent_evict,
            frequent: freq,
            frequent_evict: freq_evict,
        })
    }
}

/// `AdaptiveCache` is a fixed size Adaptive Replacement Cache (ARC).
/// ARC is an enhancement over the standard LRU cache in that tracks both
/// frequency and recency of use. This avoids a burst in access to new
/// entries from evicting the frequently used older entries. It adds some
/// additional tracking overhead to a [`RawLRU`] cache with default evict callback policy, computationally
/// it is roughly **2x** the cost, and the extra memory overhead is linear
/// with the size of the cache. ARC has been patented by IBM, but is
/// similar to the [`TwoQueueCache`] (2Q) which requires setting parameters.
///
/// # Example
///
/// ```rust
///
/// use caches::{Cache, AdaptiveCache};
///
/// let mut cache = AdaptiveCache::new(4).unwrap();
///
/// // fill recent
/// (0..4).for_each(|i| {
///     cache.put(i, i);
/// });
///
/// // move to frequent
/// cache.get(&0);
/// cache.get(&1);
/// assert_eq!(cache.frequent_len(), 2);
///
/// // evict from recent
/// cache.put(4, 4);
/// assert_eq!(cache.recent_evict_len(), 1);
///
/// // current state
/// // recent:          (MRU) [4, 3] (LRU)
/// // frequent:        (MRU) [1, 0] (LRU)
/// // recent evict:    (MRU) [2] (LRU)
/// // frequent evict:  (MRU) [] (LRU)
///
/// // Add 2, should cause hit on recent_evict
/// cache.put(2, 2);
/// assert_eq!(cache.recent_evict_len(), 1);
/// assert_eq!(cache.partition(), 1);
/// assert_eq!(cache.frequent_len(), 3);
///
/// // Current state
/// // recent LRU:      (MRU) [4] (LRU)
/// // frequent LRU:    (MRU) [2, 1, 0] (LRU)
/// // recent evict:    (MRU) [3] (LRU)
/// // frequent evict:  (MRU) [] (LRU)
///
/// // Add 4, should migrate to frequent
/// cache.put(4, 4);
/// assert_eq!(cache.recent_len(), 0);
/// assert_eq!(cache.frequent_len(), 4);
///
/// // Current state
/// // recent LRU:      (MRU) [] (LRU)
/// // frequent LRU:    (MRU) [4, 2, 1, 0] (LRU)
/// // recent evict:    (MRU) [3] (LRU)
/// // frequent evict:  (MRU) [] (LRU)
///
/// // Add 5, should evict to b2
/// cache.put(5, 5);
/// assert_eq!(cache.recent_len(), 1);
/// assert_eq!(cache.frequent_len(), 3);
/// assert_eq!(cache.frequent_evict_len(), 1);
///
/// // Current state
/// // recent:          (MRU) [5] (LRU)
/// // frequent:        (MRU) [4, 2, 1] (LRU)
/// // recent evict:    (MRU) [3] (LRU)
/// // frequent evict:  (MRU) [0] (LRU)
///
/// // Add 0, should decrease p
/// cache.put(0, 0);
/// assert_eq!(cache.recent_len(), 0);
/// assert_eq!(cache.frequent_len(), 4);
/// assert_eq!(cache.recent_evict_len(), 2);
/// assert_eq!(cache.frequent_evict_len(), 0);
/// assert_eq!(cache.partition(), 0);
///
/// // Current state
/// // recent:         (MRU) [] (LRU)
/// // frequent:       (MRU) [0, 4, 2, 1] (LRU)
/// // recent evict:   (MRU) [5, 3] (LRU)
/// // frequent evict: (MRU) [0] (LRU)
/// ```
///
/// [`RawLRU`]: struct.RawLRU.html
/// [`TwoQueueCache`]: struct.TwoQueueCache.html
pub struct AdaptiveCache<
    K,
    V,
    RH = DefaultHashBuilder,
    REH = DefaultHashBuilder,
    FH = DefaultHashBuilder,
    FEH = DefaultHashBuilder,
> {
    /// `size` is the total capacity of the cache
    size: usize,

    /// `p` is the dynamic preference towards T1 or T2
    p: usize,

    /// `recent` is the LRU for recently accessed items
    recent: RawLRU<K, V, DefaultEvictCallback, RH>,

    /// `recent_evict` is the LRU for evictions from `recent`
    recent_evict: RawLRU<K, V, DefaultEvictCallback, REH>,

    /// `frequent` is the LRU for frequently accessed items
    frequent: RawLRU<K, V, DefaultEvictCallback, FH>,

    /// `frequent_evict` is the LRU for evictions from `frequent`
    frequent_evict: RawLRU<K, V, DefaultEvictCallback, FEH>,
}

impl<K: Hash + Eq, V> AdaptiveCache<K, V> {
    /// Create a `AdaptiveCache` with size and default configurations.
    pub fn new(size: usize) -> Result<Self, CacheError> {
        AdaptiveCacheBuilder::new(size).finalize()
    }

    /// Returns a [`AdaptiveCacheBuilder`] to help build a [`AdaptiveCache`].
    ///
    /// # Example
    /// ```rust
    /// use caches::{AdaptiveCacheBuilder, AdaptiveCache, Cache};
    /// use rustc_hash::FxHasher;
    /// use std::hash::BuildHasherDefault;
    ///
    /// let mut cache = AdaptiveCache::<u64, u64>::builder(3)
    ///     .set_recent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_recent_evict_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_frequent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_frequent_evict_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .finalize::<u64, u64>()
    ///     .unwrap();
    ///
    /// cache.put(1, 1);
    /// ```
    ///
    /// [`AdaptiveCacheBuilder`]: struct.AdaptiveCacheBuilder.html
    /// [`AdaptiveCache`]: struct.AdaptiveCache.html
    pub fn builder(size: usize) -> AdaptiveCacheBuilder {
        AdaptiveCacheBuilder::new(size)
    }
}

impl<K: Hash + Eq, V, RH: BuildHasher, REH: BuildHasher, FH: BuildHasher, FEH: BuildHasher>
    Cache<K, V> for AdaptiveCache<K, V, RH, REH, FH, FEH>
{
    fn put(&mut self, k: K, mut v: V) -> PutResult<K, V> {
        let key_ref = KeyRef { k: &k };
        // check if the value is contained in recent, and potentially
        // promote it to frequent
        if let Some(_) = self
            .recent
            // here we remove an entry from recent LRU if key exists
            .remove_and_return_ent(&key_ref)
            .map(|mut ent| {
                unsafe {
                    swap_value(&mut v, ent.as_mut());
                }
                // here we add the entry to frequent LRU,
                // the result will always be PutResult::Put
                // because we have removed this entry from recent LRU
                self.frequent.put_box(ent);
            })
        {
            return PutResult::Update(v);
        }

        // check if the value is already in frequent and update it
        if let Some(ent_ptr) = self.frequent.map.get_mut(&key_ref).map(|node| {
            let node_ptr: *mut EntryNode<K, V> = &mut **node;
            node_ptr
        }) {
            self.frequent.update(&mut v, ent_ptr);
            return PutResult::Update(v);
        }

        let recent_len = self.recent.len();
        let freq_len = self.frequent.len();
        let recent_evict_len = self.recent_evict.len();
        let freq_evict_len = self.frequent_evict.len();

        // check if this value was recently evicted as part of the
        // recently used list
        if self.recent_evict.contains(&key_ref) {
            // freq set is too small, increase P appropriately
            let mut delta = 1usize;

            if freq_evict_len > recent_evict_len {
                delta = freq_evict_len / recent_evict_len;
            }

            if self.p + delta >= self.size {
                self.p = self.size;
            } else {
                self.p += delta;
            }

            // potentially need to make room in the cache
            if self.recent.len() + self.frequent.len() >= self.size {
                self.replace(false);
            }

            // remove from recent evict
            let mut ent = self.recent_evict.map.remove(&key_ref).unwrap();
            let ent_ptr = ent.as_mut();
            self.recent_evict.detach(ent_ptr);
            unsafe {
                swap_value(&mut v, ent_ptr);
            }

            // add the key to the frequently used list
            self.frequent.put_box(ent);
            return PutResult::Update(v);
        }

        // Check if this value was recently evicted as part of the
        // frequently used list
        if self.frequent_evict.map.contains_key(&key_ref) {
            // frequent set is too small, decrease P appropriately
            let mut delta = 1usize;
            if recent_evict_len > freq_evict_len {
                delta = recent_evict_len / freq_evict_len;
            }

            if delta >= self.p {
                self.p = 0;
            } else {
                self.p -= delta;
            }

            // Potentially need to make room in the cache
            if recent_len + freq_len >= self.size {
                self.replace(true);
            }

            // remove from frequent evict
            let mut ent = self.frequent_evict.map.remove(&key_ref).unwrap();
            let ent_ptr = ent.as_mut();
            self.frequent_evict.detach(ent_ptr);

            unsafe {
                swap_value(&mut v, ent_ptr);
            }

            // add the key to the frequently used list
            self.frequent.put_box(ent);
            return PutResult::Update(v);
        }

        // Potentially need to make room in the cache
        if recent_len + freq_len >= self.size {
            self.replace(false);
        }

        // Keep the size of the ghost buffers trim
        if recent_evict_len > self.size - self.p {
            self.recent_evict.remove_lru();
        }

        if freq_evict_len > self.p {
            self.frequent_evict.remove_lru();
        }

        // Add to the recently seen list
        self.recent.put(k, v)
    }

    /// Returns a reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Moves the key to the head of the LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    /// let mut cache = AdaptiveCache::new(2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get(&"banana"), Some(&6));
    /// ```
    fn get<'a, Q>(&mut self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        // If the value is contained in recent, then
        // promote it to frequent
        self.recent
            .peek(k)
            .and_then(|v| self.move_to_frequent(k, v))
            .or_else(|| self.frequent.get(k))
    }

    /// Returns a mutable reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Moves the key to the head of the LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    /// let mut cache = AdaptiveCache::new(2).unwrap();
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
    fn get_mut<'a, Q>(&mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        // If the value is contained in recent, then
        // promote it to frequent
        self.recent
            .peek_mut(k)
            .and_then(|v| self.move_to_frequent(k, v))
            .or_else(|| self.frequent.get_mut(k))
    }

    /// Returns a reference to the value corresponding to the key in the cache or `None` if it is
    /// not present in the cache. Unlike `get`, `peek` does not update the LRU list so the key's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    /// let mut cache = AdaptiveCache::new(2).unwrap();
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
        self.recent.peek(k).or_else(|| self.frequent.peek(k))
    }

    /// Returns a mutable reference to the value corresponding to the key in the cache or `None`
    /// if it is not present in the cache. Unlike `get_mut`, `peek_mut` does not update the LRU
    /// list so the key's position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    /// let mut cache = AdaptiveCache::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.peek_mut(&2), Some(&mut "b"));
    /// ```
    fn peek_mut<'a, Q>(&mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.recent
            .peek_mut(k)
            .or_else(|| self.frequent.peek_mut(k))
    }

    /// Returns a bool indicating whether the given key is in the cache.
    /// Does not update the LRU list.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    /// let mut cache = AdaptiveCache::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    ///
    /// assert!(!cache.contains(&1));
    /// assert!(cache.contains(&2));
    /// assert!(cache.contains(&3));
    /// ```
    fn contains<Q>(&self, k: &Q) -> bool
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.recent.contains(k) || self.frequent.contains(k)
    }

    /// Removes and returns the value corresponding to the key from the cache or
    /// `None` if it does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    /// let mut cache = AdaptiveCache::new(2).unwrap();
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
        self.recent
            .remove(k)
            .or_else(|| self.frequent.remove(k))
            .or_else(|| self.recent_evict.remove(k))
            .or_else(|| self.frequent_evict.remove(k))
    }

    /// Clears the contents of the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    /// let mut cache: AdaptiveCache<isize, &str> = AdaptiveCache::new(2).unwrap();
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
        self.recent.purge();
        self.frequent.purge();
        self.recent_evict.purge();
        self.frequent_evict.purge();
    }

    /// Returns the number of key-value pairs that are currently in the the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    /// let mut cache = AdaptiveCache::new(2).unwrap();
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
        self.recent.len() + self.frequent.len()
    }

    /// Returns the maximum number of key-value pairs the cache can hold.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    /// let mut cache: AdaptiveCache<isize, &str> = AdaptiveCache::new(2).unwrap();
    /// assert_eq!(cache.cap(), 2);
    /// ```
    fn cap(&self) -> usize {
        self.size
    }

    fn is_empty(&self) -> bool {
        self.recent.is_empty()
            && self.recent_evict.is_empty()
            && self.frequent.is_empty()
            && self.frequent_evict.is_empty()
    }
}

impl<K: Hash + Eq, V, RH: BuildHasher, REH: BuildHasher, FH: BuildHasher, FEH: BuildHasher>
    AdaptiveCache<K, V, RH, REH, FH, FEH>
{
    /// Create a [`AdaptiveCache`] from [`AdaptiveCacheBuilder`].
    ///
    /// # Example
    /// ```rust
    /// use caches::{Cache, AdaptiveCacheBuilder, AdaptiveCache};
    /// use rustc_hash::FxHasher;
    /// use std::hash::BuildHasherDefault;
    ///
    /// let builder = AdaptiveCacheBuilder::new(5);
    ///
    /// let mut cache = AdaptiveCache::from_builder(builder).unwrap();
    /// cache.put(1, 1);
    /// ```
    ///
    /// [`AdaptiveCacheBuilder`]: struct.AdaptiveCacheBuilder.html
    /// [`AdaptiveCache`]: struct.AdaptiveCache.html
    pub fn from_builder(
        builder: AdaptiveCacheBuilder<RH, REH, FH, FEH>,
    ) -> Result<Self, CacheError> {
        builder.finalize()
    }

    /// Returns the current partition value of the cache.  
    pub fn partition(&self) -> usize {
        self.p
    }

    /// Returns the number of key-value pairs that are currently in the recent LRU.
    pub fn recent_len(&self) -> usize {
        self.recent.len()
    }

    /// Returns the number of key-value pairs that are currently in the frequent LRU.
    pub fn frequent_len(&self) -> usize {
        self.frequent.len()
    }

    /// Returns the number of key-value pairs that are currently in the recent evict LRU.
    pub fn recent_evict_len(&self) -> usize {
        self.recent_evict.len()
    }

    /// Returns the number of key-value pairs that are currently in the frequent evict LRU.
    pub fn frequent_evict_len(&self) -> usize {
        self.frequent_evict.len()
    }

    /// An iterator visiting all keys of recent LRU in most-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.recent_keys() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn recent_keys(&self) -> KeysMRUIter<'_, K, V> {
        self.recent.keys()
    }

    /// An iterator visiting all keys of recent LRU in less-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.recent_keys_lru() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn recent_keys_lru(&self) -> KeysLRUIter<'_, K, V> {
        self.recent.keys_lru()
    }

    /// An iterator visiting all values in most-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.recent_values() {
    ///     println!("val: {}",  val);
    /// }
    /// ```
    pub fn recent_values(&self) -> ValuesMRUIter<'_, K, V> {
        self.recent.values()
    }

    /// An iterator visiting all values of recent LRU in less-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.recent_values_lru() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn recent_values_lru(&self) -> ValuesLRUIter<'_, K, V> {
        self.recent.values_lru()
    }

    /// An iterator visiting all values of recent in most-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.recent_values_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn recent_values_mut(&mut self) -> ValuesMRUIterMut<'_, K, V> {
        self.recent.values_mut()
    }

    /// An iterator visiting all values of recent LRU in less-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.recent_values_lru_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn recent_values_lru_mut(&mut self) -> ValuesLRUIterMut<'_, K, V> {
        self.recent.values_lru_mut()
    }

    /// An iterator visiting all entries of recent LRU in most-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.recent_iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn recent_iter(&self) -> MRUIter<'_, K, V> {
        self.recent.iter()
    }

    /// An iterator visiting all entries of recent LRU in less-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.recent_iter_lru() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn recent_iter_lru(&self) -> LRUIter<'_, K, V> {
        self.recent.iter_lru()
    }

    /// An iterator visiting all entries of recent LRU in most-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// struct HddBlock {
    ///     idx: u64,
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    ///
    /// // put in recent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// let mut ctr = 2i32;
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.recent_iter_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    ///     assert_eq!(*block_id, ctr);
    ///     ctr -= 1;
    /// }
    /// ```
    pub fn recent_iter_mut(&mut self) -> MRUIterMut<'_, K, V> {
        self.recent.iter_mut()
    }

    /// An iterator visiting all entries of recent LRU in less-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// struct HddBlock {
    ///     idx: u64,
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    ///
    /// // put in recent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// let mut ctr = 0i32;
    ///
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.frequent_iter_lru_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    ///     assert_eq!(*block_id, ctr);
    ///     ctr += 1;
    /// }
    /// ```
    pub fn recent_iter_lru_mut(&mut self) -> LRUIterMut<'_, K, V> {
        self.recent.iter_lru_mut()
    }

    /// An iterator visiting all keys of recent evict LRU in most-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.recent_evict_keys() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn recent_evict_keys(&self) -> KeysMRUIter<'_, K, V> {
        self.recent_evict.keys()
    }

    /// An iterator visiting all keys of recent evict LRU in less-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.recent_evict_keys_lru() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn recent_evict_keys_lru(&self) -> KeysLRUIter<'_, K, V> {
        self.recent_evict.keys_lru()
    }

    /// An iterator visiting all values of recent evict LRU in most-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.recent_evict_values() {
    ///     println!("val: {}",  val);
    /// }
    /// ```
    pub fn recent_evict_values(&self) -> ValuesMRUIter<'_, K, V> {
        self.recent_evict.values()
    }

    /// An iterator visiting all values of recent evict LRU in less-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.recent_evict_values_lru() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn recent_evict_values_lru(&self) -> ValuesLRUIter<'_, K, V> {
        self.recent_evict.values_lru()
    }

    /// An iterator visiting all values of recent evict in most-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.recent_evict_values_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn recent_evict_values_mut(&mut self) -> ValuesMRUIterMut<'_, K, V> {
        self.recent_evict.values_mut()
    }

    /// An iterator visiting all values of recent evict LRU in less-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.recent_evict_values_lru_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn recent_evict_values_lru_mut(&mut self) -> ValuesLRUIterMut<'_, K, V> {
        self.recent_evict.values_lru_mut()
    }

    /// An iterator visiting all entries of recent evict LRU in most-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.recent_evict_iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn recent_evict_iter(&self) -> MRUIter<'_, K, V> {
        self.recent_evict.iter()
    }

    /// An iterator visiting all entries of recent evict LRU in less-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.recent_evict_iter_lru() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn recent_evict_iter_lru(&self) -> LRUIter<'_, K, V> {
        self.recent_evict.iter_lru()
    }

    /// An iterator visiting all entries of recent evict LRU in most-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// struct HddBlock {
    ///     idx: u64,
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    ///
    /// // put in recent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// // evict [0, 1, 2] to recent evict list
    /// cache.put(3, HddBlock { idx: 3, dirty: false, data: [0x00; 512]});
    /// cache.put(4, HddBlock { idx: 4, dirty: true,  data: [0x55; 512]});
    /// cache.put(5, HddBlock { idx: 5, dirty: true,  data: [0x77; 512]});
    ///
    /// let mut ctr = 2i32;
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.recent_evict_iter_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    ///     assert_eq!(*block_id, ctr);
    ///     ctr -= 1;
    /// }
    /// ```
    pub fn recent_evict_iter_mut(&mut self) -> MRUIterMut<'_, K, V> {
        self.recent_evict.iter_mut()
    }

    /// An iterator visiting all entries of recent evict LRU in less-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// struct HddBlock {
    ///     idx: u64,
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    ///
    /// // put in recent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// // evict [0, 1, 2] to frequent list
    /// cache.put(3, HddBlock { idx: 3, dirty: false, data: [0x00; 512]});
    /// cache.put(4, HddBlock { idx: 4, dirty: true,  data: [0x55; 512]});
    /// cache.put(5, HddBlock { idx: 5, dirty: true,  data: [0x77; 512]});
    ///
    /// let mut ctr = 0i32;
    ///
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.recent_evict_iter_lru_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    ///     assert_eq!(*block_id, ctr);
    ///     ctr += 1;
    /// }
    /// ```
    pub fn recent_evict_iter_lru_mut(&mut self) -> LRUIterMut<'_, K, V> {
        self.recent_evict.iter_lru_mut()
    }

    /// An iterator visiting all keys of frequent LRU in most-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.frequent_keys() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn frequent_keys(&self) -> KeysMRUIter<'_, K, V> {
        self.frequent.keys()
    }

    /// An iterator visiting all keys of frequent LRU in less-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.frequent_keys_lru() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn frequent_keys_lru(&self) -> KeysLRUIter<'_, K, V> {
        self.frequent.keys_lru()
    }

    /// An iterator visiting all values of frequent LRU in most-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.frequent_values() {
    ///     println!("val: {}",  val);
    /// }
    /// ```
    pub fn frequent_values(&self) -> ValuesMRUIter<'_, K, V> {
        self.frequent.values()
    }

    /// An iterator visiting all values of frequent LRU in less-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.frequent_values_lru() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn frequent_values_lru(&self) -> ValuesLRUIter<'_, K, V> {
        self.frequent.values_lru()
    }

    /// An iterator visiting all values of frequent LRU in most-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.frequent_values_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn frequent_values_mut(&mut self) -> ValuesMRUIterMut<'_, K, V> {
        self.frequent.values_mut()
    }

    /// An iterator visiting all values of frequent LRU in less-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.frequent_values_lru_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn frequent_values_lru_mut(&mut self) -> ValuesLRUIterMut<'_, K, V> {
        self.frequent.values_lru_mut()
    }

    /// An iterator visiting all entries of frequent LRU in most-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.frequent_iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn frequent_iter(&self) -> MRUIter<'_, K, V> {
        self.frequent.iter()
    }

    /// An iterator visiting all entries of frequent LRU in less-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.frequent_iter_lru() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn frequent_iter_lru(&self) -> LRUIter<'_, K, V> {
        self.frequent.iter_lru()
    }

    /// An iterator visiting all entries of frequent LRU in most-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// struct HddBlock {
    ///     idx: u64,
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    ///
    /// // put in recent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// // upgrade to frequent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// let mut ctr = 2i32;
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.frequent_iter_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    ///     assert_eq!(*block_id, ctr);
    ///     ctr -= 1;
    /// }
    /// ```
    pub fn frequent_iter_mut(&mut self) -> MRUIterMut<'_, K, V> {
        self.frequent.iter_mut()
    }

    /// An iterator visiting all entries of frequent LRU in less-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// struct HddBlock {
    ///     idx: u64,
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    ///
    /// // put in recent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// // upgrade to frequent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// let mut ctr = 0i32;
    ///
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.frequent_iter_lru_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    ///     assert_eq!(*block_id, ctr);
    ///     ctr += 1;
    /// }
    /// ```
    pub fn frequent_iter_lru_mut(&mut self) -> LRUIterMut<'_, K, V> {
        self.frequent.iter_lru_mut()
    }

    /// An iterator visiting all keys of frequent evict LRU in most-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.frequent_evict_keys() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn frequent_evict_keys(&self) -> KeysMRUIter<'_, K, V> {
        self.frequent_evict.keys()
    }

    /// An iterator visiting all keys of frequent evict LRU in less-recently used order. The iterator element type is
    /// `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for key in cache.frequent_evict_keys_lru() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn frequent_evict_keys_lru(&self) -> KeysLRUIter<'_, K, V> {
        self.frequent_evict.keys_lru()
    }

    /// An iterator visiting all values of frequent evict LRU in most-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.frequent_evict_values() {
    ///     println!("val: {}",  val);
    /// }
    /// ```
    pub fn frequent_evict_values(&self) -> ValuesMRUIter<'_, K, V> {
        self.frequent_evict.values()
    }

    /// An iterator visiting all values of frequent evict LRU in less-recently used order. The iterator element type is
    /// `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.frequent_evict_values_lru() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn frequent_evict_values_lru(&self) -> ValuesLRUIter<'_, K, V> {
        self.frequent_evict.values_lru()
    }

    /// An iterator visiting all values of frequent evict LRU in most-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.frequent_evict_values_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn frequent_evict_values_mut(&mut self) -> ValuesMRUIterMut<'_, K, V> {
        self.frequent_evict.values_mut()
    }

    /// An iterator visiting all values of frequent evict LRU in less-recently used order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for val in cache.frequent_evict_values_lru_mut() {
    ///     println!("val: {}", val);
    /// }
    /// ```
    pub fn frequent_evict_values_lru_mut(&mut self) -> ValuesLRUIterMut<'_, K, V> {
        self.frequent_evict.values_lru_mut()
    }

    /// An iterator visiting all entries of frequent evict LRU in most-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.frequent_evict_iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn frequent_evict_iter(&self) -> MRUIter<'_, K, V> {
        self.frequent_evict.iter()
    }

    /// An iterator visiting all entries of frequent evict LRU in less-recently used order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    /// cache.put("a", 1);
    /// cache.put("b", 2);
    /// cache.put("c", 3);
    ///
    /// for (key, val) in cache.frequent_evict_iter_lru() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn frequent_evict_iter_lru(&self) -> LRUIter<'_, K, V> {
        self.frequent_evict.iter_lru()
    }

    /// An iterator visiting all entries of frequent evict LRU in most-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// struct HddBlock {
    ///     idx: u64,
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    ///
    /// // put in recent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// // upgrade to frequent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// let mut ctr = 2i32;
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.frequent_evict_iter_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    ///     assert_eq!(*block_id, ctr);
    ///     ctr -= 1;
    /// }
    /// ```
    pub fn frequent_evict_iter_mut(&mut self) -> MRUIterMut<'_, K, V> {
        self.frequent_evict.iter_mut()
    }

    /// An iterator visiting all entries of frequent evict LRU in less-recently-used order, giving a mutable reference on
    /// V.  The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use caches::{Cache, AdaptiveCache};
    ///
    /// struct HddBlock {
    ///     idx: u64,
    ///     dirty: bool,
    ///     data: [u8; 512]
    /// }
    ///
    /// let mut cache = AdaptiveCache::new(3).unwrap();
    ///
    /// // put in recent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// // upgrade to frequent list
    /// cache.put(0, HddBlock { idx: 0, dirty: false, data: [0x00; 512]});
    /// cache.put(1, HddBlock { idx: 1, dirty: true,  data: [0x55; 512]});
    /// cache.put(2, HddBlock { idx: 2, dirty: true,  data: [0x77; 512]});
    ///
    /// let mut ctr = 0i32;
    ///
    /// // write dirty blocks to disk.
    /// for (block_id, block) in cache.frequent_evict_iter_lru_mut() {
    ///     if block.dirty {
    ///         // write block to disk
    ///         block.dirty = false
    ///     }
    ///     assert_eq!(*block_id, ctr);
    ///     ctr += 1;
    /// }
    /// ```
    pub fn frequent_evict_iter_lru_mut(&mut self) -> LRUIterMut<'_, K, V> {
        self.frequent_evict.iter_lru_mut()
    }

    /// replace is used to adaptively evict from either recent or frequent
    /// based on the current learned value of P
    fn replace(&mut self, freq_contains_key: bool) {
        let recent_evict_len = self.recent.len();
        if recent_evict_len > 0
            && (recent_evict_len > self.p || (recent_evict_len == self.p && freq_contains_key))
        {
            match self.recent.remove_lru_in() {
                None => None,
                Some(ent) => Some(self.recent_evict.put_box(ent)),
            };
        } else {
            match self.frequent.remove_lru_in() {
                None => None,
                Some(ent) => Some(self.frequent_evict.put_box(ent)),
            };
        }
    }

    fn move_to_frequent<T, Q>(&mut self, k: &Q, v: T) -> Option<T>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.recent.remove_and_return_ent(k) {
            None => None,
            Some(ent) => {
                self.frequent.put_box(ent);
                Some(v)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{AdaptiveCache, Cache};
    use alloc::vec::Vec;
    use rand::seq::SliceRandom;
    use rand::{thread_rng, Rng};

    #[test]
    fn test_arc_cache_random_ops() {
        let size = 128;
        let mut rng = thread_rng();
        let mut cases: Vec<u64> = (0..200_000).collect();
        cases.shuffle(&mut rng);

        let mut cache = AdaptiveCache::new(size).unwrap();

        (0..200_000).for_each(|_i| {
            let k = rng.gen::<i64>() % 512;
            let r: i64 = rng.gen();

            match r % 3 {
                0 => {
                    let _ = cache.put(k, k);
                }
                1 => {
                    let _ = cache.get(&k);
                }
                2 => {
                    let _ = cache.remove(&k);
                }
                _ => {}
            }

            assert!(cache.recent.len() + cache.frequent.len() <= size)
        })
    }

    #[test]
    fn test_arc_get_recent_to_frequent() {
        let mut cache = AdaptiveCache::new(128).unwrap();

        // Touch all the entries, should be in recent
        (0..128).for_each(|i| {
            cache.put(i, i);
        });
        assert_eq!(cache.recent.len(), 128);
        assert_eq!(cache.frequent.len(), 0);

        // Get should upgrade to t2
        (0..128).for_each(|i| {
            assert_ne!(cache.get(&i), None);
        });
        assert_eq!(cache.recent.len(), 0);
        assert_eq!(cache.frequent.len(), 128);

        // Get be from t2
        (0..128).for_each(|i| {
            assert_ne!(cache.get(&i), None);
        });
        assert_eq!(cache.recent.len(), 0);
        assert_eq!(cache.frequent.len(), 128);
    }

    #[test]
    fn test_arc_add_recent_to_freq() {
        let mut cache = AdaptiveCache::new(128).unwrap();

        // Add initially to recent
        cache.put(1, 1);
        assert_eq!(cache.recent.len(), 1);
        assert_eq!(cache.frequent.len(), 0);

        // Add should upgrade to frequent
        cache.put(1, 1);
        assert_eq!(cache.recent.len(), 0);
        assert_eq!(cache.frequent.len(), 1);

        // Add should remain to frequent
        cache.put(1, 1);
        assert_eq!(cache.recent.len(), 0);
        assert_eq!(cache.frequent.len(), 1);
    }

    #[test]
    fn test_arc_adaptive() {
        let mut cache = AdaptiveCache::new(4).unwrap();

        // fill recent
        (0..4).for_each(|i| {
            cache.put(i, i);
        });
        assert_eq!(cache.recent.len(), 4);

        // move to frequent
        cache.get(&0);
        cache.get(&1);
        assert_eq!(cache.frequent.len(), 2);

        // evict from recent
        cache.put(4, 4);
        assert_eq!(cache.recent_evict.len(), 1);

        // current state
        // recent : (MRU) [4, 3] (LRU)
        // frequent : (MRU) [1, 0] (LRU)
        // recent_evict : (MRU) [2] (LRU)
        // frequent_evict : (MRU) [] (LRU)

        // Add 2, should cause hit on recent_evict
        cache.put(2, 2);
        assert_eq!(cache.recent_evict.len(), 1);
        assert_eq!(cache.p, 1);
        assert_eq!(cache.frequent.len(), 3);

        // Current state
        // recent LRU: (MRU) [4] (LRU)
        // frequent LRU: (MRU) [2, 1, 0] (LRU)
        // recent evict: (MRU) [3] (LRU)
        // frequent evict: (MRU) [] (LRU)

        // Add 4, should migrate to frequent
        cache.put(4, 4);
        assert_eq!(cache.recent.len(), 0);
        assert_eq!(cache.frequent.len(), 4);

        // Current state
        // recent LRU: (MRU) [] (LRU)
        // frequent LRU: (MRU) [4, 2, 1, 0] (LRU)
        // recent evict: (MRU) [3] (LRU)
        // frequent evict: (MRU) [] (LRU)

        // Add 5, should evict to b2
        cache.put(5, 5);
        assert_eq!(cache.recent.len(), 1);
        assert_eq!(cache.frequent.len(), 3);
        assert_eq!(cache.frequent_evict.len(), 1);

        // Current state
        // recent LRU: (MRU) [5] (LRU)
        // frequent LRU: (MRU) [4, 2, 1] (LRU)
        // recent evict: (MRU) [3] (LRU)
        // frequent evict: (MRU) [0] (LRU)

        // Add 0, should decrease p
        cache.put(0, 0);
        assert_eq!(cache.recent.len(), 0);
        assert_eq!(cache.frequent.len(), 4);
        assert_eq!(cache.recent_evict.len(), 2);
        assert_eq!(cache.frequent_evict.len(), 0);
        assert_eq!(cache.p, 0);

        // Current state
        // recent LRU: (MRU) [] (LRU)
        // frequent LRU: (MRU) [0, 4, 2, 1] (LRU)
        // recent evict: (MRU) [5, 3] (LRU)
        // frequent evict: (MRU) [0] (LRU)
    }

    #[test]
    fn test_arc() {
        let mut cache = AdaptiveCache::new(128).unwrap();

        (0..256).for_each(|i| {
            cache.put(i, i);
        });
        assert_eq!(cache.len(), 128);

        let rst = cache
            .frequent
            .keys_lru()
            .chain(cache.recent.keys_lru())
            .enumerate()
            .map(|(idx, k)| (idx as u64, *k))
            .collect::<Vec<(u64, u64)>>();

        rst.into_iter().for_each(|(idx, k)| match cache.get(&k) {
            None => panic!("bad: {}", k),
            Some(val) => assert_eq!(*val, idx + 128),
        });

        (0..128).for_each(|k| {
            assert_eq!(cache.get(&k), None);
        });

        (128..256).for_each(|k| {
            assert_ne!(cache.get(&k), None);
        });

        (128..192).for_each(|k| {
            cache.remove(&k);
            assert_eq!(cache.get(&k), None);
        });

        cache.purge();
        assert_eq!(cache.len(), 0);
        assert_eq!(cache.get(&200), None);
    }

    #[test]
    fn test_2q_cache_contains() {
        let mut cache = AdaptiveCache::new(2).unwrap();
        cache.put(1, 1);
        cache.put(2, 2);

        assert!(cache.contains(&1));
        cache.put(3, 3);
        assert!(
            !cache.contains(&1),
            "should be in ghost LRU, and the elements in the ghost is not counted as in cache"
        );
    }

    #[test]
    fn test_arc_peek() {
        let mut cache = AdaptiveCache::new(2).unwrap();
        cache.put(1, 1);
        cache.put(2, 2);

        assert_eq!(cache.peek(&1), Some(&1));
        cache.put(3, 3);
        assert!(!cache.contains(&1));
    }
}
