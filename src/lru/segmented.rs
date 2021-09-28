use crate::lru::{debox, swap_value, CacheError, RawLRU};
use crate::{Cache, DefaultEvictCallback, DefaultHashBuilder, KeyRef, PutResult};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};

/// `SegmentedCacheBuilder` is used to help build a [`SegmentedCache`] with custom configurations.
///
/// [`SegmentedCache`]: struct.SegmentedCache.html
pub struct SegmentedCacheBuilder<FH = DefaultHashBuilder, RH = DefaultHashBuilder> {
    probationary_size: usize,
    protected_size: usize,
    probationary_hasher: Option<RH>,
    protected_hasher: Option<FH>,
}

impl Default for SegmentedCacheBuilder {
    fn default() -> Self {
        Self {
            probationary_size: 0,
            protected_size: 0,
            probationary_hasher: Some(DefaultHashBuilder::default()),
            protected_hasher: Some(DefaultHashBuilder::default()),
        }
    }
}

impl SegmentedCacheBuilder {
    /// Returns a [`SegmentedCacheBuilder`] with default hashers.
    pub fn new(probationary_size: usize, protected_size: usize) -> Self {
        Self {
            probationary_size,
            protected_size,
            probationary_hasher: Some(DefaultHashBuilder::default()),
            protected_hasher: Some(DefaultHashBuilder::default()),
        }
    }
}

impl<FH: BuildHasher, RH: BuildHasher> SegmentedCacheBuilder<FH, RH> {
    /// Set the cache size
    pub fn set_probationary_size(self, size: usize) -> Self {
        SegmentedCacheBuilder {
            probationary_size: size,
            protected_size: self.protected_size,
            probationary_hasher: self.probationary_hasher,
            protected_hasher: self.protected_hasher,
        }
    }

    /// Set the cache size
    pub fn set_protected_size(self, size: usize) -> Self {
        SegmentedCacheBuilder {
            probationary_size: self.probationary_size,
            protected_size: size,
            probationary_hasher: self.probationary_hasher,
            protected_hasher: self.protected_hasher,
        }
    }

    /// Set the probationary LRU's hash builder
    pub fn set_probationary_hasher<NRH: BuildHasher>(
        self,
        hasher: NRH,
    ) -> SegmentedCacheBuilder<FH, NRH> {
        SegmentedCacheBuilder {
            probationary_size: self.probationary_size,
            protected_size: self.protected_size,
            probationary_hasher: Some(hasher),
            protected_hasher: self.protected_hasher,
        }
    }

    /// Set the protected LRU's hash builder
    pub fn set_protected_hasher<NFH: BuildHasher>(
        self,
        hasher: NFH,
    ) -> SegmentedCacheBuilder<NFH, RH> {
        SegmentedCacheBuilder {
            probationary_size: self.probationary_size,
            protected_size: self.protected_size,
            probationary_hasher: self.probationary_hasher,
            protected_hasher: Some(hasher),
        }
    }

    /// Finalize the builder to [`SegmentedCache`]
    ///
    /// [`SegmentedCache`]: struct.SegmentedCache.html
    pub fn finalize<K: Hash + Eq, V>(self) -> Result<SegmentedCache<K, V, FH, RH>, CacheError> {
        if self.protected_size == 0 {
            return Err(CacheError::InvalidSize(0));
        }

        if self.probationary_size == 0 {
            return Err(CacheError::InvalidSize(0));
        }

        Ok(SegmentedCache {
            probationary_size: self.probationary_size,
            probationary: RawLRU::with_hasher(
                self.probationary_size,
                self.probationary_hasher.unwrap(),
            )
            .unwrap(),
            protected_size: self.protected_size,
            protected: RawLRU::with_hasher(self.protected_size, self.protected_hasher.unwrap())
                .unwrap(),
        })
    }
}

/// `SegmentedCache` is a fixed size [Segmented LRU Cache].
///
/// # Example
/// ```rust
/// use caches::{Cache, SegmentedCache};
///
/// let mut cache = SegmentedCache::new(2, 2).unwrap();
///
/// cache.put(1, 1);
/// cache.put(2, 2);
///
/// assert_eq!(cache.probationary_len(), 2);
/// assert_eq!(cache.protected_len(), 0);
///
/// assert_eq!(cache.get(&1), Some(&1));
/// *cache.get_mut(&2).unwrap() = 22;
///
/// assert_eq!(cache.probationary_len(), 0);
/// assert_eq!(cache.protected_len(), 2);
///
/// cache.put(3, 3);
/// cache.put(4, 4);
///
/// assert_eq!(cache.probationary_len(), 2);
/// assert_eq!(cache.protected_len(), 2);
///
/// assert_eq!(cache.peek(&3), Some(&3));
/// assert_eq!(cache.peek_mut(&4), Some(&mut 4));
///
/// assert_eq!(cache.probationary_len(), 2);
/// assert_eq!(cache.protected_len(), 2);
///
/// assert_eq!(cache.remove(&2), Some(22));
/// assert_eq!(cache.len(), 3);
///
/// cache.purge();
/// assert_eq!(cache.len(), 0);
/// ```
///
/// [Segmented LRU Cache]: https://dl.acm.org/doi/10.1109/2.268884
pub struct SegmentedCache<K, V, FH = DefaultHashBuilder, RH = DefaultHashBuilder> {
    probationary_size: usize,
    probationary: RawLRU<K, V, DefaultEvictCallback, RH>,

    protected_size: usize,
    protected: RawLRU<K, V, DefaultEvictCallback, FH>,
}

impl<K: Hash + Eq, V> SegmentedCache<K, V> {
    /// Create a `SegmentedCache` with size and default configurations.
    pub fn new(probationary_size: usize, protected_size: usize) -> Result<Self, CacheError> {
        SegmentedCacheBuilder::new(probationary_size, protected_size).finalize()
    }

    /// Returns a [`SegmentedCacheBuilder`] to help build a [`SegmentedCache`].
    ///
    /// # Example
    /// ```rust
    /// use caches::{Cache, SegmentedCacheBuilder, SegmentedCache};
    /// use rustc_hash::FxHasher;
    /// use std::hash::BuildHasherDefault;
    ///
    /// let mut cache = SegmentedCache::<u64, u64>::builder(3, 3)
    ///     .set_probationary_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_protected_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .finalize()
    ///     .unwrap();
    ///
    /// cache.put(1, 1);
    /// ```
    ///
    /// [`AdaptiveCacheBuilder`]: struct.AdaptiveCacheBuilder.html
    /// [`AdaptiveCache`]: struct.AdaptiveCache.html
    pub fn builder(probationary_size: usize, protected_size: usize) -> SegmentedCacheBuilder {
        SegmentedCacheBuilder::new(probationary_size, protected_size)
    }
}

impl<K: Hash + Eq, V, FH: BuildHasher, RH: BuildHasher> SegmentedCache<K, V, FH, RH> {
    /// Create a [`AdaptiveCache`] from [`SegmentedCacheBuilder`].
    ///
    /// # Example
    /// ```rust
    /// use caches::{Cache, SegmentedCache, SegmentedCacheBuilder};
    /// use rustc_hash::FxHasher;
    /// use std::hash::BuildHasherDefault;
    ///
    /// let builder = SegmentedCacheBuilder::new(5, 5);
    ///
    /// let mut cache = SegmentedCache::from_builder(builder).unwrap();
    /// cache.put(1, 1);
    /// ```
    ///
    /// [`SegmentedCacheBuilder`]: struct.SegmentedCacheBuilder.html
    /// [`SegmentedCache`]: struct.SegmentedCache.html
    pub fn from_builder(builder: SegmentedCacheBuilder<FH, RH>) -> Result<Self, CacheError> {
        builder.finalize()
    }

    /// `put_protected` will force to put an entry in protected LRU
    pub fn put_protected(&mut self, k: K, v: V) -> PutResult<K, V> {
        self.protected.put(k, v)
    }

    /// Returns the value corresponding to the least recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_lru_from_probationary` does not update the probationary LRU list so the item's
    /// position will be unchanged.
    pub fn peek_lru_from_probationary(&mut self) -> Option<(&K, &V)> {
        self.probationary.peek_lru()
    }

    /// Returns the mutable value corresponding to the least recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_lru_mut_from_probationary` does not update the probationary LRU list so the item's
    /// position will be unchanged.
    pub fn peek_lru_mut_from_probationary(&mut self) -> Option<(&K, &mut V)> {
        self.probationary.peek_lru_mut()
    }

    /// Returns the value corresponding to the most recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_mru_from_probationary` does not update the probationary LRU list so the item's
    /// position will be unchanged.
    pub fn peek_mru_from_probationary(&mut self) -> Option<(&K, &V)> {
        self.probationary.peek_mru()
    }

    /// Returns the mutable value corresponding to the most recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_mru_mut_from_probationary` does not update the probationary LRU list so the item's
    /// position will be unchanged.
    pub fn peek_mru_mut_from_probationary(&mut self) -> Option<(&K, &mut V)> {
        self.probationary.peek_mru_mut()
    }

    /// Returns the value corresponding to the least recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_lru_from_protected` does not update the protected LRU list so the item's
    /// position will be unchanged.
    pub fn peek_lru_from_protected(&self) -> Option<(&K, &V)> {
        self.protected.peek_lru()
    }

    /// Returns the mutable value corresponding to the least recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_lru_mut_from_protected` does not update the protected LRU list so the item's
    /// position will be unchanged.
    pub fn peek_lru_mut_from_protected(&mut self) -> Option<(&K, &mut V)> {
        self.protected.peek_lru_mut()
    }

    /// Returns the value corresponding to the most recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_mru_from_protected` does not update the protected LRU list so the item's
    /// position will be unchanged.
    pub fn peek_mru_from_protected(&self) -> Option<(&K, &V)> {
        self.protected.peek_mru()
    }

    /// Returns the mutable value corresponding to the most recently used item or `None` if the
    /// cache is empty. Like `peek`, `peek_mru_mut_from_protected` does not update the protected LRU list so the item's
    /// position will be unchanged.
    pub fn peek_mru_mut_from_protected(&mut self) -> Option<(&K, &mut V)> {
        self.protected.peek_mru_mut()
    }

    /// Removes and returns the key and value corresponding to the least recently
    /// used item or `None` if the probationary cache is empty.
    pub fn remove_lru_from_probationary(&mut self) -> Option<(K, V)> {
        self.probationary.remove_lru()
    }

    /// Removes and returns the key and value corresponding to the least recently
    /// used item or `None` if the protected cache is empty.
    pub fn remove_lru_from_protected(&mut self) -> Option<(K, V)> {
        self.protected.remove_lru()
    }

    /// Returns the number of key-value pairs that are currently in the protected LRU.
    pub fn protected_len(&self) -> usize {
        self.protected.len()
    }

    /// Returns the number of key-value pairs that are currently in the probationary LRU.
    pub fn probationary_len(&self) -> usize {
        self.probationary.len()
    }

    /// Returns the capacity of probationary LRU.
    pub fn probationary_cap(&self) -> usize {
        self.probationary_size
    }

    /// Returns the capacity of protected LRU.
    pub fn protected_cap(&self) -> usize {
        self.protected_size
    }

    fn move_to_protected<T, Q>(&mut self, k: &Q, v: T) -> Option<T>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        // remove the element from the probationary LRU
        // and put it in protected LRU.
        if let Some(ent) = self.probationary.remove_and_return_ent(k) {
            match self.protected.put_or_evict_box(ent) {
                None => Some(v),
                Some(old_ent) => {
                    self.probationary.put_box(old_ent);
                    Some(v)
                }
            }
        } else {
            None
        }
    }
}

impl<K: Hash + Eq, V, FH: BuildHasher, RH: BuildHasher> Cache<K, V>
    for SegmentedCache<K, V, FH, RH>
{
    /// Puts a key-value pair into cache, returns a [`PutResult`].
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, SegmentedCache};
    /// use caches::PutResult;
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
    ///
    /// assert_eq!(PutResult::Put, cache.put(1, "a"));
    /// assert_eq!(PutResult::Put, cache.put(2, "b"));
    /// assert_eq!(PutResult::Update("b"), cache.put(2, "beta"));
    /// assert_eq!(PutResult::Put, cache.put(3, "c"));
    ///
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"beta"));
    /// ```
    ///
    /// [`PutResult`]: struct.PutResult.html
    fn put(&mut self, k: K, mut v: V) -> PutResult<K, V> {
        let key_ref = KeyRef { k: &k };

        // check if the value is already in protected segment and update it
        if let Some(ent_ptr) = self
            .protected
            .map
            .get_mut(&key_ref)
            .map(|bks| debox::<K, V>(bks))
        {
            self.protected.update(&mut v, ent_ptr);
            return PutResult::Update(v);
        }

        // check if the value is already in probationary segment and move it to protected segment
        if self.probationary.contains(&key_ref) {
            return self
                .probationary
                .remove_and_return_ent(&key_ref)
                .and_then(|mut ent| {
                    let ent_ptr = ent.as_mut();
                    unsafe {
                        swap_value(&mut v, ent_ptr);
                    }
                    self.protected
                        .put_or_evict_box(ent)
                        .map(|evicted_ent| self.probationary.put_box(evicted_ent))
                })
                .unwrap_or(PutResult::<K, V>::Update(v));
        }

        // this is a new entry
        self.probationary.put(k, v)
    }

    /// Returns a reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Moves the key to the head of the protected segment LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, SegmentedCache};
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
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
        self.protected
            // already in protected LRU, we move it to the front
            .get(k)
            // does not in protected LRU, we try to find it in
            // probationary LRU
            .or_else(|| {
                self.probationary
                    .peek(k)
                    // we find the element in probationary LRU
                    // remove the element from the probationary LRU
                    // and put it in protected LRU.
                    .and_then(|v| self.move_to_protected(k, v))
            })
    }

    /// Returns a mutable reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Moves the key to the head of the protected segment LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, SegmentedCache};
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get_mut(&"banana"), Some(&mut 6));
    /// ```
    fn get_mut<'a, Q>(&mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.protected
            // already in protected LRU, we move it to the front
            .get_mut(k)
            // does not in protected LRU, we try to find it in
            // probationary LRU
            .or_else(|| {
                self.probationary
                    .peek_mut(k)
                    // we find the element in probationary LRU
                    // remove the element from the probationary LRU
                    // and put it in protected LRU.
                    .and_then(|v| self.move_to_protected(k, v))
            })
    }

    /// Returns a reference to the value corresponding to the key in the cache or `None` if it is
    /// not present in the cache. Unlike `get`, `peek` does not update the LRU list so the key's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, SegmentedCache};
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek(&1), Some(&"a"));
    /// assert_eq!(cache.peek(&2), Some(&"b"));
    /// ```
    fn peek<'a, Q>(&self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.protected.peek(k).or_else(|| self.probationary.peek(k))
    }

    /// Returns a mutable reference to the value corresponding to the key in the cache or `None` if it is
    /// not present in the cache. Unlike `get`, `peek` does not update the LRU list so the key's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, SegmentedCache};
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
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
        self.protected
            .peek_mut(k)
            .or_else(|| self.probationary.peek_mut(k))
    }

    /// Returns a bool indicating whether the given key is in the cache.
    /// Does not update the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, SegmentedCache};
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
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
        self.protected.contains(k) || self.probationary.contains(k)
    }

    /// Removes and returns the value corresponding to the key from the cache or
    /// `None` if it does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, SegmentedCache};
    ///
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
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
        self.probationary
            .remove(k)
            .or_else(|| self.protected.remove(k))
    }

    /// Clears the contents of the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{SegmentedCache, Cache};
    ///
    /// let mut cache: SegmentedCache<isize, &str> = SegmentedCache::new(2, 2).unwrap();
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
        self.probationary.purge();
        self.protected.purge();
    }

    /// Returns the number of key-value pairs that are currently in the the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::lru::SegmentedCache;
    /// use caches::Cache;
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
    /// assert_eq!(cache.len(), 0);
    ///
    /// cache.put(1, "a");
    /// assert_eq!(cache.len(), 1);
    ///
    /// cache.put(2, "b");
    /// assert_eq!(cache.len(), 2);
    ///
    /// // because no entry is in protected LRU, so this operation will evict
    /// cache.put(3, "c");
    /// assert_eq!(cache.len(), 2);
    ///
    /// // now 3 is put in protected LRU
    /// cache.put(3, "cc");
    /// assert_eq!(cache.len(), 2);
    ///
    /// // we can put 4-"d" in probationary LRU, and the size of cache is 3
    /// cache.put(4, "d");
    /// assert_eq!(cache.len(), 3);
    /// ```
    fn len(&self) -> usize {
        self.protected.len() + self.probationary.len()
    }

    /// Returns the maximum number of key-value pairs the cache can hold.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::lru::SegmentedCache;
    /// use caches::Cache;
    /// let mut cache: SegmentedCache<isize, &str> = SegmentedCache::new(2, 2).unwrap();
    /// assert_eq!(cache.cap(), 4);
    /// ```
    fn cap(&self) -> usize {
        self.protected_size + self.probationary_size
    }

    fn is_empty(&self) -> bool {
        self.protected.is_empty() && self.probationary.is_empty()
    }
}
