use crate::lru::{debox, swap_value, CacheError, RawLRU};
use crate::{DefaultEvictCallback, DefaultHashBuilder, KeyRef, PutResult};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};

/// `SegmentedCacheBuilder` is used to help build a [`SegmentedCache`] with custom configuration.
///
/// [`SegmentedCache`]: struct.SegmentedCache.html
pub struct SegmentedCacheBuilder<RH = DefaultHashBuilder, FH = DefaultHashBuilder> {
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

impl<RH: BuildHasher, FH: BuildHasher> SegmentedCacheBuilder<RH, FH> {
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
    ) -> SegmentedCacheBuilder<NRH, FH> {
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
    ) -> SegmentedCacheBuilder<RH, NFH> {
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
    pub fn finalize<K: Hash + Eq, V>(self) -> Result<SegmentedCache<K, V, RH, FH>, CacheError> {
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
/// [Segmented LRU Cache]: https://dl.acm.org/doi/10.1109/2.268884
pub struct SegmentedCache<K, V, RH = DefaultHashBuilder, FH = DefaultHashBuilder> {
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
    /// use caches::lru::{SegmentedCacheBuilder, SegmentedCache};
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

impl<K: Hash + Eq, V, RH: BuildHasher, FH: BuildHasher> SegmentedCache<K, V, RH, FH> {
    /// Create a [`AdaptiveCache`] from [`SegmentedCacheBuilder`].
    ///
    /// # Example
    /// ```rust
    /// use caches::lru::{SegmentedCache, SegmentedCacheBuilder};
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
    pub fn from_builder(builder: SegmentedCacheBuilder<RH, FH>) -> Result<Self, CacheError> {
        builder.finalize()
    }

    /// Puts a key-value pair into cache, returns a [`PutResult`].
    ///
    /// # Example
    ///
    /// ```
    /// use caches::lru::SegmentedCache;
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
    pub fn put(&mut self, k: K, mut v: V) -> PutResult<K, V> {
        let key_ref = KeyRef { k: &k };

        // check if the value is already in protected segment and update it
        match self
            .protected
            .map
            .get_mut(&key_ref)
            .map(|bks| debox::<K, V>(bks))
        {
            None => {}
            Some(ent_ptr) => {
                self.protected.update(&mut v, ent_ptr);
                return PutResult::Update(v);
            }
        }

        // check if the value is already in probationary segment and move it to protected segment
        if self.probationary.contains(&key_ref) {
            let mut ent = self.probationary.remove_and_return_ent(&key_ref).unwrap();
            let ent_ptr = ent.as_mut();
            unsafe {
                swap_value(&mut v, ent_ptr);
            }
            return match self.protected.put_or_evict_box(ent) {
                None => PutResult::Update(v),
                Some(old_ent) => self.probationary.put_box(old_ent),
            };
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
    /// use caches::lru::SegmentedCache;
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get(&"banana"), Some(&6));
    /// ```
    pub fn get<'a, Q>(&mut self, k: &'a Q) -> Option<&'a V>
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
    /// use caches::lru::SegmentedCache;
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get_mut(&"banana"), Some(&mut 6));
    /// ```
    pub fn get_mut<'a, Q>(&mut self, k: &'a Q) -> Option<&'a mut V>
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
    /// use caches::lru::SegmentedCache;
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek(&1), Some(&"a"));
    /// assert_eq!(cache.peek(&2), Some(&"b"));
    /// ```
    pub fn peek<'a, Q>(&self, k: &'a Q) -> Option<&'a V>
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
    /// use caches::lru::SegmentedCache;
    /// let mut cache = SegmentedCache::new(2, 2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.peek_mut(&2), Some(&mut "b"));
    /// ```
    pub fn peek_mut<'a, Q>(&mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.protected
            .peek_mut(k)
            .or_else(|| self.probationary.peek_mut(k))
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

// #[cfg(test)]
// mod test {
//     // use crate::lru::SegmentedCache;
// }
