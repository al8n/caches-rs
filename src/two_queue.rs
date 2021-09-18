use crate::raw::EntryNode;
use crate::{CacheError, DefaultEvictCallback, DefaultHashBuilder, KeyRef, PutResult, RawLRU};
use alloc::boxed::Box;
use alloc::fmt;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::mem;

/// `DEFAULT_2Q_RECENT_RATIO` is the ratio of the [`TwoQueueCache`] dedicated
/// to recently added entries that have only been accessed once.
///
/// [`TwoQueueCache`]: struct.TwoQueueCache.html
pub const DEFAULT_2Q_RECENT_RATIO: f64 = 0.25;

/// `DEFAULT_2Q_GHOST_ENTRIES` is the default ratio of ghost
/// entries kept to track entries recently evicted for [`TwoQueueCache`].
///
/// [`TwoQueueCache`]: struct.TwoQueueCache.html
pub const DEFAULT_2Q_GHOST_RATIO: f64 = 0.5;

/// `TwoQueueCacheBuilder` is used to help build a [`TwoQueueCache`] with custom configuration.
///
/// [`TwoQueueCache`]: struct.TwoQueueCache.html
pub struct TwoQueueCacheBuilder<
    RH = DefaultHashBuilder,
    FH = DefaultHashBuilder,
    GH = DefaultHashBuilder,
> {
    size: usize,
    ghost_ratio: Option<f64>,
    recent_ratio: Option<f64>,
    recent_hasher: Option<RH>,
    freq_hasher: Option<FH>,
    ghost_hasher: Option<GH>,
}

impl Default for TwoQueueCacheBuilder {
    /// Create a default `TwoQueueCacheBuilder`.
    ///
    /// # Example
    /// ```rust
    /// use hashicorp_lru::{TwoQueueCacheBuilder, TwoQueueCache};
    /// let mut cache: TwoQueueCache<u64, u64> = TwoQueueCacheBuilder::default()
    ///     .set_size(5)
    ///     .finalize()
    ///     .unwrap();
    ///
    /// cache.put(1, 1);
    /// ```
    fn default() -> Self {
        Self {
            size: 0,
            ghost_ratio: Some(DEFAULT_2Q_GHOST_RATIO),
            recent_ratio: Some(DEFAULT_2Q_RECENT_RATIO),
            recent_hasher: Some(DefaultHashBuilder::default()),
            freq_hasher: Some(DefaultHashBuilder::default()),
            ghost_hasher: Some(DefaultHashBuilder::default()),
        }
    }
}

impl TwoQueueCacheBuilder {
    /// Returns a default [`TwoQueueCacheBuilder`].
    ///
    /// # Example
    /// ```rust
    /// use hashicorp_lru::{TwoQueueCacheBuilder, TwoQueueCache};
    /// use rustc_hash::FxHasher;
    /// use std::hash::BuildHasherDefault;
    ///
    /// let mut cache = TwoQueueCacheBuilder::new(3)
    ///     .set_recent_ratio(0.3)
    ///     .set_ghost_ratio(0.4)
    ///     .set_recent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_frequent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_ghost_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .finalize::<u64, u64>()
    ///     .unwrap();
    ///
    /// cache.put(1, 1);
    /// ```
    ///
    /// [`TwoQueueCacheBuilder`]: struct.TwoQueueCacheBuilder.html
    pub fn new(size: usize) -> Self {
        Self::default().set_size(size)
    }
}

impl<RH: BuildHasher, FH: BuildHasher, GH: BuildHasher> TwoQueueCacheBuilder<RH, FH, GH> {
    /// Set the ghost LRU size ratio
    pub fn set_ghost_ratio(self, ratio: f64) -> Self {
        TwoQueueCacheBuilder {
            size: self.size,
            ghost_ratio: Some(ratio),
            recent_ratio: self.recent_ratio,
            recent_hasher: self.recent_hasher,
            freq_hasher: self.freq_hasher,
            ghost_hasher: self.ghost_hasher,
        }
    }

    /// Set the recent LRU size ratio
    pub fn set_recent_ratio(self, ratio: f64) -> Self {
        TwoQueueCacheBuilder {
            size: self.size,
            ghost_ratio: self.ghost_ratio,
            recent_ratio: Some(ratio),
            recent_hasher: self.recent_hasher,
            freq_hasher: self.freq_hasher,
            ghost_hasher: self.ghost_hasher,
        }
    }

    /// Set the cache size
    pub fn set_size(self, size: usize) -> Self {
        TwoQueueCacheBuilder {
            size,
            ghost_ratio: self.ghost_ratio,
            recent_ratio: self.recent_ratio,
            recent_hasher: self.recent_hasher,
            freq_hasher: self.freq_hasher,
            ghost_hasher: self.ghost_hasher,
        }
    }

    /// Set the recent LRU's hash builder
    pub fn set_recent_hasher<NRH: BuildHasher>(
        self,
        hasher: NRH,
    ) -> TwoQueueCacheBuilder<NRH, FH, GH> {
        TwoQueueCacheBuilder {
            size: self.size,
            ghost_ratio: self.ghost_ratio,
            recent_ratio: self.recent_ratio,
            recent_hasher: Some(hasher),
            freq_hasher: self.freq_hasher,
            ghost_hasher: self.ghost_hasher,
        }
    }

    /// Set the frequent LRU's hash builder
    pub fn set_frequent_hasher<NFH: BuildHasher>(
        self,
        hasher: NFH,
    ) -> TwoQueueCacheBuilder<RH, NFH, GH> {
        TwoQueueCacheBuilder {
            size: self.size,
            ghost_ratio: self.ghost_ratio,
            recent_ratio: self.recent_ratio,
            recent_hasher: self.recent_hasher,
            freq_hasher: Some(hasher),
            ghost_hasher: self.ghost_hasher,
        }
    }

    /// Set the ghost LRU's hash builder
    pub fn set_ghost_hasher<NGH: BuildHasher>(
        self,
        hasher: NGH,
    ) -> TwoQueueCacheBuilder<RH, FH, NGH> {
        TwoQueueCacheBuilder {
            size: self.size,
            ghost_ratio: self.ghost_ratio,
            recent_ratio: self.recent_ratio,
            recent_hasher: self.recent_hasher,
            freq_hasher: self.freq_hasher,
            ghost_hasher: Some(hasher),
        }
    }

    /// Finalize the builder to [`TwoQueueCache`]
    ///
    /// [`TwoQueueCache`]: struct.TwoQueueCache.html
    pub fn finalize<K: Hash + Eq, V>(self) -> Result<TwoQueueCache<K, V, RH, FH, GH>, CacheError> {
        let size = self.size;
        if size == 0 {
            return Err(CacheError::InvalidSize(0));
        }

        let rr = self.recent_ratio.unwrap();
        if rr < 0.0 || rr > 1.0 {
            return Err(CacheError::InvalidRecentRatio(rr));
        }

        let gr = self.ghost_ratio.unwrap();
        if gr < 0.0 || gr > 1.0 {
            return Err(CacheError::InvalidGhostRatio(gr));
        }

        // Determine the sub-sizes
        let rs = ((size as f64) * rr).floor() as usize;
        let es = ((size as f64) * gr).floor() as usize;

        // allocate the lrus

        let recent = RawLRU::with_hasher(size, self.recent_hasher.unwrap()).unwrap();
        let freq = RawLRU::with_hasher(size, self.freq_hasher.unwrap()).unwrap();

        let ghost = RawLRU::with_hasher(es, self.ghost_hasher.unwrap()).unwrap();

        Ok(TwoQueueCache {
            size,
            recent_size: rs,
            recent,
            frequent: freq,
            ghost,
        })
    }
}

/// `TwoQueueCache` is a fixed size 2Q cache.
/// 2Q is an enhancement over the standard LRU cache
/// in that it tracks both frequently and recently used
/// entries separately. This avoids a burst in access to new
/// entries from evicting frequently used entries. It adds some
/// additional tracking overhead to the [`RawLRU`] cache, and is
/// computationally about **2x** the cost, and adds some metadata over
/// head. The [`AdaptiveCache`] is similar to the TwoQueueCache, but does not require setting any
/// parameters.
///
/// [`RawLRU`]: struct.RawLRU.html
/// [`AdaptiveCache`]: struct.AdaptiveCache.html
pub struct TwoQueueCache<
    K: Hash + Eq,
    V,
    RH = DefaultHashBuilder,
    FH = DefaultHashBuilder,
    GH = DefaultHashBuilder,
> {
    size: usize,
    recent_size: usize,
    recent: RawLRU<K, V, DefaultEvictCallback, RH>,
    frequent: RawLRU<K, V, DefaultEvictCallback, FH>,
    ghost: RawLRU<K, V, DefaultEvictCallback, GH>,
}

impl<K: Hash + Eq, V> TwoQueueCache<K, V> {
    /// Create a `TwoQueueCache` with size and default configurations.
    pub fn new(size: usize) -> Result<Self, CacheError> {
        Self::with_2q_parameters(size, DEFAULT_2Q_RECENT_RATIO, DEFAULT_2Q_GHOST_RATIO)
    }

    /// Returns a [`TwoQueueCacheBuilder`] to help build a [`TwoQueueCache`].
    ///
    /// # Example
    /// ```rust
    /// use hashicorp_lru::{TwoQueueCacheBuilder, TwoQueueCache};
    /// use rustc_hash::FxHasher;
    /// use std::hash::BuildHasherDefault;
    ///
    /// let mut cache = TwoQueueCache::<u64, u64>::builder(3)
    ///     .set_recent_ratio(0.3)
    ///     .set_ghost_ratio(0.4)
    ///     .set_recent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_frequent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_ghost_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .finalize::<u64, u64>()
    ///     .unwrap();
    ///
    /// cache.put(1, 1);
    /// ```
    ///
    /// [`TwoQueueCacheBuilder`]: struct.TwoQueueCacheBuilder.html
    /// [`TwoQueueCache`]: struct.TwoQueueCache.html
    pub fn builder(size: usize) -> TwoQueueCacheBuilder {
        TwoQueueCacheBuilder::new(size)
    }

    /// Create a cache with size and recent ratio.
    ///
    /// # Example
    ///
    /// ```rust
    /// use hashicorp_lru::TwoQueueCache;
    ///
    /// let mut cache: TwoQueueCache<u64, u64>= TwoQueueCache::with_recent_ratio(5, 0.3).unwrap();
    /// ```
    pub fn with_recent_ratio(size: usize, rr: f64) -> Result<Self, CacheError> {
        Self::with_2q_parameters(size, rr, DEFAULT_2Q_GHOST_RATIO)
    }

    /// Create a cache with size and ghost ratio.
    ///
    /// # Example
    ///
    /// ```rust
    /// use hashicorp_lru::TwoQueueCache;
    ///
    /// let mut cache: TwoQueueCache<u64, u64>= TwoQueueCache::with_ghost_ratio(5, 0.6).unwrap();
    /// ```
    pub fn with_ghost_ratio(size: usize, gr: f64) -> Result<Self, CacheError> {
        Self::with_2q_parameters(size, DEFAULT_2Q_RECENT_RATIO, gr)
    }

    /// Create a cache with size, recent ratio and ghost ratio
    ///
    /// # Example
    ///
    /// ```rust
    /// use hashicorp_lru::TwoQueueCache;
    ///
    /// let mut cache: TwoQueueCache<u64, u64>= TwoQueueCache::with_2q_parameters(5, 0.3, 0.6).unwrap();
    /// ```
    pub fn with_2q_parameters(size: usize, rr: f64, gr: f64) -> Result<Self, CacheError> {
        if size == 0 {
            return Err(CacheError::InvalidSize(size));
        }

        if rr < 0.0 || rr > 1.0 {
            return Err(CacheError::InvalidRecentRatio(rr));
        }

        if gr < 0.0 || gr > 1.0 {
            return Err(CacheError::InvalidGhostRatio(gr));
        }

        // Determine the sub-sizes
        let rs = ((size as f64) * rr).floor() as usize;
        let es = ((size as f64) * gr).floor() as usize;

        // allocate the lrus
        let recent = RawLRU::new(size).unwrap();
        let freq = RawLRU::new(size).unwrap();

        let ghost = RawLRU::new(es)?;

        Ok(Self {
            size,
            recent_size: rs,
            recent,
            frequent: freq,
            ghost,
        })
    }
}

impl<K: Hash + Eq, V, RH: BuildHasher, FH: BuildHasher, GH: BuildHasher>
    TwoQueueCache<K, V, RH, FH, GH>
{
    /// Create a [`TwoQueueCache`] from [`TwoQueueCacheBuilder`].
    ///
    /// # Example
    /// ```rust
    /// use hashicorp_lru::{TwoQueueCacheBuilder, TwoQueueCache};
    /// use rustc_hash::FxHasher;
    /// use std::hash::BuildHasherDefault;
    ///
    /// let builder = TwoQueueCacheBuilder::new(5)
    ///     .set_recent_ratio(0.3)
    ///     .set_ghost_ratio(0.4)
    ///     .set_recent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_frequent_hasher(BuildHasherDefault::<FxHasher>::default())
    ///     .set_ghost_hasher(BuildHasherDefault::<FxHasher>::default());
    ///
    /// let mut cache = TwoQueueCache::from_builder(builder).unwrap();
    /// cache.put(1, 1);
    /// ```
    ///
    /// [`TwoQueueCacheBuilder`]: struct.TwoQueueCacheBuilder.html
    /// [`TwoQueueCache`]: struct.TwoQueueCache.html
    pub fn from_builder(builder: TwoQueueCacheBuilder<RH, FH, GH>) -> Result<Self, CacheError> {
        builder.finalize()
    }

    /// Puts a key-value pair to the cache.
    ///
    /// # Note
    /// - [`TwoQueueCache`] guarantees that the size of the recent LRU plus the size of the freq LRU
    /// is less or equal to the [`TwoQueueCache`]'s size.
    /// - The ghost LRU has its own size.
    ///
    /// # Example
    /// ```rust
    /// use hashicorp_lru::{TwoQueueCache, PutResult};
    ///
    /// let mut cache = TwoQueueCache::new(4).unwrap();
    /// // Add 1,2,3,4,5 -> Evict 1
    /// cache.put(1, 1);
    /// cache.put(2, 2);
    /// cache.put(3, 3);
    /// cache.put(4, 4);
    /// cache.put(5, 5);
    ///
    /// // Pull in the recently evicted
    /// assert_eq!(cache.put(1, 1), PutResult::Update(1));
    ///
    /// // Add 6, should cause another recent evict
    /// assert_eq!(cache.put(6, 6), PutResult::Put);
    ///
    /// // Add 7, should evict an entry from ghost LRU.
    /// assert_eq!(cache.put(7, 7), PutResult::Evicted { key: 2, value: 2});
    ///
    /// // Add 2, should evict an entry from ghost LRU
    /// assert_eq!(cache.put(2, 11), PutResult::Evicted { key: 3, value: 3});
    ///
    /// // Add 4, should put the entry from ghost LRU to freq LRU
    /// assert_eq!(cache.put(4, 11), PutResult::Update(4));
    ///
    /// // move all entry in recent to freq.
    /// assert_eq!(cache.put(2, 22), PutResult::Update(11));
    /// assert_eq!(cache.put(7, 77), PutResult::Update(7));
    ///
    /// // Add 6, should put the entry from ghost LRU to freq LRU, and evicted one
    /// // entry
    /// assert_eq!(cache.put(6, 66), PutResult::EvictedAndUpdate { evicted: (5, 5), update: 6 });
    /// ```
    ///
    /// [`TwoQueueCache`]: struct.TwoQueueCache.html
    pub fn put(&mut self, k: K, mut v: V) -> PutResult<K, V> {
        let key_ref = KeyRef { k: &k };

        // Check if the value is frequently used already,
        // and just update the value
        match self.frequent.map.get_mut(&key_ref).map(|node| {
            let node_ptr: *mut EntryNode<K, V> = &mut **node;
            node_ptr
        }) {
            None => {}
            Some(ent_ptr) => {
                self.frequent.update(&mut v, ent_ptr);
                return PutResult::Update(v);
            }
        }

        // Check if the value is recently used, and promote
        // the value into the frequent list
        if self.recent.contains(&key_ref) {
            // here we remove one entry
            let mut ent = self.recent.map.remove(&key_ref).unwrap();
            let ent_ptr = ent.as_mut();
            self.recent.detach(ent_ptr);
            unsafe {
                mem::swap(&mut v, &mut (*(*ent_ptr).val.as_mut_ptr()) as &mut V);
            }
            self.frequent.put_box(ent);
            return PutResult::Update(v);
        }

        // if we have space, nothing to do
        let recent_len = self.recent.len();
        let freq_len = self.frequent.len();

        // If the value was recently evicted, add it to the
        // frequently used list
        if self.ghost.contains(&key_ref) {
            return if recent_len + freq_len >= self.size {
                let ent = if recent_len > self.recent_size {
                    self.recent.remove_lru_in().unwrap()
                } else {
                    self.frequent.remove_lru_in().unwrap()
                };

                let rst = self.ghost.put_or_evict_box(ent);
                match self.ghost.map.remove(&key_ref) {
                    None => match rst {
                        None => PutResult::Put,
                        Some(mut ent) => {
                            let ent_ptr = ent.as_mut();
                            unsafe {
                                mem::swap(&mut v, &mut (*(*ent_ptr).val.as_mut_ptr()) as &mut V);
                            }
                            self.frequent.put_box(ent);
                            PutResult::Update(v)
                        }
                    },
                    Some(mut ent) => {
                        let ent_ptr = ent.as_mut();
                        self.ghost.detach(ent_ptr);

                        unsafe {
                            mem::swap(&mut v, &mut (*(*ent_ptr).val.as_mut_ptr()) as &mut V);
                            self.frequent.put_box(ent);
                            match rst {
                                None => PutResult::Update(v),
                                Some(ent) => PutResult::EvictedAndUpdate {
                                    evicted: (ent.key.assume_init(), ent.val.assume_init()),
                                    update: v,
                                },
                            }
                        }
                    }
                }
            } else {
                let mut ent = self.ghost.map.remove(&key_ref).unwrap();
                let ent_ptr = ent.as_mut();
                self.ghost.detach(ent_ptr);
                unsafe {
                    mem::swap(&mut v, &mut (*(*ent_ptr).val.as_mut_ptr()) as &mut V);
                }
                self.frequent.put_box(ent);
                PutResult::Update(v)
            };
        }

        // Add to the recently seen list.
        let bks = Box::new(EntryNode::new(k, v));
        // if we have enough space, we add entry to recent LRU directly
        if freq_len + recent_len < self.size {
            return match self.recent.put_or_evict_box(bks) {
                None => PutResult::Put,
                Some(evicted) => self.ghost.put_box(evicted),
            };
        }

        // The cache does not have enough space, so we remove one entry from freq LRU or recent
        // LRU. Then, put the removed entry to the front of the ghost LRU,
        // if ghost LRU is also full, the cache will evict the less recent used entry of
        // ghost LRU.
        let ent = if recent_len >= self.recent_size {
            self.recent.remove_lru_in().unwrap()
        } else {
            self.frequent.remove_lru_in().unwrap()
        };

        self.recent.put_box(bks);
        self.ghost.put_box(ent)
    }

    /// Returns a mutable reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Moves the key to the head of the LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::TwoQueueCache;
    /// let mut cache = TwoQueueCache::new(2).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get(&"banana"), Some(&6));
    /// ```
    pub fn get<'a, Q>(&'a mut self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        // Check if this is a frequent value
        self.frequent
            .get(k)
            .or_else(move || match self.recent.remove_and_return_ent(k) {
                None => None,
                Some(ent) => {
                    let _ = self.frequent.put_box(ent);
                    self.frequent.peek(k)
                }
            })
    }

    /// Returns a mutable reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Moves the key to the head of the LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::TwoQueueCache;
    /// let mut cache = TwoQueueCache::new(2).unwrap();
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
    pub fn get_mut<'a, Q>(&'a mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        // Check if this is a frequent value
        self.frequent
            .get_mut(k)
            .or_else(|| match self.recent.remove_and_return_ent(k) {
                None => None,
                Some(ent) => {
                    let _ = self.frequent.put_box(ent);
                    self.frequent.peek_mut(k)
                }
            })
    }

    /// Returns a reference to the value corresponding to the key in the cache or `None` if it is
    /// not present in the cache. Unlike `get`, `peek` does not update the LRU list so the key's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::TwoQueueCache;
    /// let mut cache = TwoQueueCache::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek(&1), Some(&"a"));
    /// assert_eq!(cache.peek(&2), Some(&"b"));
    /// ```
    pub fn peek<'a, Q>(&'a self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.frequent.peek(k).or_else(|| self.recent.peek(k))
    }

    /// Returns a mutable reference to the value corresponding to the key in the cache or `None`
    /// if it is not present in the cache. Unlike `get_mut`, `peek_mut` does not update the LRU
    /// list so the key's position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::TwoQueueCache;
    /// let mut cache = TwoQueueCache::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.peek_mut(&2), Some(&mut "b"));
    /// ```
    pub fn peek_mut<'a, Q>(&'a mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.frequent
            .peek_mut(k)
            .or_else(|| self.recent.peek_mut(k))
    }

    /// Removes and returns the value corresponding to the key from the cache or
    /// `None` if it does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::TwoQueueCache;
    /// let mut cache = TwoQueueCache::new(2).unwrap();
    ///
    /// cache.put(2, "a");
    ///
    /// assert_eq!(cache.remove(&1), None);
    /// assert_eq!(cache.remove(&2), Some("a"));
    /// assert_eq!(cache.remove(&2), None);
    /// assert_eq!(cache.len(), 0);
    /// ```
    pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.frequent
            .remove(k)
            .or_else(|| self.recent.remove(k))
            .or_else(|| self.ghost.remove(k))
    }

    /// Returns a bool indicating whether the given key is in the cache. Does not update the
    /// LRU list.
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::TwoQueueCache;
    /// let mut cache = TwoQueueCache::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    ///
    /// assert!(!cache.contains(&1));
    /// assert!(cache.contains(&2));
    /// assert!(cache.contains(&3));
    /// ```
    pub fn contains<Q>(&self, k: &Q) -> bool
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.frequent.contains(k) || self.recent.contains(k)
    }

    /// Clears the contents of the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::TwoQueueCache;
    /// let mut cache: TwoQueueCache<isize, &str> = TwoQueueCache::new(2).unwrap();
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
    pub fn purge(&mut self) {
        self.frequent.purge();
        self.recent.purge();
        self.ghost.purge();
    }

    /// Returns the number of key-value pairs that are currently in the the cache
    /// (excluding the length of inner ghost LRU).
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::TwoQueueCache;
    /// let mut cache = TwoQueueCache::new(2).unwrap();
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
    pub fn len(&self) -> usize {
        self.recent.len() + self.frequent.len()
    }

    /// Returns the maximum number of key-value pairs the cache can hold
    /// (excluding the capacity of inner ghost LRU).
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::TwoQueueCache;
    /// let mut cache: TwoQueueCache<isize, &str> = TwoQueueCache::new(2).unwrap();
    /// assert_eq!(cache.cap(), 2);
    /// ```
    pub fn cap(&self) -> usize {
        self.size
    }
}

impl<K: Hash + Eq, V, RH: BuildHasher, FH: BuildHasher, GH: BuildHasher> fmt::Debug
    for TwoQueueCache<K, V, RH, FH, GH>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TwoQueueCache")
            .field("len", &self.len())
            .field("cap", &self.cap())
            .finish()
    }
}

#[cfg(test)]
mod test {
    use crate::two_queue::TwoQueueCache;
    use crate::{CacheError, PutResult};
    use alloc::vec::Vec;
    use rand::seq::SliceRandom;
    use rand::{thread_rng, Rng};
    use std::format;

    #[test]
    fn test_2q_cache_random_ops() {
        let size = 128;
        let mut rng = thread_rng();
        let mut cases: Vec<u64> = (0..200_000).collect();
        cases.shuffle(&mut rng);

        let mut cache = TwoQueueCache::new(size).unwrap();

        (0..200_000).for_each(|i| {
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

            assert!(
                cache.recent.len() + cache.frequent.len() <= size,
                "idx: {}, bad: recent: {} freq: {}",
                i,
                cache.recent.len(),
                cache.frequent.len()
            )
        })
    }

    #[test]
    fn test_cache_error() {
        let cache = TwoQueueCache::<usize, usize>::with_ghost_ratio(0, 3.0).unwrap_err();
        assert_eq!(CacheError::InvalidSize(0), cache);

        let cache = TwoQueueCache::<usize, usize>::with_ghost_ratio(3, 3.0).unwrap_err();
        assert_eq!(CacheError::InvalidGhostRatio(3.0), cache);

        let cache = TwoQueueCache::<usize, usize>::with_recent_ratio(3, 3.0).unwrap_err();
        assert_eq!(CacheError::InvalidRecentRatio(3.0), cache);
    }

    #[test]
    fn test_2q_cache_get_recent_to_freq() {
        let mut cache = TwoQueueCache::new(128).unwrap();
        (0..128).for_each(|i| {
            let _ = cache.put(i, i);
        });

        assert_eq!(cache.recent.len(), 128);
        assert_eq!(cache.frequent.len(), 0);

        (0..128).for_each(|i| {
            let v = cache.get(&i);
            assert_ne!(v, None, "missing: {}", i);
        });

        assert_eq!(cache.recent.len(), 0);
        assert_eq!(cache.frequent.len(), 128);
    }

    #[test]
    fn test_2q_cache_put_recent_to_freq() {
        let mut cache = TwoQueueCache::new(128).unwrap();

        // Add initially to recent
        cache.put(1, 1);
        assert_eq!(cache.recent.len(), 1, "bad {}", cache.recent.len());
        assert_eq!(cache.frequent.len(), 0, "bad {}", cache.frequent.len());

        // Add should upgrade to frequent
        cache.put(1, 1);
        assert_eq!(cache.recent.len(), 0, "bad {}", cache.recent.len());
        assert_eq!(cache.frequent.len(), 1, "bad {}", cache.frequent.len());

        // Add should remain in frequent
        cache.put(1, 1);
        assert_eq!(cache.recent.len(), 0, "bad {}", cache.recent.len());
        assert_eq!(cache.frequent.len(), 1, "bad {}", cache.frequent.len());
    }

    #[test]
    fn test_2q_cache_put() {
        let mut cache = TwoQueueCache::new(4).unwrap();

        // Add 1,2,3,4,5 -> Evict 1
        cache.put(1, 1);
        cache.put(2, 2);
        cache.put(3, 3);
        cache.put(4, 4);
        cache.put(5, 5);
        assert_eq!(cache.recent.len(), 4, "bad: {}", cache.recent.len());
        assert_eq!(cache.ghost.len(), 1, "bad: {}", cache.ghost.len());
        assert_eq!(cache.frequent.len(), 0, "bad: {}", cache.frequent.len());

        // Pull in the recently evicted
        assert_eq!(cache.put(1, 1), PutResult::Update(1));
        assert_eq!(cache.recent.len(), 3, "bad: {}", cache.recent.len());
        assert_eq!(cache.ghost.len(), 1, "bad: {}", cache.ghost.len());
        assert_eq!(cache.frequent.len(), 1, "bad: {}", cache.frequent.len());

        // Add 6, should cause another recent evict
        assert_eq!(
            format!("{:?}", cache.put(6, 6).clone()),
            format!("{:?}", PutResult::<i32, i32>::Put)
        );
        assert_eq!(cache.recent.len(), 3, "bad: {}", cache.recent.len());
        assert_eq!(cache.ghost.len(), 2, "bad: {}", cache.ghost.len());
        assert_eq!(cache.frequent.len(), 1, "bad: {}", cache.frequent.len());

        // Add 7, should evict an entry from ghost LRU.
        assert_eq!(cache.put(7, 7), PutResult::Evicted { key: 2, value: 2 });
        assert_eq!(cache.recent.len(), 3, "bad: {}", cache.recent.len());
        assert_eq!(cache.ghost.len(), 2, "bad: {}", cache.ghost.len());
        assert_eq!(cache.frequent.len(), 1, "bad: {}", cache.frequent.len());

        // Add 2, should evict an entry from ghost LRU
        assert_eq!(
            format!("{:?}", cache.put(2, 11).clone()),
            format!("{:?}", PutResult::Evicted { key: 3, value: 3 })
        );
        assert_eq!(cache.recent.len(), 3, "bad: {}", cache.recent.len());
        assert_eq!(cache.ghost.len(), 2, "bad: {}", cache.ghost.len());
        assert_eq!(cache.frequent.len(), 1, "bad: {}", cache.frequent.len());

        // Add 4, should put the entry from ghost LRU to freq LRU
        assert_eq!(cache.put(4, 11), PutResult::Update(4));
        assert_eq!(cache.recent.len(), 2, "bad: {}", cache.recent.len());
        assert_eq!(cache.ghost.len(), 2, "bad: {}", cache.ghost.len());
        assert_eq!(cache.frequent.len(), 2, "bad: {}", cache.frequent.len());

        // move all entry in recent to freq.
        assert_eq!(cache.put(2, 22).clone(), PutResult::Update(11));
        assert_eq!(cache.recent.len(), 1, "bad: {}", cache.recent.len());
        assert_eq!(cache.ghost.len(), 2, "bad: {}", cache.ghost.len());
        assert_eq!(cache.frequent.len(), 3, "bad: {}", cache.frequent.len());

        assert_eq!(
            format!("{:?}", cache.put(7, 77)),
            format!("{:?}", PutResult::<i32, i32>::Update(7))
        );
        assert_eq!(cache.recent.len(), 0, "bad: {}", cache.recent.len());
        assert_eq!(cache.ghost.len(), 2, "bad: {}", cache.ghost.len());
        assert_eq!(cache.frequent.len(), 4, "bad: {}", cache.frequent.len());

        // Add 6, should put the entry from ghost LRU to freq LRU, and evicted one
        // entry
        assert_eq!(
            format!("{:?}", cache.put(6, 66).clone()),
            format!(
                "{:?}",
                PutResult::EvictedAndUpdate {
                    evicted: (5, 5),
                    update: 6
                }
            )
        );
        assert_eq!(cache.recent.len(), 0, "bad: {}", cache.recent.len());
        assert_eq!(cache.ghost.len(), 1, "bad: {}", cache.ghost.len());
        assert_eq!(cache.frequent.len(), 4, "bad: {}", cache.frequent.len());
    }

    #[test]
    fn test_2q_cache() {
        let mut cache = TwoQueueCache::new(128).unwrap();

        (0..256u64).for_each(|i| {
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
        let mut cache = TwoQueueCache::new(2).unwrap();
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
    fn test_2q_cache_peek() {
        let mut cache = TwoQueueCache::new(2).unwrap();
        cache.put(1, 1);
        cache.put(2, 2);

        assert_eq!(cache.peek(&1), Some(&1));
        cache.put(3, 3);
        assert!(!cache.contains(&1));
    }
}
