use crate::{
    CacheError, DefaultEvictCallback, DefaultHashBuilder, PutResult, RawLRU, TwoQueueCacheBuilder,
};
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
    /// use hashicorp_lru::{AdaptiveCacheBuilder, AdaptiveCache};
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
    /// use hashicorp_lru::AdaptiveCacheBuilder;
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
/// additional tracking overhead to a standard LRU cache, computationally
/// it is roughly 2x the cost, and the extra memory overhead is linear
/// with the size of the cache. ARC has been patented by IBM, but is
/// similar to the `TwoQueueCache` (2Q) which requires setting parameters.
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
    /// use hashicorp_lru::{AdaptiveCacheBuilder, AdaptiveCache};
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
    AdaptiveCache<K, V, RH, REH, FH, FEH>
{
    /// Create a [`AdaptiveCache`] from [`AdaptiveCacheBuilder`].
    ///
    /// # Example
    /// ```rust
    /// use hashicorp_lru::{AdaptiveCacheBuilder, AdaptiveCache};
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

    /// Puts a key-value pair to the cache.
    ///
    pub fn put(&mut self, k: K, v: V) -> PutResult<K, V> {
        PutResult::Put
    }
}
