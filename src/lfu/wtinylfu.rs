mod error;
pub use error::WTinyLFUError;

use crate::lfu::{
    tinylfu::{TinyLFU, TinyLFUBuilder, TinyLFUError, DEFAULT_FALSE_POSITIVE_RATIO},
    DefaultKeyHasher, KeyHasher,
};
use crate::lru::{SegmentedCache, SegmentedCacheBuilder};
use crate::{Cache, DefaultHashBuilder, LRUCache, PutResult};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::marker::PhantomData;

const DEFAULT_WINDOW_CACHE_SIZE_RATIO: f64 = 0.01;
const DEFAULT_HOT_ITEMS_CACHE_SIZE_RATIO: f64 = 0.80;

/// `WTinyLFUCacheBuilder` is used to help build a [`TinyLFUCache`] with custom configurations.
///
/// [`TinyLFUCache`]: struct.TinyLFUCache.html
pub struct WTinyLFUCacheBuilder<
    K,
    KH = DefaultKeyHasher<K>,
    FH = DefaultHashBuilder,
    RH = DefaultHashBuilder,
    WH = DefaultHashBuilder,
> {
    samples: usize,
    window_cache_size: usize,
    main_cache_protected_size: usize,
    main_cache_probationary_size: usize,
    window_cache_hasher: Option<WH>,
    key_hasher: Option<KH>,
    main_cache_protected_hasher: Option<FH>,
    main_cache_probationary_hasher: Option<RH>,
    false_positive_ratio: Option<f64>,
    marker: PhantomData<K>,
}

impl<
        K: Hash + Eq,
        KH: KeyHasher<K> + Default,
        FH: BuildHasher + Default,
        RH: BuildHasher + Default,
        WH: BuildHasher + Default,
    > Default for WTinyLFUCacheBuilder<K, KH, FH, RH, WH>
{
    fn default() -> Self {
        Self {
            samples: 0,
            window_cache_size: 0,
            main_cache_protected_size: 0,
            main_cache_probationary_size: 0,
            window_cache_hasher: Some(WH::default()),
            main_cache_protected_hasher: Some(FH::default()),
            main_cache_probationary_hasher: Some(RH::default()),
            key_hasher: Some(KH::default()),
            false_positive_ratio: Some(DEFAULT_FALSE_POSITIVE_RATIO),
            marker: Default::default(),
        }
    }
}

impl<
        K: Hash + Eq,
        KH: KeyHasher<K> + Default,
        FH: BuildHasher + Default,
        RH: BuildHasher + Default,
        WH: BuildHasher + Default,
    > WTinyLFUCacheBuilder<K, KH, FH, RH, WH>
{
    /// The constructor of WTinyLFUCacheBuilder
    pub fn new(
        window_cache_size: usize,
        protected_cache_size: usize,
        probationary_cache_size: usize,
        samples: usize,
    ) -> Self {
        Self::default()
            .set_samples(samples)
            .set_window_cache_size(window_cache_size)
            .set_protected_cache_size(protected_cache_size)
            .set_probationary_cache_size(probationary_cache_size)
    }
}

impl<K: Hash + Eq, KH: KeyHasher<K>, FH: BuildHasher, RH: BuildHasher, WH: BuildHasher>
    WTinyLFUCacheBuilder<K, KH, FH, RH, WH>
{
    /// Construct a WTinyLFUCacheBuilder using the custom hashers.
    pub fn with_hashers(
        key_hasher: KH,
        protected_hasher: FH,
        probationary_hasher: RH,
        window_hasher: WH,
    ) -> Self {
        Self {
            samples: 0,
            window_cache_size: 0,
            main_cache_protected_size: 0,
            main_cache_probationary_size: 0,
            window_cache_hasher: Some(window_hasher),
            main_cache_protected_hasher: Some(protected_hasher),
            main_cache_probationary_hasher: Some(probationary_hasher),
            key_hasher: Some(key_hasher),
            false_positive_ratio: Some(DEFAULT_FALSE_POSITIVE_RATIO),
            marker: Default::default(),
        }
    }

    /// Set the samples of TinyLFU
    pub fn set_samples(self, samples: usize) -> Self {
        Self {
            samples,
            window_cache_size: self.window_cache_size,
            main_cache_protected_size: self.main_cache_protected_size,
            main_cache_probationary_size: self.main_cache_probationary_size,
            window_cache_hasher: self.window_cache_hasher,
            key_hasher: self.key_hasher,
            main_cache_protected_hasher: self.main_cache_protected_hasher,
            main_cache_probationary_hasher: self.main_cache_probationary_hasher,
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Set the window cache size
    pub fn set_window_cache_size(self, sz: usize) -> Self {
        Self {
            samples: self.samples,
            window_cache_size: sz,
            main_cache_protected_size: self.main_cache_protected_size,
            main_cache_probationary_size: self.main_cache_probationary_size,
            window_cache_hasher: self.window_cache_hasher,
            main_cache_protected_hasher: self.main_cache_protected_hasher,
            main_cache_probationary_hasher: self.main_cache_probationary_hasher,
            key_hasher: self.key_hasher,
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Set the protected cache size
    pub fn set_protected_cache_size(self, sz: usize) -> Self {
        Self {
            samples: self.samples,
            window_cache_size: self.window_cache_size,
            main_cache_protected_size: sz,
            main_cache_probationary_size: self.main_cache_probationary_size,
            window_cache_hasher: self.window_cache_hasher,
            main_cache_protected_hasher: self.main_cache_protected_hasher,
            main_cache_probationary_hasher: self.main_cache_probationary_hasher,
            key_hasher: self.key_hasher,
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Set the probationary cache size
    pub fn set_probationary_cache_size(self, sz: usize) -> Self {
        Self {
            samples: self.samples,
            window_cache_size: self.window_cache_size,
            main_cache_protected_size: self.main_cache_protected_size,
            main_cache_probationary_size: sz,
            window_cache_hasher: self.window_cache_hasher,
            main_cache_protected_hasher: self.main_cache_protected_hasher,
            main_cache_probationary_hasher: self.main_cache_probationary_hasher,
            key_hasher: self.key_hasher,
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Set the false positive ratio of TinyLFU
    pub fn set_false_positive_ratio(self, fpr: f64) -> Self {
        Self {
            samples: self.samples,
            window_cache_size: self.window_cache_size,
            main_cache_protected_size: self.main_cache_protected_size,
            main_cache_probationary_size: self.main_cache_probationary_size,
            window_cache_hasher: self.window_cache_hasher,
            main_cache_protected_hasher: self.main_cache_protected_hasher,
            main_cache_probationary_hasher: self.main_cache_probationary_hasher,
            key_hasher: self.key_hasher,
            false_positive_ratio: Some(fpr),
            marker: self.marker,
        }
    }

    /// Set the window cache's hash builder
    pub fn set_window_hasher<NWH: BuildHasher>(
        self,
        hasher: NWH,
    ) -> WTinyLFUCacheBuilder<K, KH, FH, RH, NWH> {
        WTinyLFUCacheBuilder {
            samples: self.samples,
            window_cache_size: self.window_cache_size,
            main_cache_protected_size: self.main_cache_protected_size,
            main_cache_probationary_size: self.main_cache_probationary_size,
            window_cache_hasher: Some(hasher),
            main_cache_protected_hasher: self.main_cache_protected_hasher,
            main_cache_probationary_hasher: self.main_cache_probationary_hasher,
            key_hasher: self.key_hasher,
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Set the protected cache's hash builder
    pub fn set_protected_hasher<NFH: BuildHasher>(
        self,
        hasher: NFH,
    ) -> WTinyLFUCacheBuilder<K, KH, NFH, RH, WH> {
        WTinyLFUCacheBuilder {
            samples: self.samples,
            window_cache_size: self.window_cache_size,
            main_cache_protected_size: self.main_cache_protected_size,
            main_cache_probationary_size: self.main_cache_probationary_size,
            window_cache_hasher: self.window_cache_hasher,
            main_cache_protected_hasher: Some(hasher),
            main_cache_probationary_hasher: self.main_cache_probationary_hasher,
            key_hasher: self.key_hasher,
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Set the probationary cache's hash builder
    pub fn set_probationary_hasher<NRH: BuildHasher>(
        self,
        hasher: NRH,
    ) -> WTinyLFUCacheBuilder<K, KH, FH, NRH, WH> {
        WTinyLFUCacheBuilder {
            samples: self.samples,
            window_cache_size: self.window_cache_size,
            main_cache_protected_size: self.main_cache_protected_size,
            main_cache_probationary_size: self.main_cache_probationary_size,
            window_cache_hasher: self.window_cache_hasher,
            main_cache_protected_hasher: self.main_cache_protected_hasher,
            key_hasher: self.key_hasher,
            main_cache_probationary_hasher: Some(hasher),
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Set the key hasher
    pub fn set_key_hasher<NKH: KeyHasher<K>>(
        self,
        hasher: NKH,
    ) -> WTinyLFUCacheBuilder<K, NKH, FH, RH, WH> {
        WTinyLFUCacheBuilder {
            samples: self.samples,
            window_cache_size: self.window_cache_size,
            main_cache_protected_size: self.main_cache_protected_size,
            main_cache_probationary_size: self.main_cache_probationary_size,
            window_cache_hasher: self.window_cache_hasher,
            main_cache_protected_hasher: self.main_cache_protected_hasher,
            key_hasher: Some(hasher),
            main_cache_probationary_hasher: self.main_cache_probationary_hasher,
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Finalize the builder to [`TinyLFUCache`]
    ///
    /// [`TinyLFUCache`]: struct.TinyLFUCache.html
    pub fn finalize<V>(self) -> Result<WTinyLFUCache<K, V, KH, FH, RH, WH>, WTinyLFUError>
    where
        K: Eq,
    {
        if self.window_cache_size == 0 {
            return Err(WTinyLFUError::InvalidWindowCacheSize(0));
        }

        if self.main_cache_protected_size == 0 {
            return Err(WTinyLFUError::InvalidProtectedCacheSize(0));
        }

        if self.main_cache_probationary_size == 0 {
            return Err(WTinyLFUError::InvalidProbationaryCacheSize(0));
        }

        if self.samples == 0 {
            return Err(WTinyLFUError::InvalidSamples(self.samples));
        }

        let fp_ratio = self.false_positive_ratio.unwrap();
        if fp_ratio <= 0.0 || fp_ratio >= 1.0 {
            return Err(WTinyLFUError::InvalidFalsePositiveRatio(fp_ratio));
        }

        let lru = LRUCache::with_hasher(self.window_cache_size, self.window_cache_hasher.unwrap())
            .unwrap();

        let slru = SegmentedCacheBuilder::new(
            self.main_cache_probationary_size,
            self.main_cache_protected_size,
        )
        .set_probationary_hasher(self.main_cache_probationary_hasher.unwrap())
        .set_protected_hasher(self.main_cache_protected_hasher.unwrap())
        .finalize()
        .unwrap();

        let size = self.window_cache_size
            + self.main_cache_protected_size
            + self.main_cache_probationary_size;

        let tinylfu = TinyLFUBuilder::new(size, self.samples)
            .set_key_hasher(self.key_hasher.unwrap())
            .set_false_positive_ratio(fp_ratio)
            .finalize()
            .map_err(|e| match e {
                TinyLFUError::InvalidCountMinWidth(v) => WTinyLFUError::InvalidCountMinWidth(v),
                TinyLFUError::InvalidSamples(v) => WTinyLFUError::InvalidSamples(v),
                TinyLFUError::InvalidFalsePositiveRatio(v) => {
                    WTinyLFUError::InvalidFalsePositiveRatio(v)
                }
            })?;

        Ok(WTinyLFUCache { tinylfu, lru, slru })
    }
}

/// WTinyLFUCache implements the W-TinyLFU, based on the paper [TinyLFU: A Highly Efficient Cache Admission Policy]
///
///
/// # Example
/// ```rust
/// use caches::{WTinyLFUCache, PutResult, Cache};
///
/// let mut cache = WTinyLFUCache::with_sizes(1, 2, 2, 5).unwrap();
/// assert_eq!(cache.cap(), 5);
/// assert_eq!(cache.window_cache_cap(), 1);
/// assert_eq!(cache.main_cache_cap(), 4);
///
/// assert_eq!(cache.put(1, 1), PutResult::Put);
/// assert!(cache.contains(&1));
/// assert_eq!(cache.put(2, 2), PutResult::Put);
/// assert!(cache.contains(&2));
/// assert_eq!(cache.put(3, 3), PutResult::Put);
/// assert!(cache.contains(&3));
///
/// // current state
/// // window cache:        (MRU) [3] (LRU)
/// // probationary cache:  (MRU) [2, 1] (LRU)
/// // protected cache:     (MRU) [] (LRU)
/// assert_eq!(cache.window_cache_len(), 1);
/// assert_eq!(cache.main_cache_len(), 2);
///
/// assert_eq!(cache.put(2, 22), PutResult::Update(2));
/// assert_eq!(cache.put(1, 11), PutResult::Update(1));
///
/// // current state
/// // window cache:        (MRU) [3] (LRU)
/// // probationary cache:  (MRU) [] (LRU)
/// // protected cache:     (MRU) [1, 2] (LRU)
/// assert_eq!(cache.window_cache_len(), 1);
///
/// assert_eq!(cache.put(3, 33), PutResult::Update(3));
///
/// // current state
/// // window cache:        (MRU) [2] (LRU)
/// // probationary cache:  (MRU) [] (LRU)
/// // protected cache:     (MRU) [3, 1] (LRU)
/// assert_eq!(cache.window_cache_len(), 1);
///
/// assert_eq!(cache.put(4, 4), PutResult::Put);
/// assert_eq!(cache.put(5, 5), PutResult::Put);
///
/// // current state
/// // window cache:        (MRU) [5] (LRU)
/// // probationary cache:  (MRU) [4, 2] (LRU)
/// // protected cache:     (MRU) [3, 1] (LRU)
///
/// assert_eq!(cache.get(&4), Some(&4));
/// assert_eq!(cache.get_mut(&5), Some(&mut 5));
///
/// // current state
/// // window cache:        (MRU) [5] (LRU)
/// // probationary cache:  (MRU) [1, 2] (LRU)
/// // protected cache:     (MRU) [4, 3] (LRU)
/// assert_eq!(cache.peek(&3), Some(&33));
/// assert_eq!(cache.peek_mut(&2), Some(&mut 22));
///
/// assert_eq!(cache.remove(&3), Some(33));
/// assert_eq!(cache.remove(&2), Some(22));
/// ```
///
/// [TinyLFU: A Highly Efficient Cache Admission Policy]: https://arxiv.org/pdf/1512.00727.pdf
pub struct WTinyLFUCache<
    K: Hash,
    V,
    KH = DefaultKeyHasher<K>,
    FH = DefaultHashBuilder,
    RH = DefaultHashBuilder,
    WH = DefaultHashBuilder,
> {
    tinylfu: TinyLFU<K, KH>,
    lru: LRUCache<K, V, WH>,
    slru: SegmentedCache<K, V, FH, RH>,
}

impl<K: Hash + Eq, V> WTinyLFUCache<K, V, DefaultKeyHasher<K>> {
    /// Returns a WTinyLFUCache based on the size and samples
    ///
    /// **NOTE:** the size is not the actual cache size,
    /// the actual size is calculated base on the size param.
    pub fn new(size: usize, samples: usize) -> Result<Self, WTinyLFUError> {
        let wsz = ((size as f64) * DEFAULT_WINDOW_CACHE_SIZE_RATIO) as usize;
        let hsz = ((size as f64) * DEFAULT_HOT_ITEMS_CACHE_SIZE_RATIO) as usize;
        let csz = ((size as f64) * (1f64 - DEFAULT_HOT_ITEMS_CACHE_SIZE_RATIO)) as usize;

        WTinyLFUCacheBuilder::new(wsz, hsz, csz, samples).finalize()
    }

    /// Returns a WTinyLFUCache based on the related cache sizes and samples
    ///
    /// # Note
    /// According to the [TinyLFU: A Highly Efficient Cache Admission Policy]
    ///
    /// [TinyLFU: A Highly Efficient Cache Admission Policy]: https://arxiv.org/pdf/1512.00727.pdf
    pub fn with_sizes(
        window_cache_size: usize,
        protected_cache_size: usize,
        probationary_cache_size: usize,
        samples: usize,
    ) -> Result<Self, WTinyLFUError> {
        WTinyLFUCacheBuilder::new(
            window_cache_size,
            protected_cache_size,
            probationary_cache_size,
            samples,
        )
        .finalize()
    }
}

impl<K: Hash + Eq, V, KH: KeyHasher<K>, FH: BuildHasher, RH: BuildHasher, WH: BuildHasher>
    WTinyLFUCache<K, V, KH, FH, RH, WH>
{
    /// Creates a WTinyLFUCache according to [`WTinyLFUCacheBuilder`]
    ///
    /// [`WTinyLFUCacheBuilder`]: struct.WTinyLFUCacheBuilder.html
    pub fn from_builder(
        builder: WTinyLFUCacheBuilder<K, KH, FH, RH, WH>,
    ) -> Result<Self, WTinyLFUError> {
        builder.finalize()
    }

    /// Returns a [`WTinyLFUCacheBuilder`] with default configurations.
    ///
    /// [`WTinyLFUCacheBuilder`]: struct.WTinyLFUCacheBuilder.html
    pub fn builder() -> WTinyLFUCacheBuilder<K> {
        WTinyLFUCacheBuilder::default()
    }

    ///
    pub fn window_cache_len(&self) -> usize {
        self.lru.len()
    }

    ///
    pub fn window_cache_cap(&self) -> usize {
        self.lru.cap()
    }

    ///
    pub fn main_cache_len(&self) -> usize {
        self.slru.len()
    }

    ///
    pub fn main_cache_cap(&self) -> usize {
        self.slru.cap()
    }
}

impl<K: Hash + Eq, V, KH: KeyHasher<K>, FH: BuildHasher, RH: BuildHasher, WH: BuildHasher>
    Cache<K, V> for WTinyLFUCache<K, V, KH, FH, RH, WH>
{
    /// Puts a key-value pair into cache, returns a [`PutResult`].
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, WTinyLFUCache};
    /// use caches::PutResult;
    /// let mut cache = WTinyLFUCache::with_sizes(1, 2, 2, 5).unwrap();
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
    fn put(&mut self, k: K, v: V) -> PutResult<K, V> {
        match self.lru.remove(&k) {
            None => {
                if self.slru.contains(&k) {
                    return self.slru.put(k, v);
                }

                match self.lru.put(k, v) {
                    PutResult::Put => PutResult::Put,
                    PutResult::Update(v) => PutResult::Update(v),
                    PutResult::Evicted { key, value } => {
                        if self.slru.len() < self.slru.cap() {
                            return self.slru.put(key, value);
                        }

                        match self.slru.peek_lru_from_probationary() {
                            None => self.slru.put(key, value),
                            Some((lruk, _)) => {
                                if self.tinylfu.lt(&key, lruk) {
                                    PutResult::Evicted { key, value }
                                } else {
                                    self.slru.put(key, value)
                                }
                            }
                        }
                    }
                    // this branch will never happen,
                    // we keep this for good measure.
                    _ => PutResult::Put,
                }
            }
            Some(old) => {
                if self.slru.protected_len() >= self.slru.protected_cap() {
                    let ent = self.slru.remove_lru_from_protected().unwrap();
                    self.lru.put(ent.0, ent.1);
                }

                self.slru.put_protected(k, v);
                PutResult::Update(old)
            }
        }
    }

    /// Returns a reference to the value of the key in the cache or `None`.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, WTinyLFUCache};
    /// let mut cache = WTinyLFUCache::with_sizes(1, 2, 2, 5).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get(&"banana"), Some(&6));
    /// ```
    fn get<Q>(&mut self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.tinylfu.try_reset();
        self.tinylfu.increment(k);

        match self.lru.get(k) {
            Some(v) => Some(v),
            None => self.slru.get(k),
        }
    }

    /// Returns a mutable reference to the value of the key in the cache or `None`.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, WTinyLFUCache};
    /// let mut cache = WTinyLFUCache::with_sizes(1, 2, 2, 5).unwrap();
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get_mut(&"banana"), Some(&mut 6));
    /// ```
    fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.tinylfu.try_reset();
        self.tinylfu.increment(k);
        match self.lru.get_mut(k) {
            Some(v) => Some(v),
            None => self.slru.get_mut(k),
        }
    }

    /// Returns a reference to the value corresponding to the key in the cache or `None` if it is
    /// not present in the cache. Unlike `get`, `peek` does not update the LRU list so the key's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, WTinyLFUCache};
    ///
    /// let mut cache = WTinyLFUCache::with_sizes(1, 2, 2, 5).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek(&1), Some(&"a"));
    /// assert_eq!(cache.peek(&2), Some(&"b"));
    /// ```
    fn peek<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.lru.peek(k).or_else(|| self.slru.peek(k))
    }

    /// Returns a mutable reference to the value corresponding to the key in the cache or `None`
    /// if it is not present in the cache. Unlike `get_mut`, `peek_mut` does not update the LRU
    /// list so the key's position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use caches::{Cache, WTinyLFUCache};
    ///
    /// let mut cache = WTinyLFUCache::with_sizes(1, 2, 2, 5).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.peek_mut(&2), Some(&mut "b"));
    /// ```
    fn peek_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.lru.peek_mut(k) {
            Some(v) => Some(v),
            None => self.slru.peek_mut(k),
        }
    }

    fn contains<Q>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.lru.contains(k) || self.slru.contains(k)
    }

    fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.lru.remove(k).or_else(|| self.slru.remove(k))
    }

    fn purge(&mut self) {
        self.lru.purge();
        self.slru.purge();
        self.tinylfu.clear();
    }

    fn len(&self) -> usize {
        self.lru.len() + self.slru.len()
    }

    fn cap(&self) -> usize {
        self.lru.cap() + self.slru.cap()
    }

    fn is_empty(&self) -> bool {
        self.lru.is_empty() && self.slru.is_empty()
    }
}

impl<
        K: Hash + Eq + Clone,
        V: Clone,
        KH: KeyHasher<K> + Clone,
        FH: BuildHasher + Clone,
        RH: BuildHasher + Clone,
        WH: BuildHasher + Clone,
    > Clone for WTinyLFUCache<K, V, KH, FH, RH, WH>
{
    fn clone(&self) -> Self {
        Self {
            tinylfu: self.tinylfu.clone(),
            lru: self.lru.clone(),
            slru: self.slru.clone(),
        }
    }
}

#[cfg(test)]
mod test {
    use core::hash::BuildHasher;

    use crate::lfu::tinylfu::test::{PassthroughU64Hasher, PassthroughU64KeyHasher};
    use crate::lfu::WTinyLFUCache;
    use crate::{Cache, PutResult, WTinyLFUCacheBuilder};

    #[derive(Default)]
    struct PassthroughBuilderU64Hasher {}

    impl BuildHasher for PassthroughBuilderU64Hasher {
        type Hasher = PassthroughU64Hasher;

        fn build_hasher(&self) -> Self::Hasher {
            Default::default()
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_wtinylfu_custom_hasher() {
        let mut cache: WTinyLFUCache<
            u64,
            u32,
            PassthroughU64KeyHasher,
            PassthroughBuilderU64Hasher,
            PassthroughBuilderU64Hasher,
            PassthroughBuilderU64Hasher,
        > = WTinyLFUCacheBuilder::default()
            .set_window_cache_size(1)
            .set_protected_cache_size(2)
            .set_probationary_cache_size(2)
            .set_samples(5)
            .finalize()
            .unwrap();
        assert_eq!(cache.cap(), 5);
        assert_eq!(cache.window_cache_cap(), 1);
        assert_eq!(cache.main_cache_cap(), 4);

        assert_eq!(cache.put(1, 1), PutResult::Put);
        assert!(cache.contains(&1));
        assert_eq!(cache.put(2, 2), PutResult::Put);
        assert!(cache.contains(&2));
        assert_eq!(cache.put(3, 3), PutResult::Put);
        assert!(cache.contains(&3));

        // current state
        // window cache:        (MRU) [3] (LRU)
        // probationary cache:  (MRU) [2, 1] (LRU)
        // protected cache:     (MRU) [] (LRU)
        assert_eq!(cache.window_cache_len(), 1);
        assert_eq!(cache.main_cache_len(), 2);

        assert_eq!(cache.put(2, 22), PutResult::Update(2));
        assert_eq!(cache.put(1, 11), PutResult::Update(1));

        // current state
        // window cache:        (MRU) [3] (LRU)
        // probationary cache:  (MRU) [] (LRU)
        // protected cache:     (MRU) [1, 2] (LRU)
        assert_eq!(cache.slru.peek_lru_from_protected(), Some((&2, &22)));
        assert_eq!(cache.slru.peek_mru_from_protected(), Some((&1, &11)));
        assert_eq!(cache.window_cache_len(), 1);
        assert_eq!(cache.slru.protected_len(), 2);
        assert_eq!(cache.slru.probationary_len(), 0);

        assert_eq!(cache.put(3, 33), PutResult::Update(3));

        // current state
        // window cache:        (MRU) [2] (LRU)
        // probationary cache:  (MRU) [] (LRU)
        // protected cache:     (MRU) [3, 1] (LRU)
        assert_eq!(cache.lru.peek_lru(), Some((&2, &22)));
        assert_eq!(cache.slru.peek_lru_from_protected(), Some((&1, &11)));
        assert_eq!(cache.slru.peek_mru_from_protected(), Some((&3, &33)));
        assert_eq!(cache.window_cache_len(), 1);
        assert_eq!(cache.slru.protected_len(), 2);
        assert_eq!(cache.slru.probationary_len(), 0);

        assert_eq!(cache.put(4, 4), PutResult::Put);
        assert_eq!(cache.put(5, 5), PutResult::Put);

        // current state
        // window cache:        (MRU) [5] (LRU)
        // probationary cache:  (MRU) [4, 2] (LRU)
        // protected cache:     (MRU) [3, 1] (LRU)
        assert_eq!(cache.lru.peek_lru(), Some((&5, &5)));
        assert_eq!(cache.slru.peek_lru_from_probationary(), Some((&2, &22)));
        assert_eq!(cache.slru.peek_mru_from_probationary(), Some((&4, &4)));
        assert_eq!(cache.lru.len(), 1);
        assert_eq!(cache.slru.protected_len(), 2);
        assert_eq!(cache.slru.probationary_len(), 2);

        assert_eq!(cache.get(&4), Some(&4));
        assert_eq!(cache.get_mut(&5), Some(&mut 5));

        // current state
        // window cache:        (MRU) [5] (LRU)
        // probationary cache:  (MRU) [1, 2] (LRU)
        // protected cache:     (MRU) [4, 3] (LRU)
        assert_eq!(cache.lru.peek_lru(), Some((&5, &5)));
        assert_eq!(cache.slru.peek_lru_from_probationary(), Some((&2, &22)));
        assert_eq!(cache.slru.peek_mru_from_probationary(), Some((&1, &11)));
        assert_eq!(cache.slru.peek_lru_from_protected(), Some((&3, &33)));
        assert_eq!(cache.slru.peek_mru_from_protected(), Some((&4, &4)));
        assert_eq!(cache.lru.len(), 1);
        assert_eq!(cache.slru.protected_len(), 2);
        assert_eq!(cache.slru.probationary_len(), 2);

        assert_eq!(cache.peek(&3), Some(&33));
        assert_eq!(cache.peek_mut(&2), Some(&mut 22));

        assert_eq!(cache.remove(&3), Some(33));
        assert_eq!(cache.remove(&2), Some(22));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_wtinylfu() {
        let mut cache = WTinyLFUCache::with_sizes(1, 2, 2, 5).unwrap();
        assert_eq!(cache.cap(), 5);
        assert_eq!(cache.window_cache_cap(), 1);
        assert_eq!(cache.main_cache_cap(), 4);

        assert_eq!(cache.put(1, 1), PutResult::Put);
        assert!(cache.contains(&1));
        assert_eq!(cache.put(2, 2), PutResult::Put);
        assert!(cache.contains(&2));
        assert_eq!(cache.put(3, 3), PutResult::Put);
        assert!(cache.contains(&3));

        // current state
        // window cache:        (MRU) [3] (LRU)
        // probationary cache:  (MRU) [2, 1] (LRU)
        // protected cache:     (MRU) [] (LRU)
        assert_eq!(cache.window_cache_len(), 1);
        assert_eq!(cache.main_cache_len(), 2);

        assert_eq!(cache.put(2, 22), PutResult::Update(2));
        assert_eq!(cache.put(1, 11), PutResult::Update(1));

        // current state
        // window cache:        (MRU) [3] (LRU)
        // probationary cache:  (MRU) [] (LRU)
        // protected cache:     (MRU) [1, 2] (LRU)
        assert_eq!(cache.slru.peek_lru_from_protected(), Some((&2, &22)));
        assert_eq!(cache.slru.peek_mru_from_protected(), Some((&1, &11)));
        assert_eq!(cache.window_cache_len(), 1);
        assert_eq!(cache.slru.protected_len(), 2);
        assert_eq!(cache.slru.probationary_len(), 0);

        assert_eq!(cache.put(3, 33), PutResult::Update(3));

        // current state
        // window cache:        (MRU) [2] (LRU)
        // probationary cache:  (MRU) [] (LRU)
        // protected cache:     (MRU) [3, 1] (LRU)
        assert_eq!(cache.lru.peek_lru(), Some((&2, &22)));
        assert_eq!(cache.slru.peek_lru_from_protected(), Some((&1, &11)));
        assert_eq!(cache.slru.peek_mru_from_protected(), Some((&3, &33)));
        assert_eq!(cache.window_cache_len(), 1);
        assert_eq!(cache.slru.protected_len(), 2);
        assert_eq!(cache.slru.probationary_len(), 0);

        assert_eq!(cache.put(4, 4), PutResult::Put);
        assert_eq!(cache.put(5, 5), PutResult::Put);

        // current state
        // window cache:        (MRU) [5] (LRU)
        // probationary cache:  (MRU) [4, 2] (LRU)
        // protected cache:     (MRU) [3, 1] (LRU)
        assert_eq!(cache.lru.peek_lru(), Some((&5, &5)));
        assert_eq!(cache.slru.peek_lru_from_probationary(), Some((&2, &22)));
        assert_eq!(cache.slru.peek_mru_from_probationary(), Some((&4, &4)));
        assert_eq!(cache.lru.len(), 1);
        assert_eq!(cache.slru.protected_len(), 2);
        assert_eq!(cache.slru.probationary_len(), 2);

        assert_eq!(cache.get(&4), Some(&4));
        assert_eq!(cache.get_mut(&5), Some(&mut 5));

        // current state
        // window cache:        (MRU) [5] (LRU)
        // probationary cache:  (MRU) [1, 2] (LRU)
        // protected cache:     (MRU) [4, 3] (LRU)
        assert_eq!(cache.lru.peek_lru(), Some((&5, &5)));
        assert_eq!(cache.slru.peek_lru_from_probationary(), Some((&2, &22)));
        assert_eq!(cache.slru.peek_mru_from_probationary(), Some((&1, &11)));
        assert_eq!(cache.slru.peek_lru_from_protected(), Some((&3, &33)));
        assert_eq!(cache.slru.peek_mru_from_protected(), Some((&4, &4)));
        assert_eq!(cache.lru.len(), 1);
        assert_eq!(cache.slru.protected_len(), 2);
        assert_eq!(cache.slru.probationary_len(), 2);

        assert_eq!(cache.peek(&3), Some(&33));
        assert_eq!(cache.peek_mut(&2), Some(&mut 22));

        assert_eq!(cache.remove(&3), Some(33));
        assert_eq!(cache.remove(&2), Some(22));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_wtinylfu_clone() {
        let mut cache = WTinyLFUCache::with_sizes(1, 2, 2, 5).unwrap();
        assert_eq!(cache.cap(), 5);
        assert_eq!(cache.window_cache_cap(), 1);
        assert_eq!(cache.main_cache_cap(), 4);

        assert_eq!(cache.put(1, 1), PutResult::Put);
        assert!(cache.contains(&1));
        assert_eq!(cache.put(2, 2), PutResult::Put);
        assert!(cache.contains(&2));
        assert_eq!(cache.put(3, 3), PutResult::Put);
        assert!(cache.contains(&3));

        assert_eq!(cache.put(4, 3), PutResult::Evicted { key: 1, value: 1 });
    }
}
