use crate::lfu::tinylfu::bloom::Bloom;
use crate::lfu::tinylfu::error::TinyLFUError;
use crate::lfu::tinylfu::sketch::CountMinSketch;
use crate::{DefaultHashBuilder, KeyRef};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash, Hasher};
use core::marker::PhantomData;

mod bloom;
pub mod error;
mod sketch;

pub(crate) const DEFAULT_FALSE_POSITIVE_RATIO: f64 = 0.01;

/// KeyHasher is used to hash keys for Bloom Filter and CountSketch
pub trait KeyHasher<K: Hash + Eq> {
    fn hash<Q>(&self, t: &Q) -> u64
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized;
}

/// `DefaultKeyHasher` uses the same hasher as the Hashmap's default hasher
#[derive(Copy, Clone)]
pub struct DefaultKeyHasher<K: Hash + Eq> {
    marker: PhantomData<K>,
}

impl<K: Hash + Eq> Default for DefaultKeyHasher<K> {
    fn default() -> Self {
        Self {
            marker: Default::default(),
        }
    }
}

impl<K: Hash + Eq> KeyHasher<K> for DefaultKeyHasher<K> {
    fn hash<Q>(&self, t: &Q) -> u64
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let mut s = DefaultHashBuilder::default().build_hasher();
        t.hash(&mut s);
        s.finish()
    }
}

pub struct TinyLFUBuilder<K, KH = DefaultKeyHasher<K>> {
    samples: usize,
    size: usize,
    key_hasher: Option<KH>,
    false_positive_ratio: Option<f64>,
    marker: PhantomData<K>,
}

impl<K: Hash + Eq> Default for TinyLFUBuilder<K> {
    fn default() -> Self {
        Self {
            samples: 0,
            size: 0,
            key_hasher: Some(DefaultKeyHasher::default()),
            false_positive_ratio: Some(DEFAULT_FALSE_POSITIVE_RATIO),
            marker: Default::default(),
        }
    }
}

impl<K: Hash + Eq> TinyLFUBuilder<K> {
    /// The constructor of TinyLFUBuilder
    pub fn new(size: usize, samples: usize) -> Self {
        Self::default().set_size(size).set_samples(samples)
    }
}

impl<K: Hash + Eq, KH: KeyHasher<K>> TinyLFUBuilder<K, KH> {
    /// Set the samples of TinyLFU
    pub fn set_samples(self, samples: usize) -> Self {
        Self {
            samples,
            size: self.size,
            key_hasher: self.key_hasher,
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Set the size of TinyLFU
    pub fn set_size(self, sz: usize) -> Self {
        Self {
            samples: self.samples,
            size: sz,
            key_hasher: self.key_hasher,
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Set the false positive ratio of TinyLFU
    pub fn set_false_positive_ratio(self, fp_ratio: f64) -> Self {
        Self {
            samples: self.samples,
            size: self.size,
            key_hasher: self.key_hasher,
            false_positive_ratio: Some(fp_ratio),
            marker: self.marker,
        }
    }

    /// Set the size of TinyLFU
    pub fn set_key_hasher<NKH: KeyHasher<K>>(self, kh: NKH) -> TinyLFUBuilder<K, NKH> {
        TinyLFUBuilder {
            samples: self.samples,
            size: self.size,
            key_hasher: Some(kh),
            false_positive_ratio: self.false_positive_ratio,
            marker: self.marker,
        }
    }

    /// Finalize the builder to [`TinyLFU`]
    ///
    /// [`TinyLFU`]: struct.TinyLFU.html
    pub fn finalize(self) -> Result<TinyLFU<K, KH>, TinyLFUError> {
        if self.samples == 0 {
            return Err(TinyLFUError::InvalidSamples(self.samples));
        }

        let fp_ratio = self.false_positive_ratio.unwrap();
        if fp_ratio <= 0.0 || fp_ratio >= 1.0 {
            return Err(TinyLFUError::InvalidFalsePositiveRatio(fp_ratio));
        }

        Ok(TinyLFU {
            ctr: CountMinSketch::new(self.size as u64)?,
            doorkeeper: Bloom::new(self.samples, fp_ratio),
            samples: self.samples,
            w: 0,
            kh: self.key_hasher.unwrap(),
            marker: Default::default(),
        })
    }
}

/// TinyLFU is an admission helper that keeps track of access frequency using
/// tiny (4-bit) counters in the form of a count-min sketch.
/// tinyLFU is NOT thread safe.
pub struct TinyLFU<K, KH = DefaultKeyHasher<K>> {
    ctr: CountMinSketch,
    doorkeeper: Bloom,
    samples: usize,
    w: usize,
    kh: KH,
    marker: PhantomData<K>,
}

impl<K: Hash + Eq> TinyLFU<K> {
    /// The constructor of TinyLFU
    pub fn new(
        size: usize,
        samples: usize,
        false_positive_ratio: f64,
    ) -> Result<Self, TinyLFUError> {
        TinyLFUBuilder::new(size, samples)
            .set_false_positive_ratio(false_positive_ratio)
            .finalize()
    }
}

impl<K: Hash + Eq, KH: KeyHasher<K>> TinyLFU<K, KH> {
    pub fn from_builder(builder: TinyLFUBuilder<K, KH>) -> Result<Self, TinyLFUError> {
        builder.finalize()
    }

    /// estimates the frequency for a key.
    ///
    /// # Details
    /// Explanation from [TinyLFU: A Highly Efficient Cache Admission Policy §3.4.2]:
    /// - When querying items, we use both the Doorkeeper and the main structures.
    /// That is, if the item is included in the Doorkeeper,
    /// TinyLFU estimates the frequency of this item as its estimation in the main structure plus 1.
    /// Otherwise, TinyLFU returns just the estimation from the main structure.
    ///
    /// [TinyLFU: A Highly Efficient Cache Admission Policy §3.4.2]: https://arxiv.org/pdf/1512.00727.pdf
    pub fn estimate(&self, key: &K) -> u64 {
        let kh = self.hash(key);
        let mut hits = self.ctr.estimate(kh);
        if self.doorkeeper.contains(kh) {
            hits += 1;
        }
        hits
    }

    /// estimates the frequency.of key hash
    ///
    /// # Details
    /// Explanation from [TinyLFU: A Highly Efficient Cache Admission Policy §3.4.2]:
    /// - When querying items, we use both the Doorkeeper and the main structures.
    /// That is, if the item is included in the Doorkeeper,
    /// TinyLFU estimates the frequency of this item as its estimation in the main structure plus 1.
    /// Otherwise, TinyLFU returns just the estimation from the main structure.
    ///
    /// [TinyLFU: A Highly Efficient Cache Admission Policy §3.4.2]: https://arxiv.org/pdf/1512.00727.pdf
    pub fn estimate_hash(&self, kh: u64) -> u64 {
        let mut hits = self.ctr.estimate(kh);
        if self.doorkeeper.contains(kh) {
            hits += 1;
        }
        hits
    }

    /// increment multiple keys, for details, please see [`increment`].
    ///
    /// [`increment`]: struct.TinyLFU.method.increment.html
    pub fn increment_keys(&mut self, keys: &[K]) {
        keys.into_iter().for_each(|k| self.increment(k))
    }

    /// increment multiple hashed keys, for details, please see [`increment_hash`].
    ///
    /// [`increment_hash`]: struct.TinyLFU.method.increment_hash.html
    pub fn increment_hashes(&mut self, khs: &[u64]) {
        khs.into_iter().for_each(|k| self.increment_hash(*k))
    }

    /// See [TinyLFU: A Highly Efficient Cache Admission Policy] §3.2
    ///
    /// [TinyLFU: A Highly Efficient Cache Admission Policy]: https://arxiv.org/pdf/1512.00727.pdf
    pub fn increment<Q>(&mut self, key: &Q)
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let kh = self.hash(key);
        // Flip doorkeeper bit if not already done.
        if !self.doorkeeper.contains_or_add(kh) {
            // Increment count-min counter if doorkeeper bit is already set.
            self.ctr.increment(kh);
        }

        self.try_reset();
    }

    /// See [TinyLFU: A Highly Efficient Cache Admission Policy] §3.2
    ///
    /// [TinyLFU: A Highly Efficient Cache Admission Policy]: https://arxiv.org/pdf/1512.00727.pdf
    pub fn increment_hash(&mut self, kh: u64) {
        // Flip doorkeeper bit if not already done.
        if !self.doorkeeper.contains_or_add(kh) {
            // Increment count-min counter if doorkeeper bit is already set.
            self.ctr.increment(kh);
        }

        self.try_reset();
    }

    /// See [TinyLFU: A Highly Efficient Cache Admission Policy] §3.2 and §3.3
    ///
    /// [TinyLFU: A Highly Efficient Cache Admission Policy]: https://arxiv.org/pdf/1512.00727.pdf
    pub fn try_reset(&mut self) {
        self.w += 1;
        if self.w >= self.samples {
            self.reset();
        }
    }

    #[inline]
    fn reset(&mut self) {
        // zero out size
        self.w = 0;

        // zero bloom filter bits
        self.doorkeeper.reset();

        // halves count-min counters
        self.ctr.reset();
    }

    /// `clear` is an extension for the original TinyLFU.
    ///
    /// Comparing to [`reset`] halves the all the bits of count-min sketch,
    /// `clear` will set all the bits to zero of count-min sketch
    ///
    /// [`reset`]: struct.TinyLFU.method.reset.html
    pub fn clear(&mut self) {
        self.w = 0;
        self.doorkeeper.clear();
        self.ctr.clear();
    }

    /// `contains` checks if bit(s) for entry is/are set,
    /// returns true if the hash was added to the TinyLFU.
    pub fn contains(&self, key: &K) -> bool {
        let kh = self.hash(key);
        self.doorkeeper.contains(kh)
    }

    /// `contains_hash` checks if bit(s) for entry hash is/are set,
    /// returns true if the hash was added to the TinyLFU.
    pub fn contains_hash(&self, kh: u64) -> bool {
        self.doorkeeper.contains(kh)
    }

    /// `eq` compares `a` and `b`, returns if `a`'s counter is equal to `b`'s counter.
    pub fn eq<'a, 'b>(&'_ self, a: &'a K, b: &'b K) -> bool {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        if a_ctr == b_ctr {
            true
        } else {
            false
        }
    }

    /// `le` compares `a` and `b`, returns if `a`'s counter is less or equal to `b`'s counter.
    pub fn le<'a, 'b>(&'_ self, a: &'a K, b: &'b K) -> bool {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        if a_ctr <= b_ctr {
            true
        } else {
            false
        }
    }

    /// `lt` compares `a` and `b`, returns if `a`'s counter is less than `b`'s counter.
    pub fn lt<'a, 'b>(&'_ self, a: &'a K, b: &'b K) -> bool {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        if a_ctr < b_ctr {
            true
        } else {
            false
        }
    }

    /// `gt` compares `a` and `b`, returns if `a`'s counter is greater than `b`'s counter.
    pub fn gt<'a, 'b>(&'_ self, a: &'a K, b: &'b K) -> bool {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        if a_ctr > b_ctr {
            true
        } else {
            false
        }
    }

    /// `ge` compares `a` and `b`, returns if `a`'s counter is greater or equal to `b`'s counter.
    pub fn ge<'a, 'b>(&'_ self, a: &'a K, b: &'b K) -> bool {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        if a_ctr >= b_ctr {
            true
        } else {
            false
        }
    }

    fn compare_helper<'a, 'b>(&'_ self, a: &'a K, b: &'b K) -> (u64, u64) {
        let akh = self.hash(a);
        let mut a_ctr = 0;
        if !self.doorkeeper.contains(akh) {
            let bkh = self.hash(b);
            return if !self.doorkeeper.contains(bkh) {
                (0, 0)
            } else {
                (0, 1)
            };
        } else {
            a_ctr += 1;
        }

        let bkh = self.hash(b);
        let mut b_ctr = 0;
        if !self.doorkeeper.contains(bkh) {
            return (1, 0);
        } else {
            b_ctr += 1;
        }

        a_ctr += self.ctr.estimate(akh);
        b_ctr += self.ctr.estimate(bkh);

        (a_ctr, b_ctr)
    }
}

impl<K: Hash + Eq, KH: KeyHasher<K>> KeyHasher<K> for TinyLFU<K, KH> {
    #[inline]
    fn hash<Q>(&self, t: &Q) -> u64
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.kh.hash(t)
    }
}
