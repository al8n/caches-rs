//! Implement [TinyLFU: A Highly Efficient Cache Admission Policy].
//! The implementation is highly inspired by [Dgraph's ristretto]
//!
//! [Dgraph's ristretto]: https://github.com/dgraph-io/ristretto/blob/master/policy.go
//! [TinyLFU: A Highly Efficient Cache Admission Policy]: https://arxiv.org/pdf/1512.00727.pdf

use crate::lfu::tinylfu::bloom::Bloom;
use crate::lfu::tinylfu::sketch::CountMinSketch;
use crate::lfu::{DefaultKeyHasher, KeyHasher};
use core::borrow::Borrow;
use core::hash::Hash;
use core::marker::PhantomData;

mod bloom;
mod error;
pub use error::TinyLFUError;
mod sketch;

pub(crate) const DEFAULT_FALSE_POSITIVE_RATIO: f64 = 0.01;

/// TinyLFUBuilder is used to build a TinyLFU
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
    /// Returns a TinyLFU according to the [`TinyLFUBuilder`]
    ///
    /// [`TinyLFUBuilder`]: struct.TinyLFUBuilder.html
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
    pub fn estimate<Q>(&self, key: &Q) -> u64
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let kh = self.hash_key(key);
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
    pub fn estimate_hashed_key(&self, kh: u64) -> u64 {
        let mut hits = self.ctr.estimate(kh);
        if self.doorkeeper.contains(kh) {
            hits += 1;
        }
        hits
    }

    /// increment multiple keys, for details, please see [`increment`].
    ///
    /// [`increment`]: struct.TinyLFU.method.increment.html
    pub fn increment_keys<Q>(&mut self, keys: &[&Q])
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        keys.iter().for_each(|k| self.increment(k))
    }

    /// increment multiple hashed keys, for details, please see [`increment_keys`].
    ///
    /// [`increment_keys`]: struct.TinyLFU.method.increment_keys.html
    pub fn increment_hashed_keys(&mut self, khs: &[u64]) {
        khs.iter().for_each(|k| self.increment_hashed_key(*k))
    }

    /// See [TinyLFU: A Highly Efficient Cache Admission Policy] §3.2
    ///
    /// [TinyLFU: A Highly Efficient Cache Admission Policy]: https://arxiv.org/pdf/1512.00727.pdf
    pub fn increment<Q>(&mut self, key: &Q)
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let kh = self.hash_key(key);
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
    pub fn increment_hashed_key(&mut self, kh: u64) {
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
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let kh = self.hash_key(key);
        self.doorkeeper.contains(kh)
    }

    /// `contains_hash` checks if bit(s) for entry hash is/are set,
    /// returns true if the hash was added to the TinyLFU.
    pub fn contains_hash(&self, kh: u64) -> bool {
        self.doorkeeper.contains(kh)
    }

    /// `eq` compares `a` and `b`, returns if `a`'s counter is equal to `b`'s counter.
    pub fn eq<Q>(&'_ self, a: &Q, b: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        a_ctr == b_ctr
    }

    /// `le` compares `a` and `b`, returns if `a`'s counter is less or equal to `b`'s counter.
    pub fn le<Q>(&'_ self, a: &Q, b: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        a_ctr <= b_ctr
    }

    /// `lt` compares `a` and `b`, returns if `a`'s counter is less than `b`'s counter.
    pub fn lt<Q>(&'_ self, a: &Q, b: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        a_ctr < b_ctr
    }

    /// `gt` compares `a` and `b`, returns if `a`'s counter is greater than `b`'s counter.
    pub fn gt<Q>(&'_ self, a: &Q, b: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        a_ctr > b_ctr
    }

    /// `ge` compares `a` and `b`, returns if `a`'s counter is greater or equal to `b`'s counter.
    pub fn ge<Q>(&'_ self, a: &Q, b: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (a_ctr, b_ctr) = self.compare_helper(a, b);

        a_ctr >= b_ctr
    }

    fn compare_helper<Q>(&'_ self, a: &Q, b: &Q) -> (u64, u64)
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let akh = self.hash_key(a);
        let mut a_ctr = 0;
        if !self.doorkeeper.contains(akh) {
            let bkh = self.hash_key(b);
            return if !self.doorkeeper.contains(bkh) {
                (0, 0)
            } else {
                (0, 1)
            };
        } else {
            a_ctr += 1;
        }

        let bkh = self.hash_key(b);
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

    /// Returns the hash for the key
    #[inline]
    pub fn hash_key<Q>(&self, k: &Q) -> u64
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.kh.hash_key(k)
    }
}

#[cfg(test)]
mod test {
    use crate::lfu::tinylfu::TinyLFU;

    #[test]
    fn test_increment() {
        let mut l: TinyLFU<u64> = TinyLFU::new(4, 4, 0.01).unwrap();
        let kh = l.hash_key(&1);
        l.increment(&1);
        l.increment(&1);
        l.increment(&1);
        assert!(l.doorkeeper.contains(kh));
        assert_eq!(l.ctr.estimate(kh), 2);

        l.increment(&1);
        assert!(!l.doorkeeper.contains(kh));
        assert_eq!(l.ctr.estimate(kh), 1);
    }

    #[test]
    fn test_increment_hashed_key() {
        let mut l: TinyLFU<u64> = TinyLFU::new(4, 4, 0.01).unwrap();

        l.increment_hashed_key(1);
        l.increment_hashed_key(1);
        l.increment_hashed_key(1);
        assert!(l.doorkeeper.contains(1));
        assert_eq!(l.ctr.estimate(1), 2);

        l.increment_hashed_key(1);
        assert!(!l.doorkeeper.contains(1));
        assert_eq!(l.ctr.estimate(1), 1);
    }

    #[test]
    fn test_estimate() {
        let mut l: TinyLFU<u64> = TinyLFU::new(8, 8, 0.01).unwrap();
        l.increment(&1);
        l.increment(&1);
        l.increment(&1);

        assert_eq!(l.estimate(&1), 3);
        assert_eq!(l.estimate(&2), 0);
        assert_eq!(l.w, 3);
    }

    #[test]
    fn test_estimate_hashed_keyed_key() {
        let mut l: TinyLFU<u64> = TinyLFU::new(8, 8, 0.01).unwrap();
        l.increment_hashed_key(1);
        l.increment_hashed_key(1);
        l.increment_hashed_key(1);
        assert_eq!(l.estimate_hashed_key(1), 3);
        assert_eq!(l.estimate_hashed_key(2), 0);
        assert_eq!(l.w, 3);
    }

    // TODO: fix the bug caused by random
    // #[test]
    // fn test_increment_keys() {
    //     let mut l: TinyLFU<u64> = TinyLFU::new(16, 16, 0.01).unwrap();

    //     assert_eq!(l.samples, 16);
    //     l.increment_keys(&[&1, &2, &2, &3, &3, &3]);
    //     assert_eq!(l.estimate(&1), 1);
    //     assert_eq!(l.estimate(&2), 2);
    //     assert_eq!(l.estimate(&3), 3);
    //     assert_eq!(6, l.w);
    // }

    #[test]
    fn test_increment_hashed_keys() {
        let mut l: TinyLFU<u64> = TinyLFU::new(16, 16, 0.01).unwrap();

        assert_eq!(l.samples, 16);
        l.increment_hashed_keys(&[1, 2, 2, 3, 3, 3]);
        assert_eq!(l.estimate_hashed_key(1), 1);
        assert_eq!(l.estimate_hashed_key(2), 2);
        assert_eq!(l.estimate_hashed_key(3), 3);
        assert_eq!(6, l.w);
    }

    #[test]
    fn test_clear() {
        let mut l: TinyLFU<u64> = TinyLFU::new(16, 16, 0.01).unwrap();
        l.increment_hashed_keys(&[1, 3, 3, 3]);
        l.clear();
        assert_eq!(0, l.w);
        assert_eq!(0, l.estimate_hashed_key(3));
    }
}
