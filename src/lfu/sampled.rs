//! Implement SampledLFU, which is used to stores key-costs paris.
//! The implementation is highly inspired by [Dgraph's ristretto].
//!
//! [Dgraph's ristretto]: https://github.com/dgraph-io/ristretto/blob/master/policy.go
use crate::lfu::{DefaultKeyHasher, KeyHasher};
use crate::{import_hashbrown, import_std, DefaultHashBuilder, KeyRef};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::marker::PhantomData;
use core::sync::atomic::{AtomicI64, Ordering};

import_hashbrown!(HashMap);
import_std!(HashMap);

/// DEFAULT_SAMPLES is the number of items to sample when looking at eviction
/// candidates. 5 seems to be the most optimal number [citation needed].
const DEFAULT_SAMPLES: usize = 5;

/// SampledLFU stores key-costs paris
pub struct SampledLFU<K, KH = DefaultKeyHasher<K>, S = DefaultHashBuilder> {
    samples: usize,
    max_cost: AtomicI64,
    used: i64,
    key_costs: HashMap<u64, i64, S>,
    kh: KH,
    marker: PhantomData<K>,
}

impl<K: Hash + Eq> SampledLFU<K> {
    /// Create a new SampledLFU
    pub fn new(max_cost: i64) -> Self {
        Self {
            samples: DEFAULT_SAMPLES,
            max_cost: AtomicI64::new(max_cost),
            used: 0,
            key_costs: HashMap::with_hasher(DefaultHashBuilder::default()),
            kh: DefaultKeyHasher::default(),
            marker: Default::default(),
        }
    }

    /// Create a new SampledLFU with samples.
    #[inline]
    pub fn with_samples(max_cost: i64, samples: usize) -> Self {
        Self {
            samples,
            max_cost: AtomicI64::new(max_cost),
            used: 0,
            key_costs: HashMap::with_hasher(DefaultHashBuilder::default()),
            kh: DefaultKeyHasher::default(),
            marker: Default::default(),
        }
    }
}

impl<K: Hash + Eq, S: BuildHasher> SampledLFU<K, DefaultKeyHasher<K>, S> {
    /// Create a new SampledLFU with specific hasher
    #[inline]
    pub fn with_hasher(max_cost: i64, hasher: S) -> Self {
        Self {
            samples: DEFAULT_SAMPLES,
            max_cost: AtomicI64::new(max_cost),
            used: 0,
            key_costs: HashMap::with_hasher(hasher),
            kh: DefaultKeyHasher::default(),
            marker: Default::default(),
        }
    }

    /// Create a new SampledLFU with samples and hasher
    #[inline]
    pub fn with_samples_and_hasher(max_cost: i64, samples: usize, hasher: S) -> Self {
        Self {
            samples,
            max_cost: AtomicI64::new(max_cost),
            used: 0,
            key_costs: HashMap::with_hasher(hasher),
            kh: DefaultKeyHasher::default(),
            marker: Default::default(),
        }
    }
}

impl<K: Hash + Eq, KH: KeyHasher<K>> SampledLFU<K, KH> {
    /// Create a new SampledLFU with specific hasher
    #[inline]
    pub fn with_key_hasher(max_cost: i64, kh: KH) -> Self {
        Self {
            samples: DEFAULT_SAMPLES,
            max_cost: AtomicI64::new(max_cost),
            used: 0,
            key_costs: HashMap::with_hasher(DefaultHashBuilder::default()),
            kh,
            marker: Default::default(),
        }
    }

    /// Create a new SampledLFU with samples and key hasher
    #[inline]
    pub fn with_samples_and_key_hasher(max_cost: i64, samples: usize, kh: KH) -> Self {
        Self {
            samples,
            max_cost: AtomicI64::new(max_cost),
            used: 0,
            key_costs: HashMap::with_hasher(DefaultHashBuilder::default()),
            kh,
            marker: Default::default(),
        }
    }
}

impl<K: Hash + Eq, KH: KeyHasher<K>, S: BuildHasher> SampledLFU<K, KH, S> {
    /// Create a new SampledLFU with samples and key hasher
    #[inline]
    pub fn with_samples_and_key_hasher_and_hasher(
        max_cost: i64,
        samples: usize,
        kh: KH,
        hasher: S,
    ) -> Self {
        Self {
            samples,
            max_cost: AtomicI64::new(max_cost),
            used: 0,
            key_costs: HashMap::with_hasher(hasher),
            kh,
            marker: Default::default(),
        }
    }

    /// Update the max_cost
    #[inline]
    pub fn update_max_cost(&self, mc: i64) {
        self.max_cost.store(mc, Ordering::SeqCst);
    }

    /// get the max_cost
    #[inline]
    pub fn get_max_cost(&self) -> i64 {
        self.max_cost.load(Ordering::SeqCst)
    }

    /// get the remain space of SampledLRU
    #[inline]
    pub fn room_left(&self, cost: i64) -> i64 {
        self.get_max_cost() - (self.used + cost)
    }

    /// try to fill the SampledLFU by the given pairs.
    pub fn fill_sample(&mut self, mut pairs: Vec<(u64, i64)>) -> Vec<(u64, i64)> {
        if pairs.len() >= self.samples {
            pairs
        } else {
            for (k, v) in &self.key_costs {
                pairs.push((*k, *v));
                if pairs.len() >= self.samples {
                    return pairs;
                }
            }
            pairs
        }
    }

    /// Put a key-cost pair to SampledLFU
    #[inline]
    pub fn increment<Q>(&mut self, key: &Q, cost: i64)
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let kh = self.hash_key(key);
        self.increment_hashed_key(kh, cost)
    }

    /// Put a hashed key and cost to SampledLFU
    #[inline]
    pub fn increment_hashed_key(&mut self, key: u64, cost: i64) {
        self.key_costs.insert(key, cost);
        self.used += cost
    }

    /// Remove an entry from SampledLFU by hashed key
    #[inline]
    pub fn remove_hashed_key(&mut self, kh: u64) -> Option<i64> {
        self.key_costs.remove(&kh).map(|cost| {
            self.used -= cost;
            cost
        })
    }

    /// Remove an entry from SampledLFU by key
    #[inline]
    pub fn remove<Q>(&mut self, key: &Q) -> Option<i64>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let kh = self.hash_key(key);
        self.remove_hashed_key(kh)
    }

    /// Clear the SampledLFU
    #[inline]
    pub fn clear(&mut self) {
        self.used = 0;
        self.key_costs.clear();
    }

    /// Update the cost by key. If the provided key in SampledLFU, then update it and return true, otherwise false.
    pub fn update<Q>(&mut self, k: &Q, cost: i64) -> bool
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let kh = self.hash_key(k);
        self.update_hashed_key(kh, cost)
    }

    /// Update the cost by hashed key. If the provided key in SampledLFU, then update it and return true, otherwise false.
    pub fn update_hashed_key(&mut self, k: u64, cost: i64) -> bool {
        // Update the cost of an existing key, but don't worry about evicting.
        // Evictions will be handled the next time a new item is added
        match self.key_costs.get_mut(&k) {
            None => false,
            Some(prev) => {
                let prev_val = *prev;
                self.used += cost - prev_val;
                *prev = cost;
                true
            }
        }
    }

    /// Returns the hash for the key
    #[inline]
    pub fn hash_key<Q>(&self, k: &Q) -> u64
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.kh.hash_key(k)
    }
}

#[cfg(test)]
mod test {
    use crate::lfu::sampled::SampledLFU;
    use std::vec;

    #[test]
    fn test_remove() {
        let mut lfu = SampledLFU::<u64>::new(4);
        lfu.increment_hashed_key(lfu.hash_key(&1), 1);
        lfu.increment(&2, 2);
        assert_eq!(lfu.remove(&2), Some(2));
        assert_eq!(lfu.used, 1);
        assert_eq!(lfu.key_costs.get(&2), None);
        assert_eq!(lfu.remove_hashed_key(4), None);
    }

    #[test]
    fn test_room() {
        let mut l = SampledLFU::<u64>::new(16);
        l.increment(&1, 1);
        l.increment_hashed_key(2, 2);
        l.increment_hashed_key(3, 3);
        assert_eq!(6, l.room_left(4));
    }

    #[test]
    fn test_clear() {
        let mut l = SampledLFU::<u64>::new(4);
        l.increment(&1, 1);
        l.increment(&2, 2);
        l.increment(&3, 3);
        l.clear();
        assert_eq!(0, l.key_costs.len());
        assert_eq!(0, l.used);
    }

    #[test]
    fn test_update() {
        let mut l = SampledLFU::<u64>::new(5);
        l.increment(&1, 1);
        l.increment(&2, 2);
        assert!(l.update(&1, 2));
        assert_eq!(4, l.used);
        let kh = l.hash_key(&2);
        assert!(l.update_hashed_key(kh, 3));
        assert_eq!(5, l.used);
        assert!(!l.update(&3, 3));
    }

    #[test]
    fn test_fill_sample() {
        let mut l = SampledLFU::<u64>::new(16);
        l.increment(&4, 4);
        l.increment(&5, 5);
        let sample = l.fill_sample(vec![(1, 1), (2, 2), (3, 3)]);
        let k = sample[sample.len() - 1].0;
        assert_eq!(5, sample.len());
        assert_ne!(1, k);
        assert_ne!(2, k);
        assert_ne!(3, k);
        assert_eq!(sample.len(), l.fill_sample(sample.clone()).len());
        l.remove(&5);
        let sample = l.fill_sample(sample[0..(sample.len() - 2)].to_vec());
        assert_eq!(4, sample.len())
    }
}
