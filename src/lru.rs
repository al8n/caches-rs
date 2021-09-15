use crate::{
    CacheError, DefaultEvictCallback, DefaultHashBuilder, KeyRef, LRUIter, LRUIterMut, MRUIter,
    MRUIterMut, PutResult, RawLRU,
};

#[cfg(feature = "nightly")]
use crate::NotKeyRef;

use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};

// #[cfg(feature = "hashbrown")]
// use hashbrown::{HashMap, HashSet};
//
// #[cfg(not(feature = "hashbrown"))]
// use std::collections::{HashMap, HashSet};

// use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
// use alloc::vec::Vec;

/// `LRUCache` is a fixed size LRU cache.
pub struct LRUCache<K, V, S = DefaultHashBuilder> {
    core: RawLRU<K, V, DefaultEvictCallback, S>,
}

// impl<K: Clone, V: Clone, S: Clone> Clone for LRUCache<K, V, S> {
//     fn clone(&self) -> Self {
//         Self {
//             core: self.core.clone(),
//         }
//     }
// }

impl<'a, K: Hash + Eq, V> LRUCache<K, V> {
    pub fn new(size: usize) -> Result<Self, CacheError> {
        RawLRU::new(size).map(|raw| Self { core: raw })
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> LRUCache<K, V, S> {
    pub fn with_hasher(size: usize, hasher: S) -> Result<Self, CacheError> {
        RawLRU::with_hasher(size, hasher).map(|r| Self { core: r })
    }

    /// `purge` is used to completely clear the cache.
    pub fn purge(&mut self) {
        self.core.purge()
    }

    /// `put` puts a key-value pair into cache, returns a [`PutResult`].
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::{LRUCache, PutResult};
    /// let mut cache = LRUCache::new(2).unwrap();
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
    pub fn put(&mut self, k: K, v: V) -> PutResult<K, V> {
        self.core.put(k, v)
    }

    // /// `keys` returns an iterator of the keys in the cache, from newest to oldest.
    // ///
    // /// The iterator will not updating the recent-ness or deleting it for being stale.
    // pub fn keys(&self) -> Keys<'_, K, V> {
    //     self.core.keys()
    // }
    //
    // /// `reversed_keys` returns an iterator of the keys in the cache, from oldest to newest.
    // ///
    // /// The iterator will not updating the recent-ness or deleting it for being stale.
    // pub fn reversed_keys(&self) -> ReversedKeys<'_, K, V> {
    //     self.core.reversed_keys()
    // }
    //
    // /// `values` returns an iterator of the values in the cache, from newest to oldest.
    // ///
    // /// The iterator will not updating the recent-ness or deleting it for being stale.
    // pub fn values(&self) -> Values<'_, K, V> {
    //     self.core.values()
    // }

    // /// `reversed_values` returns an iterator of the values in the cache, from oldest to newest.
    // ///
    // /// The iterator will not updating the recent-ness or deleting it for being stale.
    // pub fn reversed_values(&self) -> ReversedValues<'_, K, V> {
    //     self.core.reversed_values()
    // }
    //
    // /// `values_mut` returns an iterator of the mutable values in the cache, from newest to oldest.
    // ///
    // /// The iterator will not updating the recent-ness or deleting it for being stale.
    // pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
    //     self.core.values_mut()
    // }
    //
    // /// `reversed_values_mut` returns an iterator of the mutable values in the cache, from oldest to newest.
    // ///
    // /// The iterator will not updating the recent-ness or deleting it for being stale.
    // pub fn reversed_values_mut(&mut self) -> ReversedValuesMut<'_, K, V> {
    //     self.core.reversed_values_mut()
    // }

    /// `iter` returns an iterator of entries, in most recent used order.
    ///
    /// The iterator will not updating the recent-ness or deleting it for being stale.
    pub fn iter(&self) -> MRUIter<'_, K, V> {
        self.core.iter()
    }

    /// `iter_mut` returns an iterator of mutable entries, in most recent used order.
    ///
    /// The iterator will not updating the recent-ness or deleting it for being stale.
    pub fn iter_mut(&mut self) -> MRUIterMut<'_, K, V> {
        self.core.iter_mut()
    }

    // /// `reversed_iter` returns an iterator of entries, from oldest to newest
    // ///
    // /// The iterator will not updating the recent-ness or deleting it for being stale.
    // pub fn reversed_iter(&self) -> ReversedIter<'_, K, V> {
    //     self.core.reversed_iter()
    // }
    //
    // /// `reversed_iter_mut` returns an iterator of mutable entries, from oldest to newest
    // ///
    // /// The iterator will not updating the recent-ness or deleting it for being stale.
    // pub fn reversed_iter_mut(&mut self) -> ReversedIterMut<'_, K, V> {
    //     self.core.reversed_iter_mut()
    // }

    /// `get` looks up a key's value from the cache.
    pub fn get<Q>(&mut self, k: &Q) -> Option<&V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.core.get(k)
    }

    /// `get_mut` looks up a key's value(mutable) from the cache.
    pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.core.get_mut(k)
    }

    /// `get_oldest` returns the oldest entry.
    pub fn get_lru(&mut self) -> Option<(&K, &V)> {
        self.core.get_lru()
    }

    /// `get_oldest_mut` returns the mutable oldest entry.
    pub fn get_lru_mut(&mut self) -> Option<(&K, &mut V)> {
        self.core.get_lru_mut()
    }

    /// `peek` returns the value (or undefined if not found) without updating
    /// the "recently used"-ness of the key.
    pub fn peek<Q>(&self, k: &Q) -> Option<&V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.core.peek(k)
    }

    /// `peek_mut` returns the mutable value (or undefined if not found) without updating
    /// the "recently used"-ness of the key.
    pub fn peek_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.core.peek_mut(k)
    }

    /// `peek_lru` returns the oldest entry without updating the
    /// recent-ness.
    pub fn peek_lru(&self) -> Option<(&K, &V)> {
        self.core.peek_lru()
    }

    /// `peek_lru_mut` returns the mutable oldest entry without updating the
    /// recent-ness.
    pub fn peek_lru_mut(&mut self) -> Option<(&K, &mut V)> {
        self.core.peek_lru_mut()
    }

    /// `remove` removes the provided key from the cache.
    /// if the k is in cache, return the removed entry.
    pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.core.remove(k)
    }

    /// `remove_lru` removes the oldest item from the cache.
    /// if success, return the oldest entry.
    pub fn remove_lru(&mut self) -> Option<(K, V)> {
        self.core.remove_lru()
    }

    /// `contains` checks if a key is in the cache, without updating the
    /// recent-ness or deleting it for being stale.
    pub fn contains<Q>(&self, k: &Q) -> bool
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.core.contains(k)
    }

    /// `contains_or_put` checks if a key is in the cache without updating the
    /// recent-ness or deleting it for being stale, and if not, adds the value.
    /// Returns whether found and whether an eviction occurred.
    ///
    ///
    /// # Example
    ///
    /// ```
    /// use hashicorp_lru::{LRUCache, PutResult};
    /// let mut cache = LRUCache::new(2).unwrap();
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    ///
    /// assert_eq!(cache.contains_or_put(2, "B"), (true, None));
    /// assert_eq!(cache.contains_or_put(1, "A"), (false, Some(PutResult::Evicted { key: 2, value: "b",})));
    /// ```
    pub fn contains_or_put(&mut self, k: K, v: V) -> (bool, Option<PutResult<K, V>>) {
        self.core.contains_or_put(k, v)
    }

    /// `resize` changes the cache size. return the number of evicted entries
    pub fn resize(&mut self, size: usize) -> u64 {
        self.core.resize(size)
    }

    /// `len` returns the number of items in the cache.
    pub fn len(&self) -> usize {
        self.core.len()
    }
}

// impl<'a, K: Hash + Eq + Clone, V: Clone, S: BuildHasher>
//     From<RawLRU<'a, K, V, DefaultEvictCallback, S>> for LRUCache<'a, K, V, S>
// {
//     fn from(raw: RawLRU<'a, K, V, DefaultEvictCallback, S>) -> Self {
//         Self { core: raw }
//     }
// }

// macro_rules! impl_from_collections_for_lru {
//     ($($t:ty),*) => {
//         $(
//         impl<'a, K: Hash + Eq, V> From<$t> for LRUCache<'a, K, V>
//         {
//             fn from(vals: $t) -> Self {
//                 Self::from(RawLRU::from(vals))
//             }
//         }
//         )*
//     }
// }

// impl_from_collections_for_lru!(
//     Vec<(K, V)>,
//     VecDeque<(K, V)>,
//     LinkedList<(K, V)>,
//     HashSet<(K, V)>,
//     BTreeSet<(K,V)>,
//     BinaryHeap<(K, V)>,
//     HashMap<K, V>,
//     BTreeMap<K, V>
// );

// impl<'a, K: Hash + Eq + Clone, V: Clone> From<&[(K, V)]> for LRUCache<'a, K, V> {
//     fn from(vals: &[(K, V)]) -> Self {
//         Self::from(RawLRU::from(vals))
//     }
// }
//
// impl<'a, K: Hash + Eq + Clone, V: Clone> From<&mut [(K, V)]> for LRUCache<'a, K, V> {
//     fn from(vals: &mut [(K, V)]) -> Self {
//         Self::from(RawLRU::from(vals))
//     }
// }
//
// #[cfg(feature = "nightly")]
// impl_from_collections_for_lru!([(K, V); N]);

#[cfg(test)]
mod test {
    // use crate::lru::LRUCache;
    // use crate::RawLRU;
    // use alloc::string::ToString;

    #[test]
    fn test_lru() {

        // let mut cache = RawLRU::new(3);
        // cache.put("a".to_string(), "a".to_string());
        // cache.put("b".to_string(), "b".to_string());
        // cache.put("c".to_string(), "c".to_string());
        //
        // let mut lru = LRUCache::new(1);
        //
        // let a = lru.get_mut(&"a".to_string()).unwrap();
        // *a = "aa".to_string();
        // let a = lru.get(&"a".to_string()).unwrap();
        // assert_eq!(*a, "aa".to_string());
    }
}
