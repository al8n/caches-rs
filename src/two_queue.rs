// use crate::{DefaultEvictCallback, DefaultHashBuilder, RawLRU, CacheError};
// use core::hash::{BuildHasher, Hash};
// use hashbrown::HashMap;
// use crate::raw::{KeyRef, EntryNodeLinkedList, EntryNode};
// use alloc::boxed::Box;
//
// /// DEFAULT_2Q_RECENT_RATIO is the ratio of the 2Q cache dedicated
// /// to recently added entries that have only been accessed once.
// pub static DEFAULT_2Q_RECENT_RATIO: f64 = 0.25;
//
// /// DEFAULT_2Q_GHOST_ENTRIES is the default ratio of ghost
// /// entries kept to track entries recently evicted
// pub static DEFAULT_2Q_GHOST_RATIO: f64 = 0.5;
//
// /// `TwoQueueCache` is a fixed size 2Q cache.
// /// 2Q is an enhancement over the standard LRU cache
// /// in that it tracks both frequently and recently used
// /// entries separately. This avoids a burst in access to new
// /// entries from evicting frequently used entries. It adds some
// /// additional tracking overhead to the standard LRU cache, and is
// /// computationally about 2x the cost, and adds some metadata over
// /// head. The ARCCache is similar, but does not require setting any
// /// parameters.
// pub struct TwoQueueCache<'a, K, V, S = DefaultHashBuilder> {
//     size: usize,
//     recent_size: usize,
//
//     recent: &'a mut RawLRU<K, V, DefaultEvictCallback, S>,
//     // recent_map: HashMap<KeyRef<K>, Box<EntryNode<K, V>>>,
//     // recent_ll: EntryNodeLinkedList<K, V>,
//
//     // freq_size: usize,
//     frequent: &'a mut RawLRU<K, V, DefaultEvictCallback, S>,
//     recent_evict: &'a mut RawLRU<K, V, DefaultEvictCallback, S>,
// }
//
// impl<'a, K: Hash + Eq, V> TwoQueueCache<'a, K, V> {
//     pub fn new(size: usize) -> Result<Self, CacheError> {
//         Self::with_2q_parameters(size, DEFAULT_2Q_RECENT_RATIO, DEFAULT_2Q_GHOST_RATIO)
//     }
//
//     pub fn with_recent_ratio(size: usize, rr: f64) -> Result<Self, CacheError> {
//         Self::with_2q_parameters(size, rr, DEFAULT_2Q_GHOST_RATIO)
//     }
//
//     pub fn with_ghost_ratio(size: usize, gr: f64) -> Result<Self, CacheError> {
//         Self::with_2q_parameters(size, DEFAULT_2Q_RECENT_RATIO, gr)
//     }
//
//     pub fn with_2q_parameters(size: usize, rr: f64, gr: f64) -> Result<Self, CacheError> {
//         if size == 0 {
//             return Err(CacheError::InvalidSize(size));
//         }
//
//         if rr < 0.0 || rr > 1.0 {
//             return Err(CacheError::InvalidRecentRatio(rr));
//         }
//
//         if gr < 0.0 || gr > 1.0 {
//             return Err(CacheError::InvalidGhostRatio(gr));
//         }
//
//         // Determine the sub-sizes
//         let rs = ((size as f64) * rr).floor() as usize;
//         let es = ((size as f64) * gr).floor() as usize;
//
//         // allocate the lrus
//         let recent = RawLRU::new(size).unwrap();
//         let freq = RawLRU::new(size).unwrap();
//
//         let recent_evict = RawLRU::new(es )?;
//
//         Ok(Self {
//             size,
//             recent_size: rs,
//             recent,
//             frequent: freq,
//             recent_evict,
//         })
//     }
//
// }
//
//
// impl<'a, K: Hash + Eq, V, S: BuildHasher + Clone> TwoQueueCache<'a, K, V, S> {
//     pub fn with_recent_ratio_and_hasher(size: usize, rr: f64, hasher: S)  -> Result<Self, CacheError> {
//         Self::with_2q_parameters_and_hasher(size, rr, DEFAULT_2Q_GHOST_RATIO, hasher)
//     }
//
//     pub fn with_ghost_ratio_and_hasher(size: usize, gr: f64, hasher: S) -> Result<Self, CacheError> {
//         Self::with_2q_parameters_and_hasher(size, DEFAULT_2Q_RECENT_RATIO, gr, hasher)
//     }
//
//     pub fn with_2q_parameters_and_hasher(size: usize, rr: f64, gr: f64, hasher: S) -> Result<Self, CacheError> {
//         if size == 0 {
//             return Err(CacheError::InvalidSize(size));
//         }
//
//         if rr < 0.0 || rr > 1.0 {
//             return Err(CacheError::InvalidRecentRatio(rr));
//         }
//
//         if gr < 0.0 || gr > 1.0 {
//             return Err(CacheError::InvalidGhostRatio(gr));
//         }
//
//         // Determine the sub-sizes
//         let rs = ((size as f64) * rr).floor() as usize;
//         let es = ((size as f64) * gr).floor() as usize;
//
//         // allocate the lrus
//         let recent = RawLRU::with_hasher(size, hasher.clone()).unwrap();
//         let freq = RawLRU::with_hasher(size, hasher.clone()).unwrap();
//
//         let recent_evict = RawLRU::with_hasher(es, hasher)?;
//
//         Ok(Self {
//             size,
//             recent_size: rs,
//             recent,
//             frequent: freq,
//             recent_evict,
//         })
//     }
//
//
//     pub fn put(&mut self, k: K, v: V) -> Option<(K, V)> {
//         // Check if the value is frequently used already,
//         // and just update the value
//         if self.frequent.contains(&k) {
//             let _ = self.frequent.put(k, v);
//             return None;
//         }
//
//         // Check if the value is recently used, and promote
//         // the value into the frequent list
//         if self.recent.contains(&k) {
//             let ent = self.recent.remove_and_return_box(&k);
//             let _ = self.frequent.put_box(ent);
//             return None;
//         }
//
//         // If the value was recently evicted, add it to the
//         // frequently used list
//         if self.recent_evict.contains(&k) {
//             self.ensure_space(true);
//             let ent = self.recent_evict.remove_and_return_box(&k);
//             self.frequent.put_box(ent);
//             return None;
//         }
//
//         // add to the recently seen list
//         self.ensure_space(false);
//         self.recent.put(k, v)
//     }
//
//     pub fn get(&mut self, k: &K) -> Option<&'a V> {
//         // Check if this is a frequent value
//         self.frequent
//             .get(k)
//             .or_else(move || match self.recent.remove(k) {
//                 None => None,
//                 Some(ent) => {
//                     let _ = self.frequent.put(ent.0, ent.1);
//                     self.frequent.peek(k)
//                 }
//             })
//     }
//
//     pub fn get_mut(&mut self, k: &K) -> Option<&'a mut V> {
//         // Check if this is a frequent value
//         self.frequent
//             .get_mut(k)
//             .or_else(move || match self.recent.remove(k) {
//                 None => None,
//                 Some(ent) => {
//                     let _ = self.frequent.put(ent.0, ent.1);
//                     self.frequent.peek_mut(k)
//                 }
//             })
//     }
//
//     fn ensure_space(&mut self, recent_evict: bool) {
//         // if we have space, nothing to do
//         let recent_len = self.recent.len();
//         let freq_len = self.frequent.len();
//         if recent_len + freq_len < self.size {
//             return;
//         }
//
//         // If the recent buffer is larger than
//         // the target, evict from there
//         if recent_len > 0 && (recent_len > self.recent_size || (recent_len == self.recent_size && !recent_evict)) {
//             let oldest = self.recent.remove_oldest_and_return_box();
//             self.recent_evict.put_box(oldest);
//             return;
//         }
//
//         // Remove from the frequent list otherwise
//         self.frequent.remove_oldest_without_cb_and_return();
//     }
//
//     pub fn remove(&mut self, k: &K) -> Option<(K,V)> {
//         self.frequent.remove(k)
//             .or_else(|| self.recent.remove(k)
//                 .or_else(|| self.recent_evict.remove(k)))
//     }
// }
//
// #[cfg(test)]
// mod test {
//     use crate::two_queue::TwoQueueCache;
//     use rand::{thread_rng, Rng};
//     use alloc::vec::Vec;
//     use rand::seq::SliceRandom;
//
//
//     #[test]
//     fn test_2q_cache_random_ops() {
//         let size = 128;
//         let mut rng = thread_rng();
//         let mut cases: Vec<u64> = (0..200_000).collect();
//         cases.shuffle(&mut rng);
//
//         let mut cache = TwoQueueCache::new(size).unwrap();
//
//         (0..200_000).for_each(|_| {
//             let k = rng.gen::<i64>() % 512;
//             let r: i64 = rng.gen();
//
//             match r % 3 {
//                 0 => {
//                     let _ = cache.put(k, k);
//                 }
//                 1 => {
//                     let _ = cache.get(&k);
//                 }
//                 2 => {
//                     let _ = cache.remove(&k);
//                 }
//                 _ => {}
//             }
//
//             assert!(cache.recent.len() + cache.frequent.len() <= size, "bad: recent: {} freq: {}", cache.recent.len(), cache.frequent.len())
//         })
//     }
//
//     #[test]
//     fn test_2q_cache_get_recent_to_freq() {
//
//     }
//
//     #[test]
//     fn test_2q_cache_put_recent_to_freq() {
//         let mut cache = TwoQueueCache::new(128).unwrap();
//
//         // Add initially to recent
//         cache.put(1, 1);
//         assert_eq!(cache.recent.len(), 1, "bad {}", cache.recent.len());
//         assert_eq!(cache.frequent.len(), 0, "bad {}", cache.frequent.len());
//
//         // Add should upgrade to frequent
//         cache.put(1, 1);
//         assert_eq!(cache.recent.len(), 0, "bad {}", cache.recent.len());
//         assert_eq!(cache.frequent.len(), 1, "bad {}", cache.frequent.len());
//
//         // Add should remain in frequent
//         cache.put(1, 1);
//         assert_eq!(cache.recent.len(), 0, "bad {}", cache.recent.len());
//         assert_eq!(cache.frequent.len(), 1, "bad {}", cache.frequent.len());
//     }
//
//     #[test]
//     fn test_2q_cache_put_recent_evict() {}
//
//     #[test]
//     fn test_2q_cache() {}
//
//     #[test]
//     fn test_2q_cache_contains() {}
//
//     #[test]
//     fn test_2q_cache_peek() {}
// }
