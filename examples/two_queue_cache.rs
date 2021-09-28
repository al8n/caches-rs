use caches::{Cache, TwoQueueCache, PutResult};

fn main() {
    let mut cache = TwoQueueCache::new(4).unwrap();

    // Add 1,2,3,4,
    (1..=4).for_each(|i| { assert_eq!(cache.put(i, i), PutResult::Put);});

    // Add 5 -> Evict 1 to ghost LRU
    assert_eq!(cache.put(5, 5), PutResult::Put);

    // Pull in the recently evicted
    assert_eq!(cache.put(1, 1), PutResult::Update(1));

    // Add 6, should cause another recent evict
    assert_eq!(cache.put(6, 6), PutResult::<i32, i32>::Put);

    // Add 7, should evict an entry from ghost LRU.
    assert_eq!(cache.put(7, 7), PutResult::Evicted { key: 2, value: 2 });

    // Add 2, should evict an entry from ghost LRU
    assert_eq!(cache.put(2, 11), PutResult::Evicted { key: 3, value: 3 });

    // Add 4, should put the entry from ghost LRU to freq LRU
    assert_eq!(cache.put(4, 11), PutResult::Update(4));

    // move all entry in recent to freq.
    assert_eq!(cache.put(2, 22), PutResult::Update(11));
    assert_eq!(cache.put(7, 77), PutResult::<i32, i32>::Update(7));

    // Add 6, should put the entry from ghost LRU to freq LRU, and evicted one
    // entry
    assert_eq!(cache.put(6, 66), PutResult::EvictedAndUpdate { evicted: (5, 5), update: 6});
    assert_eq!(cache.recent_len(), 0);
    assert_eq!(cache.ghost_len(), 1);
    assert_eq!(cache.frequent_len(), 4);
}