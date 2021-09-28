use caches::{Cache, AdaptiveCache};

fn main() {
    let mut cache = AdaptiveCache::new(4).unwrap();

    // fill recent
    (0..4).for_each(|i| {
        cache.put(i, i);
    });

    // move to frequent
    cache.get(&0);
    cache.get(&1);
    assert_eq!(cache.frequent_len(), 2);

    // evict from recent
    cache.put(4, 4);
    assert_eq!(cache.recent_evict_len(), 1);

    // current state
    // recent:          (MRU) [4, 3] (LRU)
    // frequent:        (MRU) [1, 0] (LRU)
    // recent evict:    (MRU) [2] (LRU)
    // frequent evict:  (MRU) [] (LRU)

    // Add 2, should cause hit on recent_evict
    cache.put(2, 2);
    assert_eq!(cache.recent_evict_len(), 1);
    assert_eq!(cache.partition(), 1);
    assert_eq!(cache.frequent_len(), 3);

    // Current state
    // recent LRU:      (MRU) [4] (LRU)
    // frequent LRU:    (MRU) [2, 1, 0] (LRU)
    // recent evict:    (MRU) [3] (LRU)
    // frequent evict:  (MRU) [] (LRU)

    // Add 4, should migrate to frequent
    cache.put(4, 4);
    assert_eq!(cache.recent_len(), 0);
    assert_eq!(cache.frequent_len(), 4);

    // Current state
    // recent LRU:      (MRU) [] (LRU)
    // frequent LRU:    (MRU) [4, 2, 1, 0] (LRU)
    // recent evict:    (MRU) [3] (LRU)
    // frequent evict:  (MRU) [] (LRU)

    // Add 5, should evict to b2
    cache.put(5, 5);
    assert_eq!(cache.recent_len(), 1);
    assert_eq!(cache.frequent_len(), 3);
    assert_eq!(cache.frequent_evict_len(), 1);

    // Current state
    // recent:          (MRU) [5] (LRU)
    // frequent:        (MRU) [4, 2, 1] (LRU)
    // recent evict:    (MRU) [3] (LRU)
    // frequent evict:  (MRU) [0] (LRU)

    // Add 0, should decrease p
    cache.put(0, 0);
    assert_eq!(cache.recent_len(), 0);
    assert_eq!(cache.frequent_len(), 4);
    assert_eq!(cache.recent_evict_len(), 2);
    assert_eq!(cache.frequent_evict_len(), 0);
    assert_eq!(cache.partition(), 0);

    // Current state
    // recent:         (MRU) [] (LRU)
    // frequent:       (MRU) [0, 4, 2, 1] (LRU)
    // recent evict:   (MRU) [5, 3] (LRU)
    // frequent evict: (MRU) [0] (LRU)
}