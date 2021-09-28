use caches::{Cache, WTinyLFUCache, PutResult};

fn main() {
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
    assert_eq!(cache.window_cache_len(), 1);

    assert_eq!(cache.put(3, 33), PutResult::Update(3));

    // current state
    // window cache:        (MRU) [2] (LRU)
    // probationary cache:  (MRU) [] (LRU)
    // protected cache:     (MRU) [3, 1] (LRU)
    assert_eq!(cache.window_cache_len(), 1);

    assert_eq!(cache.put(4, 4), PutResult::Put);
    assert_eq!(cache.put(5, 5), PutResult::Put);

    // current state
    // window cache:        (MRU) [5] (LRU)
    // probationary cache:  (MRU) [4, 2] (LRU)
    // protected cache:     (MRU) [3, 1] (LRU)

    assert_eq!(cache.get(&4), Some(&4));
    assert_eq!(cache.get_mut(&5), Some(&mut 5));

    // current state
    // window cache:        (MRU) [5] (LRU)
    // probationary cache:  (MRU) [1, 2] (LRU)
    // protected cache:     (MRU) [4, 3] (LRU)
    assert_eq!(cache.peek(&3), Some(&33));
    assert_eq!(cache.peek_mut(&2), Some(&mut 22));

    assert_eq!(cache.remove(&3), Some(33));
    assert_eq!(cache.remove(&2), Some(22));
}