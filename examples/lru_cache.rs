use caches::{Cache, LRUCache, PutResult};

fn main() {
    let mut cache = LRUCache::new(2).unwrap();
    // fill the cache
    assert_eq!(cache.put(1, 1), PutResult::Put);
    assert_eq!(cache.put(2, 2), PutResult::Put);

    // put 3, should evict the entry (1, 1)
    assert_eq!(cache.put(3, 3), PutResult::Evicted {key: 1,value: 1});

    // put 4, should evict the entry (2, 2)
    assert_eq!(cache.put(4, 4), PutResult::Evicted {key: 2,value: 2});

    // get 3, should update the recent-ness
    assert_eq!(cache.get(&3), Some(&3));

    // put 5, should evict the entry (4, 4)
    assert_eq!(cache.put(5, 5), PutResult::Evicted {key: 4,value: 4});
}