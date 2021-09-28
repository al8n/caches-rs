use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use caches::{OnEvictCallback, RawLRU, PutResult};

// EvictedCounter is a callback which is used to record the number of evicted entries.
struct EvictedCounter {
    ctr: Arc<AtomicU64>,
}

impl EvictedCounter {
    pub fn new(ctr: Arc<AtomicU64>) -> Self {
        Self {
            ctr,
        }
    }
}

impl OnEvictCallback for EvictedCounter {
    fn on_evict<K, V>(&self, _: &K, _: &V) {
        self.ctr.fetch_add(1, Ordering::SeqCst);
    }
}

fn main() {
    use caches::Cache;let counter = Arc::new(AtomicU64::new(0));

    let mut cache: RawLRU<u64, u64, EvictedCounter> = RawLRU::with_on_evict_cb(2, EvictedCounter::new(counter.clone())).unwrap();

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

    assert_eq!(counter.load(Ordering::SeqCst), 3);
}