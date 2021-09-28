use caches::{Cache, SegmentedCache};

fn main() {
    let mut cache = SegmentedCache::new(2, 2).unwrap();

    cache.put(1, 1);
    cache.put(2, 2);

    assert_eq!(cache.probationary_len(), 2);
    assert_eq!(cache.protected_len(), 0);

    assert_eq!(cache.get(&1), Some(&1));
    *cache.get_mut(&2).unwrap() = 22;

    assert_eq!(cache.probationary_len(), 0);
    assert_eq!(cache.protected_len(), 2);

    cache.put(3, 3);
    cache.put(4, 4);

    assert_eq!(cache.probationary_len(), 2);
    assert_eq!(cache.protected_len(), 2);

    assert_eq!(cache.peek(&3), Some(&3));
    assert_eq!(cache.peek_mut(&4), Some(&mut 4));

    assert_eq!(cache.probationary_len(), 2);
    assert_eq!(cache.protected_len(), 2);

    assert_eq!(cache.remove(&2), Some(22));
    assert_eq!(cache.len(), 3);

    cache.purge();
    assert_eq!(cache.len(), 0);
}