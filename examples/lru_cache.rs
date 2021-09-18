use hashicorp_lru::LRUCache;

fn main() {
    let mut cache = LRUCache::new(5).unwrap();

    // put element
    cache.put(1, 1);


}
