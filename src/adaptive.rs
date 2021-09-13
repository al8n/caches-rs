use crate::{DefaultEvictCallback, DefaultHashBuilder, RawLRU};

/// `AdaptiveCache` is a fixed size Adaptive Replacement Cache (ARC).
/// ARC is an enhancement over the standard LRU cache in that tracks both
/// frequency and recency of use. This avoids a burst in access to new
/// entries from evicting the frequently used older entries. It adds some
/// additional tracking overhead to a standard LRU cache, computationally
/// it is roughly 2x the cost, and the extra memory overhead is linear
/// with the size of the cache. ARC has been patented by IBM, but is
/// similar to the `TwoQueueCache` (2Q) which requires setting parameters.
pub struct AdaptiveCache<'a, K, V, S = DefaultHashBuilder> {
    /// `size` is the total capacity of the cache
    size: usize,

    /// `p` is the dynamic preference towards T1 or T2
    p: usize,

    /// `t1` is the LRU for recently accessed items
    t1: RawLRU<'a, K, V, DefaultEvictCallback, S>,

    /// `b1` is the LRU for evictions from `t1`
    b1: RawLRU<'a, K, V, DefaultEvictCallback, S>,

    /// `t2` is the LRU for frequently accessed items
    t2: RawLRU<'a, K, V, DefaultEvictCallback, S>,

    /// `b2` is the LRU for evictions from `t2`
    b2: RawLRU<'a, K, V, DefaultEvictCallback, S>,
}
