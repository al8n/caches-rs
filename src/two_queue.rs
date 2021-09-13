use crate::{DefaultEvictCallback, DefaultHashBuilder, RawLRU};

/// `TwoQueueCache` is a fixed size 2Q cache.
/// 2Q is an enhancement over the standard LRU cache
/// in that it tracks both frequently and recently used
/// entries separately. This avoids a burst in access to new
/// entries from evicting frequently used entries. It adds some
/// additional tracking overhead to the standard LRU cache, and is
/// computationally about 2x the cost, and adds some metadata over
/// head. The ARCCache is similar, but does not require setting any
/// parameters.
pub struct TweQueueCache<'a, K, V, S = DefaultHashBuilder> {
    size: usize,
    recent_size: usize,

    recent: RawLRU<'a, K, V, DefaultEvictCallback, S>,
    frequent: RawLRU<'a, K, V, DefaultEvictCallback, S>,
    recent_evict: RawLRU<'a, K, V, DefaultEvictCallback, S>,
}
