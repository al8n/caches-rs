use core::fmt::{Display, Formatter};

/// `CacheError` is the errors of this crate.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub enum CacheError {
    /// Invalid cache size
    InvalidSize(usize),
    /// Invalid recent ratio for [`TwoQueueCache`]
    ///
    /// [`TwoQueueCache`]: struct.TwoQueueCache.html
    InvalidRecentRatio(f64),
    /// Invalid ghost ratio for [`TwoQueueCache`]
    ///
    /// [`TwoQueueCache`]: struct.TwoQueueCache.html
    InvalidGhostRatio(f64),
}

impl Display for CacheError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            CacheError::InvalidSize(size) => write!(f, "invalid cache size {}", *size),
            CacheError::InvalidRecentRatio(r) => write!(f, "invalid recent ratio {}", *r),
            CacheError::InvalidGhostRatio(r) => write!(f, "invalid ghost ratio {}", *r),
        }
    }
}
