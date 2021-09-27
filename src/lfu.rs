//!  asd
mod error;
mod raw;
mod sampled;
mod tinylfu;
mod wtinylfu;

pub use error::CacheError;
pub use wtinylfu::{WTinyLFUCache, WTinyLFUCacheBuilder};