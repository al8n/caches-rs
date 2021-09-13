#![no_std]
#![cfg_attr(feature = "nightly", feature(negative_impls, auto_traits))]
#[deny(missing_docs)]
extern crate alloc;
#[cfg(feature = "hashbrown")]
extern crate hashbrown;

#[cfg(any(test, not(feature = "hashbrown")))]
extern crate std;

mod lru;
mod raw;

#[macro_use]
mod macros;
mod adaptive;
mod two_queue;

pub use raw::{
    IntoIter, Iter, IterMut, Keys, RawLRU, ReversedIter, ReversedIterMut, ReversedKeys,
    ReversedValues, ReversedValuesMut, Values, ValuesMut,
};

use core::fmt::{Debug, Display, Formatter};

#[cfg(feature = "hashbrown")]
pub type DefaultHashBuilder = hashbrown::hash_map::DefaultHashBuilder;

#[cfg(not(feature = "hashbrown"))]
pub type DefaultHashBuilder = std::collections::hash_map::DefaultHasher;

/// `DefaultEvictCallback` is a noop evict callback.
#[derive(Debug, Clone, Copy)]
pub struct DefaultEvictCallback;

impl OnEvictCallback for DefaultEvictCallback {
    fn on_evict<K, V>(&self, _: &K, _: &V) {}
}

pub trait OnEvictCallback {
    fn on_evict<K, V>(&self, key: &K, val: &V);
}

/// `CacheError` is the errors of this crate.
#[derive(Debug)]
pub enum CacheError {
    InvalidSize(usize),
}

impl Display for CacheError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            CacheError::InvalidSize(size) => write!(f, "invalid cache size {}", *size),
        }
    }
}
