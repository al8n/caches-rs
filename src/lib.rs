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

pub use raw::{
    IntoIter, Iter, IterMut, Keys, OnEvictCallback, RawLRU, ReversedIter, ReversedIterMut,
    ReversedKeys, ReversedValues, ReversedValuesMut, Values, ValuesMut,
};

use core::fmt::{Debug, Display, Formatter};

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
