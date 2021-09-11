#![no_std]
#![feature(auto_traits)]
#![feature(negative_impls)]
#[deny(missing_docs)]
extern crate alloc;
extern crate hashbrown;

mod lru;
mod raw;

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
