//! LFU based caches implementation.
//!
//! This module contains LFU based caches, [`WTinyLFUCache`], [`TinyLFU`] and [`SampledLFU`].
//!
mod sampled;
pub use sampled::SampledLFU;
mod tinylfu;
pub use tinylfu::TinyLFU;

mod wtinylfu;
pub use wtinylfu::{WTinyLFUCache, WTinyLFUCacheBuilder};

use crate::DefaultHashBuilder;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash, Hasher};
use core::marker::PhantomData;

/// KeyHasher is used to hash keys for Bloom Filter and CountSketch
pub trait KeyHasher<K: Hash + Eq> {
    /// hash the key
    fn hash_key<Q>(&self, key: &Q) -> u64
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized;
}

/// `DefaultKeyHasher` uses the same hasher as the Hashmap's default hasher
#[derive(Clone)]
pub struct DefaultKeyHasher<K: Hash + Eq> {
    marker: PhantomData<K>,
    hasher: DefaultHashBuilder,
}

impl<K: Hash + Eq> Default for DefaultKeyHasher<K> {
    fn default() -> Self {
        Self {
            marker: Default::default(),
            hasher: DefaultHashBuilder::default(),
        }
    }
}

impl<K: Hash + Eq> KeyHasher<K> for DefaultKeyHasher<K> {
    fn hash_key<Q>(&self, key: &Q) -> u64
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let mut s = self.hasher.build_hasher();
        key.hash(&mut s);
        s.finish()
    }
}
