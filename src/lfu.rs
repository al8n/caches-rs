//! LFU based caches implementation.
//!
//!
//! ## Acknowledgments
//! - dgryski's [go-tinylfu]
//! - The implementation of TinyLFU and SampledLFU are inspired by [Dgraph's ristretto].
//! - Gil Einziger's paper -- [TinyLFU: A Highly Efficient Cache Admission Policy]
//!
//! [go-tinylfu]: https://github.com/dgryski/go-tinylfu
//! [Dgraph's ristretto]: https://github.com/dgraph-io/ristretto/blob/master/policy.go
//! [TinyLFU: A Highly Efficient Cache Admission Policy]: https://arxiv.org/pdf/1512.00727.pdf
mod raw;
pub mod sampled;
pub mod tinylfu;
mod wtinylfu;

pub use wtinylfu::{WTinyLFUCache, WTinyLFUCacheBuilder};

use crate::{DefaultHashBuilder, KeyRef};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash, Hasher};
use core::marker::PhantomData;

/// KeyHasher is used to hash keys for Bloom Filter and CountSketch
pub trait KeyHasher<K: Hash + Eq> {
    /// hash the key
    fn hash_key<Q>(&self, key: &Q) -> u64
    where
        KeyRef<K>: Borrow<Q>,
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
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let mut s = self.hasher.build_hasher();
        key.hash(&mut s);
        s.finish()
    }
}
