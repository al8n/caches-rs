//! The basic APIs for Cache implementation.
use crate::{KeyRef, PutResult};
use core::borrow::Borrow;
use core::hash::Hash;

/// Cache contains the basic APIs for a cache.
/// All of caches in this crate implement this trait.
pub trait Cache<K: Hash + Eq, V> {
    /// Puts a key-value pair into cache, returns a [`PutResult`].
    ///
    /// [`PutResult`]: struct.PutResult.html
    fn put(&mut self, k: K, v: V) -> PutResult<K, V>;

    /// Returns a reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Update the cache if it exists.
    fn get<'a, Q>(&mut self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    /// Returns a mutable reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Update the cache if it exists.
    fn get_mut<'a, Q>(&mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    /// Returns a reference to the value corresponding to the key in the cache or `None` if it is
    /// not present in the cache. Unlike `get`, `peek` does not update the cache so the key's
    /// position will be unchanged.
    fn peek<'a, Q>(&self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    /// Returns a mutable reference to the value corresponding to the key in the cache or `None` if it is
    /// not present in the cache. Unlike `get_mut`, `peek_mut` does not update the cache so the key's
    /// position will be unchanged.
    fn peek_mut<'a, Q>(&mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    /// Returns a bool indicating whether the given key is in the cache. Does not update the
    /// cache.
    fn contains<Q>(&self, k: &Q) -> bool
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    /// Removes and returns the value corresponding to the key from the cache or
    /// `None` if it does not exist.
    fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    /// Clears the contents of the cache.
    fn purge(&mut self);

    /// Returns the number of key-value pairs that are currently in the the cache.
    fn len(&self) -> usize;

    /// Returns the maximum number of key-value pairs the cache can hold.
    fn cap(&self) -> usize;

    /// Returns a bool indicating whether the cache is empty or not.
    fn is_empty(&self) -> bool;
}

/// Implement this trait for Cache to support resize.
pub trait ResizableCache {
    /// Resizes the cache. If the new capacity is smaller than the size of the current
    /// cache any entries past the new capacity are discarded.
    ///
    /// Returns the number of discarded entries
    fn resize(&mut self, cap: usize) -> u64;
}
