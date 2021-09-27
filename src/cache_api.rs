use crate::lru::{
    KeysLRUIter, KeysMRUIter, LRUIter, LRUIterMut, MRUIter, MRUIterMut, ValuesLRUIter,
    ValuesLRUIterMut, ValuesMRUIter, ValuesMRUIterMut,
};
use crate::{KeyRef, PutResult};
use core::borrow::Borrow;
use core::hash::Hash;

/// Cache contains the basic APIs for a cache.
/// All of caches in this crate implement this trait.
pub trait Cache<K: Hash + Eq, V> {
    ///
    fn put(&mut self, k: K, v: V) -> PutResult<K, V>;

    ///
    fn get<'a, Q>(&mut self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    ///
    fn get_mut<'a, Q>(&mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    ///
    fn peek<'a, Q>(&self, k: &'a Q) -> Option<&'a V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    ///
    fn peek_mut<'a, Q>(&mut self, k: &'a Q) -> Option<&'a mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    ///
    fn contains<Q>(&self, k: &Q) -> bool
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    ///
    fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized;

    ///
    fn purge(&mut self);

    ///
    fn len(&self) -> usize;

    ///
    fn cap(&self) -> usize;
}

pub trait CacheMRUIter<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn iter_mru(&self) -> MRUIter<'_, K, V>;
}

pub trait CacheMRUIterMut<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn iter_mru_mut(&mut self) -> MRUIterMut<'_, K, V>;
}

pub trait CacheLRUIter<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn iter_lru(&self) -> LRUIter<'_, K, V>;
}

pub trait CacheLRUIterMut<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn iter_lru_mut(&self) -> LRUIterMut<'_, K, V>;
}

pub trait CacheKeysMRU<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn keys_mru(&self) -> KeysMRUIter<'_, K, V>;
}

pub trait CacheKeysLRU<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn keys_lru(&self) -> KeysLRUIter<'_, K, V>;
}

pub trait CacheValuesLRU<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn values_lru(&self) -> ValuesLRUIter<'_, K, V>;
}

pub trait CacheValuesLRUMut<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn values_lru_mut(&self) -> ValuesLRUIterMut<'_, K, V>;
}

pub trait CacheValuesMRU<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn values_mru(&self) -> ValuesMRUIter<'_, K, V>;
}

pub trait CacheValuesMRUMut<K: Hash + Eq, V>: Cache<K, V> {
    ///
    fn values_mru_mut(&self) -> ValuesMRUIterMut<'_, K, V>;
}

pub trait CacheIters<K: Hash + Eq, V>:
CacheMRUIter<K, V> + CacheMRUIterMut<K, V> +
CacheLRUIter<K, V> + CacheLRUIterMut<K, V> +
CacheKeysLRU<K, V> + CacheKeysMRU<K, V> +
CacheValuesLRU<K, V> + CacheValuesLRUMut<K, V> +
CacheValuesMRU<K, V> + CacheValuesMRUMut<K, V>
{}