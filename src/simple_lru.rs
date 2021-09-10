use crate::{
    CacheError, DefaultEvictCallback, Entry, EntryLinkedList, Iter, IterMut, KeyRef, LRUCache,
    OnEvictCallback,
};

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::borrow::{Borrow, BorrowMut};
use core::fmt::{Debug, Formatter};
use core::hash::{BuildHasher, Hash};
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem;
use core::ops::{Index, IndexMut};
use core::option::Option::Some;
use core::ptr::NonNull;
use hashbrown::hash_map::DefaultHashBuilder;
use hashbrown::HashMap;

pub struct SimpleLRU<K, V, E = DefaultEvictCallback, S = DefaultHashBuilder> {
    size: usize,
    evict_list: EntryLinkedList<K, V>,
    items: HashMap<KeyRef<K>, Box<Entry<K, V>>, S>,
    on_evict: Option<E>,
}

impl<K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> SimpleLRU<K, V, E, S> {
    pub fn with_callback_and_hasher(size: usize, callback: E, hash_builder: S) -> Self {
        Self::new_in(
            size,
            HashMap::with_capacity_and_hasher(size, hash_builder),
            Some(callback),
        )
    }

    fn new_in(
        size: usize,
        items: HashMap<KeyRef<K>, Box<Entry<K, V>>, S>,
        on_evict: Option<E>,
    ) -> Self {
        Self {
            size,
            evict_list: EntryLinkedList::new(),
            items,
            on_evict,
        }
    }

    /// `put` puts a value to the cache, returns true if an eviction occurred and
    /// updates the "recently used"-ness of the key.
    pub fn put(&mut self, key: K, mut val: V) -> bool {
        // Avoid `Option::map` because it bloats LLVM IR.
        let ent_ptr = self.items.get_mut(&KeyRef::new(&key)).map(|ent| {
            let ent_ptr: *mut Entry<K, V> = &mut **ent;
            ent_ptr
        });

        match ent_ptr {
            None => {
                let evict = self.evict_list.len >= self.size;
                // Verify size not exceed
                let mut ent: Box<Entry<K, V>> = if evict {
                    let old_key = self.evict_list.back().unwrap();
                    let old_key = KeyRef::new(old_key);
                    let mut old_ent = self.items.remove(&old_key).unwrap();

                    old_ent.key = key;
                    old_ent.val = val;

                    let old_ent_ptr: *mut Entry<K, V> = &mut *old_ent;
                    self.evict_list.detach(old_ent_ptr);
                    old_ent
                } else {
                    Box::new(Entry::new(key, val))
                };

                let ent_ptr = &mut *ent;
                self.evict_list.attach(ent_ptr);

                self.items.insert(
                    KeyRef {
                        ptr: &(*ent_ptr).key,
                    },
                    ent,
                );
                evict
            }
            Some(ptr) => {
                self.evict_list.move_to_front(ptr);
                // key is in cache, update evict list
                unsafe {
                    mem::swap(&mut val, &mut (*ptr).val);
                }
                false
            }
        }
    }

    pub fn get<Q>(&mut self, key: &Q) -> Option<&V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(ent) = self.items.get_mut(key) {
            let ent_ptr: *mut Entry<K, V> = &mut **ent;
            self.evict_list.move_to_front(ent_ptr);

            Some(unsafe { &(*(*ent_ptr).val.borrow()) })
        } else {
            None
        }
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(ent) = self.items.get_mut(key) {
            let ent_ptr: *mut Entry<K, V> = &mut **ent;
            self.evict_list.move_to_front(ent_ptr);

            Some(unsafe { &mut (*(*ent_ptr).val.borrow_mut()) })
        } else {
            None
        }
    }

    /// `get_oldest` returns the oldest entry from the cache. #key, value, isFound
    pub fn get_oldest(&self) -> Option<(&K, &V)> {
        self.evict_list.back_key_value()
    }

    /// `get_oldest_mut` returns the oldest entry from the cache. #key, value, isFound
    pub fn get_oldest_mut(&mut self) -> Option<(&mut K, &mut V)> {
        self.evict_list.back_key_value_mut()
    }

    /// `remove` tries remove a key from the cache.
    ///
    /// Remove removes the provided key from the cache, returning if the
    /// key was contained.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.items.remove(key) {
            None => None,
            Some(ent) => {
                let ent_ptr = Box::leak(ent);
                self.evict_list.detach(ent_ptr);

                if let Some(on_evict) = &self.on_evict {
                    on_evict.on_evict(&(*ent_ptr).key, &(*ent_ptr).val);
                }

                Some(unsafe { Box::from_raw(ent_ptr).val })
            }
        }
    }

    pub fn remove_oldest(&mut self) -> Option<(K, V)> {
        let tail = self.evict_list.tail?.as_ptr();
        unsafe {
            match self.items.remove(&KeyRef::new(&(*tail).key)) {
                None => None,
                Some(ent) => {
                    let ent_ptr = Box::leak(ent);
                    self.evict_list.detach(ent_ptr);

                    if let Some(on_evict) = &self.on_evict {
                        on_evict.on_evict(&(*ent_ptr).key, &(*ent_ptr).val);
                    }

                    let ent = Box::from_raw(ent_ptr);
                    Some((ent.key, ent.val))
                }
            }
        }
    }

    /// `len` returns the number of items in the cache.
    pub fn len(&self) -> usize {
        self.evict_list.len
    }

    /// `purge` clears the number of items in the cache.
    pub fn purge(&mut self) {
        self.evict_list.clear();
        self.items.clear();
    }

    /// `iter` returns a slice of the key-value pairs in the cache, from newest to oldest
    pub fn iter(&self) -> Iter<'_, K, V> {
        self.evict_list.iter()
    }

    /// `iter_mut` returns a slice of the key-value pairs(mutable) in the cache, from newest to oldest
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        self.evict_list.iter_mut()
    }

    /// `keys` returns a slice of the keys in the cache, from newest to oldest
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    /// `values` returns a slice of the values in the cache, from newest to oldest
    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }

    /// `values_mut` returns a slice of the values(mutable) in the cache, from newest to oldest
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// `peek` returns key's value without updating the "recently used"-ness of the key.
    pub fn peek<Q>(&self, key: &Q) -> Option<&V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.items.get(key) {
            None => None,
            Some(ent) => Some(&(*(*ent).val.borrow())),
        }
    }

    /// `peek_mut` returns a mutable key's value without updating the "recently used"-ness of the key.
    pub fn peek_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.items.get_mut(key) {
            None => None,
            Some(ent) => Some(&mut (*(*ent).val.borrow_mut())),
        }
    }

    /// `contains` checks if a key exists in cache without updating the recent-ness.
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.items.contains_key(key)
    }
}

impl<K: Hash + Eq, V> SimpleLRU<K, V, DefaultEvictCallback, DefaultHashBuilder> {
    pub fn new(size: usize) -> Self {
        Self::new_in(size, HashMap::with_capacity(size), None)
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> SimpleLRU<K, V, DefaultEvictCallback, S> {
    pub fn with_hasher(size: usize, hash_builder: S) -> Self {
        Self::new_in(
            size,
            HashMap::with_capacity_and_hasher(size, hash_builder),
            None,
        )
    }
}

impl<K: Hash + Eq, V, E: OnEvictCallback> SimpleLRU<K, V, E, DefaultHashBuilder> {
    pub fn with_evict_callback(size: usize, callback: E) -> Self {
        Self::new_in(size, HashMap::with_capacity(size), Some(callback))
    }
}

pub struct Keys<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<K, V> Clone for Keys<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<K: Debug, V> Debug for Keys<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a K> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((k, _)) => Some(k),
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.inner.next_back() {
            None => None,
            Some((k, _)) => Some(k),
        }
    }
}

impl<K, V> ExactSizeIterator for Keys<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for Keys<'_, K, V> {}

pub struct Values<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<K, V> Clone for Values<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<K: Debug, V: Debug> Debug for Values<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a V> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.inner.next_back() {
            None => None,
            Some((_, v)) => Some(v),
        }
    }
}

impl<K, V> ExactSizeIterator for Values<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for Values<'_, K, V> {}

pub struct ValuesMut<'a, K: 'a, V: 'a> {
    inner: IterMut<'a, K, V>,
}

impl<K: Debug, V: Debug> Debug for ValuesMut<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.inner.iter()).finish()
    }
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<Self::Item> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for ValuesMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.inner.next_back() {
            None => None,
            Some((_, v)) => Some(v),
        }
    }
}

impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_simple_lru() {
        let mut cache = SimpleLRU::new(5);
        cache.put(1, 1);
        cache.put(2, 2);
        cache.put(3, 3);
        cache.put(4, 4);
        cache.put(5, 5);
        cache.put(6, 6);

        assert_eq!(cache.len(), 5);

        assert_eq!(None, cache.get(&1));

        let v = cache.get_mut(&2).unwrap();
        *v = 5;
        assert_eq!(5, *cache.get(&2).unwrap());

        let v = cache.get(&3).unwrap();
        assert_eq!(3, *v);

        let v = cache.get(&4).unwrap();
        assert_eq!(4, *v);

        let v = cache.get(&5).unwrap();
        assert_eq!(5, *v);

        let v = cache.get(&6).unwrap();
        assert_eq!(6, *v);

        let oldest = cache.get_oldest().unwrap();
        assert_eq!(oldest, (&2, &5));
        let oldest = cache.remove_oldest().unwrap();
        assert_eq!(oldest, (2, 5));

        assert_eq!(cache.len(), 4);

        let v = cache.remove(&3).unwrap();
        assert_eq!(v, 3);
        assert_eq!(cache.len(), 3);

        let v = cache.peek(&4).unwrap();
        assert_eq!(*v, 4);

        let v = cache.peek_mut(&4).unwrap();
        *v = 2;
        assert_eq!(cache.get(&4), Some(&2));
    }
}
