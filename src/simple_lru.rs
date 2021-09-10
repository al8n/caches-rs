use crate::{LRUCache, Entry, CacheError, EntryLinkedList, KeyRef, DefaultEvictCallback, OnEvictCallback};

use alloc::boxed::Box;
use core::hash::{BuildHasher, Hash, Hasher};
use core::iter::FusedIterator;
use core::mem;
use core::ptr::{NonNull, drop_in_place};
use hashbrown::hash_map::DefaultHashBuilder;
use hashbrown::HashMap;
use alloc::collections::LinkedList;
use core::borrow::{BorrowMut, Borrow};
use alloc::vec::Vec;
use core::option::Option::Some;
use std::fmt::Debug;


pub struct SimpleLRU<K, V, E = DefaultEvictCallback, S = DefaultHashBuilder>
{
    size: usize,
    evict_list: EntryLinkedList<K, V>,
    items: HashMap<KeyRef<K>, NonNull<Entry<K, V>>, S>,
    on_evict: Option<E>,
}

impl<K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> SimpleLRU<K, V, E, S> {
    pub fn with_callback_and_hasher(size: usize, callback: E, hash_builder: S) -> Self {
        Self::build(size, HashMap::with_capacity_and_hasher(size, hash_builder), Some(callback))
    }

    fn build(size: usize, items: HashMap<KeyRef<K>, NonNull<Entry<K, V>>, S>, on_evict: Option<E>) -> Self {
        Self {
            size,
            evict_list: EntryLinkedList::new(),
            items,
            on_evict,
        }
    }

    // pub fn new(size: usize) -> Self {
    //     Self::build(size, HashMap::new())
    // }

    /// `put` puts a value to the cache, returns true if an eviction occurred and
    /// updates the "recently used"-ness of the key.
    pub fn put(&mut self, key: K, mut val: V) -> bool {

        // Avoid `Option::map` because it bloats LLVM IR.
        let ent_ptr = self.items.get_mut(&KeyRef::new(&key));

        match ent_ptr {
            None => {
                let evict = self.evict_list.len > self.size;
                // Verify size not exceed
                let mut ent: NonNull<Entry<K, V>> = if evict {
                    let old_key = self.evict_list.back().unwrap();
                    let old_key = KeyRef::new(old_key);
                    let mut old_ent = self.items.remove(&old_key).unwrap();

                    unsafe {
                        let oe_ptr = old_ent.as_ptr();
                        (*oe_ptr).key = key;
                        (*oe_ptr).val = val;
                    }
                    self.evict_list.detach(old_ent);
                    old_ent
                } else {
                    unsafe { NonNull::new_unchecked(&mut Entry::new(key, val)) }
                };

                self.evict_list.attach(ent);
                let key = unsafe { KeyRef::new(&(*ent.as_ptr()).key) };

                self.items.insert(key, ent);
                evict
            }
            Some(ptr) => {
                self.evict_list.move_to_front(*ptr);
                // key is in cache, update evict list
                unsafe { mem::swap(&mut val,  &mut (*ptr.as_ptr()).val); }
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
            self.evict_list.move_to_front(*ent);

            unsafe  {
                Some(&(*ent.as_ptr()).val)
            }
        } else {
            None
        }
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
        where
            KeyRef<K>: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        if let Some(ent) = self.items.get_mut(&KeyRef::new(key)) {
            self.evict_list.move_to_front(*ent);
            unsafe { Some(&mut (*ent.as_ptr()).val) }
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
                let ent_ptr = ent.as_ptr();
                self.evict_list.detach(ent);

                if let Some(on_evict) = &self.on_evict {
                    unsafe { on_evict.on_evict(&(*ent_ptr).key, &(*ent_ptr).val); }
                }

                Some(unsafe {Box::from_raw(ent_ptr).val})
            }
        }
    }

    pub fn remove_oldest(&mut self) -> Option<(K, V)> {
        let tail = self.evict_list.tail?;
        unsafe {
            self.evict_list.detach(tail);

            let tail_ptr = tail.as_ptr();
            self.items.remove(&KeyRef::new(&(*tail_ptr).key));

            let entry = Box::from_raw(tail_ptr);
            Some((entry.key, entry.val))
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

    /// `keys` returns a slice of the keys in the cache, from oldest to newest
    pub fn keys(&self) -> Vec<K> {
        todo!()
    }

    /// `peek` returns key's value without updating the "recently used"-ness of the key.
    pub fn peek<Q>(&self, key: &Q) -> Option<&V>
        where
            KeyRef<K>: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        match self.items.get(key) {
            None => None,
            Some(k) => unsafe { Some(&((*k.as_ptr()).val))},
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
            Some(k) => unsafe { Some(&mut ((*k.as_ptr()).val)) },
        }
    }

    /// `contains` checks if a key exists in cache without updating the recent-ness.
    pub fn contains<Q>(&self, key: &Q) -> bool
    where KeyRef<K>: Borrow<Q>,
          Q: Hash + Eq + ?Sized,
    {
        self.items.contains_key(key)
    }
}

impl<K: Hash + Eq, V> SimpleLRU<K, V, DefaultEvictCallback, DefaultHashBuilder> {
    pub fn new(size: usize) -> Self {
        Self::build(size, HashMap::with_capacity(size), None)
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> SimpleLRU<K, V, DefaultEvictCallback, S> {
    pub fn with_hasher(size: usize, hash_builder: S) -> Self {
        Self::build(size, HashMap::with_capacity_and_hasher(size, hash_builder), None)
    }
}

impl<K: Hash + Eq, V, E: OnEvictCallback> SimpleLRU<K, V, E, DefaultHashBuilder> {
    pub fn with_evict_callback(size: usize, callback: E) -> Self {
        Self::build(size, HashMap::with_capacity(size), Some(callback))
    }
}

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

        assert_eq!(cache.evict_list.len, 5);
        assert_eq!(cache.items.len(), 5);

        for ent in cache.items.keys() {
            println!("{:p}", ent);
        }

        let v = cache.get_mut(&1).unwrap();
        *v = 5;
        assert_eq!(5, *cache.get(&1).unwrap());
        //
        // let v = cache.get(&2).unwrap();
        // assert_eq!(2, *v);
        //
        // let v = cache.get(&3).unwrap();
        // assert_eq!(3, *v);
        //
        // let v = cache.get(&4).unwrap();
        // assert_eq!(4, *v);
        //
        // let v = cache.get(&5).unwrap();
        // assert_eq!(5, *v);

        // let r1 = cache.remove(&2).unwrap();
        // assert_eq!(r1, 2);
        //
        // let oldest = cache.get_oldest().unwrap();
        // assert_eq!(oldest, (&3, &3));
        // let oldest = cache.remove_oldest().unwrap();
        // assert_eq!(oldest, (3, 3));
    }
}