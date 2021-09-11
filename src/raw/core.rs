use crate::raw::ll::{Entry, EntryLinkedList, KeyRef};
#[cfg(feature = "nightly")]
use crate::raw::NotKeyRef;

use alloc::boxed::Box;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::mem;
use core::ptr::drop_in_place;

#[cfg(feature = "hashbrown")]
use hashbrown::{hash_map::DefaultHashBuilder, HashMap, HashSet};

#[cfg(not(feature = "hashbrown"))]
use std::collections::{hash_map::DefaultHasher as DefaultHashBuilder, HashMap, HashSet};

use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
use alloc::vec::Vec;

pub struct RawLRU<K, V, E = DefaultEvictCallback, S = DefaultHashBuilder> {
    pub(crate) size: usize,
    pub(crate) evict_list: EntryLinkedList<K, V>,
    pub(crate) items: HashMap<KeyRef<K>, Box<Entry<K, V>>, S>,
    pub(crate) on_evict: Option<E>,
}

impl<K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> RawLRU<K, V, E, S> {
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
    ///
    /// ```rust
    /// use hashicorp_lru::RawLRU;
    ///
    /// let mut cache = RawLRU::<String, u64>::new(3);
    /// cache.put("a".to_string(), 1);
    /// cache.put("b".to_string(), 1);
    /// cache.put("c".to_string(), 1);
    /// let evicted = cache.put("d".to_string(), 1);
    /// assert!(evicted);
    /// ```
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

                    unsafe {
                        drop_in_place(old_ent.key.as_mut_ptr());
                        drop_in_place(old_ent.val.as_mut_ptr());
                    }
                    old_ent.key = mem::MaybeUninit::new(key);
                    old_ent.val = mem::MaybeUninit::new(val);

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
                        ptr: (*ent_ptr).key.as_ptr(),
                    },
                    ent,
                );
                evict
            }
            Some(ptr) => {
                self.evict_list.move_to_front(ptr);
                // key is in cache, update evict list
                unsafe {
                    mem::swap(&mut val, &mut (*(*ptr).val.as_mut_ptr()) as &mut V);
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

            Some(unsafe { &(*(*ent_ptr).val.as_ptr()) as &V })
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

            Some(unsafe { &mut (*(*ent_ptr).val.as_mut_ptr()) as &mut V })
        } else {
            None
        }
    }

    /// `get_oldest` returns the oldest entry from the cache. #key, value, isFound.
    ///
    /// This method will update the "recently used"-ness of the key. If you do not want
    /// to update the "recently used"-ness of the key, use [`peek_oldest`] instead.
    ///
    /// [`peek_oldest`]: struct.RawLRU.html#method.peek_oldest
    pub fn get_oldest(&mut self) -> Option<(&K, &V)> {
        let tail = self.evict_list.tail?.as_ptr();

        unsafe {
            match self.items.get_mut(&KeyRef::new((*tail).key.as_ptr())) {
                None => None,
                Some(ent) => {
                    let ent_ptr: *mut Entry<K, V> = &mut **ent;
                    self.evict_list.move_to_front(ent_ptr);

                    Some((&(*(*ent_ptr).key.as_ptr()), &(*(*ent_ptr).val.as_mut_ptr())))
                }
            }
        }
    }

    /// `get_oldest_mut` returns the oldest entry(key is immutable, value is mutable) from the cache. #key, value, isFound.
    ///
    /// This method will update the "recently used"-ness of the key. If you do not want
    /// to update the "recently used"-ness of the key, use [`peek_oldest_mut`] instead.
    ///
    /// [`peek_oldest_mut`]: struct.RawLRU.html#method.peek_oldest_mut
    pub fn get_oldest_mut(&mut self) -> Option<(&K, &mut V)> {
        let tail = self.evict_list.tail?.as_ptr();

        unsafe {
            match self.items.get_mut(&KeyRef::new((*tail).key.as_ptr())) {
                None => None,
                Some(ent) => {
                    let ent_ptr: *mut Entry<K, V> = &mut **ent;
                    self.evict_list.move_to_front(ent_ptr);

                    Some((
                        &(*(*ent_ptr).key.as_ptr()),
                        &mut (*(*ent_ptr).val.as_mut_ptr()),
                    ))
                }
            }
        }
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
                    unsafe {
                        on_evict.on_evict(&(*(*ent_ptr).key.as_ptr()), &(*(*ent_ptr).val.as_ptr()));
                    }
                }

                Some(unsafe { Box::from_raw(ent_ptr).val.assume_init() })
            }
        }
    }

    pub fn remove_oldest(&mut self) -> Option<(K, V)> {
        let tail = self.evict_list.tail?.as_ptr();
        unsafe {
            match self.items.remove(&KeyRef::new((*tail).key.as_ptr())) {
                None => None,
                Some(ent) => {
                    let ent_ptr = Box::leak(ent);
                    self.evict_list.detach(ent_ptr);

                    if let Some(on_evict) = &self.on_evict {
                        on_evict.on_evict(&(*(*ent_ptr).key.as_ptr()), &(*(*ent_ptr).val.as_ptr()));
                    }

                    let ent = Box::from_raw(ent_ptr);
                    Some((ent.key.assume_init(), ent.val.assume_init()))
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

    /// `peek` returns key's value without updating the "recently used"-ness of the key.
    pub fn peek<Q>(&self, key: &Q) -> Option<&V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.items.get(key) {
            None => None,
            Some(ent) => unsafe { Some(&(*(*ent).val.as_ptr())) },
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
            Some(ent) => unsafe { Some(&mut (*(*ent).val.as_mut_ptr())) },
        }
    }

    /// `peek_oldest` returns the oldest entry without updating the "recently used"-ness of the key.
    /// If you want to update the "recently used"-ness of the key, use [`get_oldest`]
    ///
    /// [`get_oldest`]: struct.RawLRU.html#method.get_oldest
    pub fn peek_oldest(&self) -> Option<(&K, &V)> {
        self.evict_list.back_key_value()
    }

    /// `peek_oldest_mut` returns the oldest entry(key is immutable, value is mutable) without updating the "recently used"-ness of the key.
    /// If you want to update the "recently used"-ness of the key, use [`get_oldest_mut`]
    ///
    /// [`get_oldest_mut`]: struct.RawLRU.html#method.get_oldest_mut
    pub fn peek_oldest_mut(&mut self) -> Option<(&K, &mut V)> {
        self.evict_list.back_key_value_mut()
    }

    /// `contains` checks if a key exists in cache without updating the recent-ness.
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.items.contains_key(key)
    }

    /// `resize` resizes cache, returning number evicted.
    pub fn resize(&mut self, size: usize) -> u64 {
        if self.len() > size {
            let delta = self.len() - size;
            for _ in 0..delta {
                let _ = self.remove_oldest();
            }

            self.size = size;
            delta as u64
        } else {
            self.size = size;
            0
        }
    }
}

#[cfg(feature = "nightly")]
impl<K: Hash + Eq + NotKeyRef + Clone, V: Clone> From<&[(K, V)]> for RawLRU<K, V> {
    fn from(vals: &[(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

#[cfg(feature = "nightly")]
impl<K: Hash + Eq + NotKeyRef + Clone, V: Clone> From<&mut [(K, V)]> for RawLRU<K, V> {
    fn from(vals: &mut [(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

#[cfg(not(feature = "nightly"))]
impl<K: Hash + Eq + Clone, V: Clone> From<&[(K, V)]> for RawLRU<K, V> {
    fn from(vals: &[(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

#[cfg(not(feature = "nightly"))]
impl<K: Hash + Eq + Clone, V: Clone> From<&mut [(K, V)]> for RawLRU<K, V> {
    fn from(vals: &mut [(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

impl<K: Hash + Eq, V, const N: usize> From<[(K, V); N]> for RawLRU<K, V> {
    fn from(vals: [(K, V); N]) -> Self {
        let mut this = Self::new(vals.len());
        for (k, v) in vals {
            this.put(k, v);
        }
        this
    }
}

macro_rules! impl_from_collections {
    ($($t:ty),*) => {
        $(
        #[cfg(feature = "nightly")]
        impl<K: Hash + Eq + NotKeyRef, V> From<$t> for RawLRU<K, V> {
            fn from(vals: $t) -> Self {
                let mut this = Self::new(vals.len());
                for (k, v) in vals {
                    if !this.contains(&k) {
                        this.put(k, v);
                    }
                }
                this
            }
        }
        #[cfg(not(feature = "nightly"))]
        impl<K: Hash + Eq, V> From<$t> for RawLRU<K, V>
        {
            fn from(vals: $t) -> Self {
                let mut this = Self::new(vals.len());
                for (k, v) in vals {
                    this.put(k, v);
                }
                this
            }
        }
        )*
    }
}

impl_from_collections!(
    Vec<(K, V)>,
    VecDeque<(K, V)>,
    LinkedList<(K, V)>,
    HashSet<(K, V)>,
    BTreeSet<(K,V)>,
    BinaryHeap<(K, V)>,
    HashMap<K, V>,
    BTreeMap<K, V>
);

impl<K: Hash + Eq, V> RawLRU<K, V> {
    pub fn new(size: usize) -> Self {
        Self::new_in(size, HashMap::with_capacity(size), None)
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> RawLRU<K, V, DefaultEvictCallback, S> {
    pub fn with_hasher(size: usize, hash_builder: S) -> Self {
        Self::new_in(
            size,
            HashMap::with_capacity_and_hasher(size, hash_builder),
            None,
        )
    }
}

impl<K: Hash + Eq, V, E: OnEvictCallback> RawLRU<K, V, E, DefaultHashBuilder> {
    pub fn with_evict_callback(size: usize, callback: E) -> Self {
        Self::new_in(size, HashMap::with_capacity(size), Some(callback))
    }
}

impl<K, V, E, S> Drop for RawLRU<K, V, E, S> {
    fn drop(&mut self) {
        self.items.values_mut().for_each(|ent| unsafe {
            drop_in_place(ent.key.as_mut_ptr());
            drop_in_place(ent.val.as_mut_ptr());
        });
    }
}

/// `DefaultEvictCallback` is a noop evict callback.
#[derive(Debug, Clone)]
pub struct DefaultEvictCallback;

impl OnEvictCallback for DefaultEvictCallback {
    fn on_evict<K: Hash + Eq, V>(&self, _: &K, _: &V) {}
}

pub trait OnEvictCallback {
    fn on_evict<K: Hash + Eq, V>(&self, key: &K, val: &V);
}
