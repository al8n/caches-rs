use crate::raw::ll::{EntryNode, EntryNodeLinkedList, KeyRef};
#[cfg(feature = "nightly")]
use crate::raw::NotKeyRef;
use crate::{DefaultEvictCallback, DefaultHashBuilder, OnEvictCallback};
use alloc::boxed::Box;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::mem;
use core::ptr::drop_in_place;

#[cfg(feature = "hashbrown")]
use hashbrown::{HashMap, HashSet};

#[cfg(not(feature = "hashbrown"))]
use std::collections::{HashMap, HashSet};

use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
use alloc::vec::Vec;

pub struct RawLRU<'a, K, V, E = DefaultEvictCallback, S = DefaultHashBuilder> {
    pub(crate) size: usize,
    pub(crate) evict_list: EntryNodeLinkedList<K, V>,
    pub(crate) items: HashMap<KeyRef<K>, Box<EntryNode<K, V>>, S>,
    on_evict: Option<&'a E>,
}

impl<'a, K: Clone, V: Clone, E: Clone, S: Clone> Clone for RawLRU<'a, K, V, E, S> {
    fn clone(&self) -> Self {
        Self {
            size: self.size,
            evict_list: self.evict_list.clone(),
            items: self.items.clone(),
            on_evict: self.on_evict.clone(),
        }
    }
}

impl<'a, K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> RawLRU<'a, K, V, E, S> {
    fn new_in(
        size: usize,
        items: HashMap<KeyRef<K>, Box<EntryNode<K, V>>, S>,
        on_evict: Option<&'a E>,
    ) -> Self {
        assert_ne!(size, 0, "invalid cache size {}", 0);
        Self {
            size,
            evict_list: EntryNodeLinkedList::new(),
            items,
            on_evict,
        }
    }

    /// `put` puts a value to the cache, returns evicted key-value pair if an eviction occurred and
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
    pub fn put(&mut self, key: K, mut val: V) -> Option<(K, V)> {
        // Avoid `Option::map` because it bloats LLVM IR.
        let ent_ptr = self.items.get_mut(&KeyRef::new(&key)).map(|ent| {
            let ent_ptr: *mut EntryNode<K, V> = &mut **ent;
            ent_ptr
        });

        match ent_ptr {
            // Verify size not exceed
            None => {
                if self.evict_list.len >= self.size {
                    let (old_ek, mut old_ev) = self.remove_oldest().unwrap();
                    let ent = Box::new(EntryNode::new(key, val));
                    self.put_in(ent);

                    unsafe { Some((old_ek, old_ev)) }
                } else {
                    let ent = Box::new(EntryNode::new(key, val));
                    self.put_in(ent);
                    None
                }
            }
            // Update value
            Some(ptr) => {
                self.evict_list.move_to_front(ptr);
                // key is in cache, update evict list
                unsafe {
                    mem::swap(&mut val, &mut (*(*ptr).val.as_mut_ptr()) as &mut V);
                }
                None
            }
        }
    }

    fn put_in(&mut self, mut ent: Box<EntryNode<K, V>>) {
        let ent_ptr = &mut *ent;
        self.evict_list.attach(ent_ptr);

        self.items.insert(
            KeyRef {
                ptr: (*ent_ptr).key.as_ptr(),
            },
            ent,
        );
    }

    pub fn get<Q>(&mut self, key: &Q) -> Option<&V>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(ent) = self.items.get_mut(key) {
            let ent_ptr: *mut EntryNode<K, V> = &mut **ent;
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
            let ent_ptr: *mut EntryNode<K, V> = &mut **ent;
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
                    let ent_ptr: *mut EntryNode<K, V> = &mut **ent;
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
                    let ent_ptr: *mut EntryNode<K, V> = &mut **ent;
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
    pub fn remove<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        KeyRef<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.items.remove(key) {
            None => None,
            Some(ent) => {
                let ent_ptr = Box::leak(ent);
                self.evict_list.detach(ent_ptr);

                // Safety: the key and value must be initialized because
                // we can get the entry pointer from items.
                unsafe {
                    let ent = Box::from_raw(ent_ptr);
                    Some((ent.key.assume_init(), ent.val.assume_init()))
                }
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

                    // Safety: the key and value must be initialized because
                    // we can get the entry pointer from items.
                    let ent = Box::from_raw(ent_ptr);
                    let (ek, ev) = (ent.key.assume_init(), ent.val.assume_init());
                    self.cb(&ek, &ev);
                    Some((ek, ev))
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
        for (k, v) in self.iter() {
            self.cb(k, v)
        }
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

    /// `contains_or_put` checks if a key is in the cache without updating the
    /// recent-ness or deleting it for being stale, and if not, adds the value.
    /// Returns whether found and whether an eviction occurred.
    pub fn contains_or_put(&mut self, key: K, val: V) -> (Option<(K, V)>, bool) {
        if !self.contains(&key) {
            let ent = self.put(key, val);
            (ent, false)
        } else {
            (None, true)
        }
    }

    /// `resize` resizes cache, returning the number of evicted entries.
    pub fn resize(&mut self, size: usize) -> u64 {
        let ctr = if self.len() > size {
            let delta = self.len() - size;
            (0..delta).for_each(|_| {
                let _ = self.remove_oldest();
            });
            delta as u64
        } else {
            0u64
        };
        self.size = size;
        ctr
    }

    #[inline]
    fn cb(&self, k: &K, v: &V) {
        if let Some(cb) = self.on_evict {
            cb.on_evict(k, v)
        }
    }
}

#[cfg(feature = "nightly")]
impl<'a, K: Hash + Eq + NotKeyRef + Clone, V: Clone> From<&[(K, V)]> for RawLRU<'a, K, V> {
    fn from(vals: &[(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

#[cfg(feature = "nightly")]
impl<'a, K: Hash + Eq + NotKeyRef + Clone, V: Clone> From<&mut [(K, V)]> for RawLRU<'a, K, V> {
    fn from(vals: &mut [(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

impl<'a, K: Hash + Eq + Clone, V: Clone> From<&[(K, V)]> for RawLRU<'a, K, V> {
    fn from(vals: &[(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

impl<'a, K: Hash + Eq + Clone, V: Clone> From<&mut [(K, V)]> for RawLRU<'a, K, V> {
    fn from(vals: &mut [(K, V)]) -> Self {
        Self::from(vals.to_vec())
    }
}

#[cfg(feature = "nightly")]
impl<'a, K: Hash + Eq, V, const N: usize> From<[(K, V); N]> for RawLRU<'a, K, V> {
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
        impl<'a, K: Hash + Eq, V> From<$t> for RawLRU<'a, K, V>
        {
            fn from(vals: $t) -> Self {
                let mut this = Self::new(vals.len());
                for (k, v) in vals {
                    this.contains_or_put(k, v);
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

impl<'a, K: Hash + Eq, V> RawLRU<'a, K, V> {
    pub fn new(size: usize) -> Self {
        Self::new_in(size, HashMap::with_capacity(size), None)
    }
}

impl<'a, K: Hash + Eq, V, S: BuildHasher> RawLRU<'a, K, V, DefaultEvictCallback, S> {
    pub fn with_hasher(size: usize, hash_builder: S) -> Self {
        Self::new_in(
            size,
            HashMap::with_capacity_and_hasher(size, hash_builder),
            None,
        )
    }
}

impl<'a, K: Hash + Eq, V, E: OnEvictCallback> RawLRU<'a, K, V, E, DefaultHashBuilder> {
    pub fn with_evict_callback(size: usize, cb: &'a E) -> Self {
        Self::new_in(size, HashMap::with_capacity(size), Some(cb))
    }
}

impl<'a, K, V, E, S> Drop for RawLRU<'a, K, V, E, S> {
    fn drop(&mut self) {
        self.items.values_mut().for_each(|ent| unsafe {
            drop_in_place(ent.key.as_mut_ptr());
            drop_in_place(ent.val.as_mut_ptr());
        });
    }
}
