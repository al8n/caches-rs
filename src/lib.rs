#![no_std]
#![feature(auto_traits)]
#![feature(negative_impls)]

extern crate alloc;
extern crate hashbrown;

mod simple_lru;

pub use simple_lru::SimpleLRU;

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::fmt::{Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem;
use core::ptr::NonNull;

/// `LRUCache` is the interface for simple LRU cache.
pub trait LRUCache<K, V> {
    /// `add` adds a value to the cache, returns true if an eviction occurred and
    /// updates the "recently used"-ness of the key.
    fn add(&mut self, key: K, val: V) -> bool;

    /// `get` returns key's value from the cache and
    /// updates the "recently used"-ness of the key. #value, isFound
    fn get(&self, key: K) -> Option<V>;

    /// `contains` checks if a key exists in cache without updating the recent-ness.
    fn contains(&self, key: K) -> bool;

    /// `peek` returns key's value without updating the "recently used"-ness of the key.
    fn peek(&self, key: K) -> Option<V>;

    /// `remove` tries remove a key from the cache.
    fn remove(&mut self, key: K) -> bool;

    /// `remove_oldest` removes the oldest entry from cache
    fn remove_oldest(&mut self) -> Option<(K, V)>;

    /// `get_oldest` returns the oldest entry from the cache. #key, value, isFound
    fn get_oldest(&self) -> Option<(K, V)>;

    /// `keys` returns a slice of the keys in the cache, from oldest to newest
    fn keys(&self) -> Vec<K>;

    /// `len` returns the number of items in the cache.
    fn len(&self) -> usize;

    /// `purge` clears the number of items in the cache.
    fn purge(&mut self);

    /// `resize` resizes cache, returning number evicted.
    fn resize(&mut self, size: usize) -> u64;
}

pub struct KeyRef<T> {
    ptr: *const T,
}

impl<T> KeyRef<T> {
    fn new(ptr: *const T) -> Self {
        Self { ptr }
    }
}

impl<K: Hash> Hash for KeyRef<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe { (*self.ptr).hash(state) }
    }
}
impl<K: PartialEq> PartialEq for KeyRef<K> {
    fn eq(&self, other: &KeyRef<K>) -> bool {
        unsafe { (*self.ptr).eq(&*other.ptr) }
    }
}

impl<K: Eq> Eq for KeyRef<K> {}

pub auto trait NotKeyRef {}

impl<K> !NotKeyRef for KeyRef<K> {}

impl<K, D> Borrow<D> for KeyRef<K>
where
    K: Borrow<D>,
    D: NotKeyRef + ?Sized,
{
    fn borrow(&self) -> &D {
        unsafe { &*self.ptr }.borrow()
    }
}

/// `Entry` is used to hold a key-value pair.
struct Entry<K, V> {
    key: K,
    val: V,
    prev: Option<NonNull<Entry<K, V>>>,
    next: Option<NonNull<Entry<K, V>>>,
}

impl<K: Debug, V: Debug> Debug for Entry<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Entry")
            .field(&self.key)
            .field(&self.val)
            .finish()
    }
}

impl<K, V> Entry<K, V> {
    fn new(key: K, val: V) -> Self {
        Self {
            key,
            val,
            prev: None,
            next: None,
        }
    }
}

/// `EntryLinkedList` is a double direction linked list.
///
/// For LRU, read and write should be O(1), so we need a
/// double direct linked list.
struct EntryLinkedList<K, V> {
    head: Option<NonNull<Entry<K, V>>>,
    tail: Option<NonNull<Entry<K, V>>>,
    len: usize,
    marker: PhantomData<Box<Entry<K, V>>>,
}

impl<K, V> Default for EntryLinkedList<K, V> {
    fn default() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }
}

impl<K: Debug, V: Debug> Debug for EntryLinkedList<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<K, V> EntryLinkedList<K, V> {
    fn new() -> Self {
        Self::default()
    }

    /// `move_to_front` moves `ent` to the front of `EntryLinkedList`.
    /// If `ent` is not an element of the list, the list is not modified.
    /// The element must not be nil.
    fn move_to_front(&mut self, ent: *mut Entry<K, V>) {
        self.detach(ent);
        self.attach(ent);
    }

    fn detach(&mut self, ent: *mut Entry<K, V>) {
        unsafe {
            // Not creating new mutable (unique!) references overlapping `element`.
            match (*ent).prev {
                Some(prev) => (*prev.as_ptr()).next = (*ent).next,
                // this node is the head node
                None => self.head = (*ent).next,
            };

            match (*ent).next {
                Some(next) => (*next.as_ptr()).prev = (*ent).prev,
                // this node is the tail node
                None => self.tail = (*ent).prev,
            };
            self.len -= 1;
        }
    }

    // move entry to front
    fn attach(&mut self, mut ent: *mut Entry<K, V>) {
        unsafe {
            (*ent).next = self.head;
            (*ent).prev = None;

            let node = Some(ent.as_mut().unwrap().into());

            match self.head {
                None => self.tail = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = node,
            }

            self.head = node;
            self.len += 1;
        }
    }

    fn pop_front(&mut self) -> Option<(K, V)> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.head.map(|ent| unsafe {
            let ent = Box::from_raw(ent.as_ptr());
            self.head = ent.next;

            match self.head {
                None => self.tail = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = None,
            }

            self.len -= 1;
            (ent.key, ent.val)
        })
    }

    fn pop_back(&mut self) -> Option<(K, V)> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.tail.map(|ent| unsafe {
            let ent = Box::from_raw(ent.as_ptr());
            self.tail = ent.prev;

            match self.tail {
                None => self.head = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = None,
            }

            self.len -= 1;
            (ent.key, ent.val)
        })
    }

    fn back(&self) -> Option<&K> {
        unsafe { self.tail.as_ref().map(|ent| &ent.as_ref().key) }
    }

    fn back_key_value(&self) -> Option<(&K, &V)> {
        unsafe {
            self.tail.as_ref().map(|ent| {
                let ent_ref = ent.as_ref();
                (&ent_ref.key, &ent_ref.val)
            })
        }
    }

    fn back_key_value_mut(&mut self) -> Option<(&mut K, &mut V)> {
        unsafe {
            self.tail.as_mut().map(|ent| {
                let ent_ref = ent.as_mut();
                (&mut ent_ref.key, &mut ent_ref.val)
            })
        }
    }

    fn clear(&mut self) {
        *self = Self::new();
    }

    fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }
}

impl<K, V> IntoIterator for EntryLinkedList<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { list: self }
    }
}

impl<'a, K, V> IntoIterator for &'a EntryLinkedList<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut EntryLinkedList<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

pub struct IntoIter<K, V> {
    list: EntryLinkedList<K, V>,
}

impl<K: Debug, V: Debug> Debug for IntoIter<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("IntoIter").field(&self.list).finish()
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.pop_back()
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {}

impl<K, V> FusedIterator for IntoIter<K, V> {}

pub struct Iter<'a, K: 'a, V: 'a> {
    head: Option<NonNull<Entry<K, V>>>,
    tail: Option<NonNull<Entry<K, V>>>,
    len: usize,
    marker: PhantomData<&'a Entry<K, V>>,
}

impl<K: Debug, V: Debug> Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Iter")
            .field(&*mem::ManuallyDrop::new(EntryLinkedList {
                head: self.head,
                tail: self.tail,
                len: self.len,
                marker: PhantomData,
            }))
            .field(&self.len)
            .finish()
    }
}

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Iter { ..*self }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &*ent.as_ptr();
                self.len -= 1;
                self.head = ent.next;
                (&(ent.key), &(ent.val))
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &*ent.as_ptr();
                self.len -= 1;
                self.tail = ent.prev;
                (&(ent.key), &(ent.val))
            })
        }
    }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {}

pub struct IterMut<'a, K: 'a, V: 'a> {
    head: Option<NonNull<Entry<K, V>>>,
    tail: Option<NonNull<Entry<K, V>>>,
    len: usize,
    marker: PhantomData<&'a Entry<K, V>>,
}

impl<K: Debug, V: Debug> Debug for IterMut<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("IterMut")
            .field(&*mem::ManuallyDrop::new(EntryLinkedList {
                head: self.head,
                tail: self.tail,
                len: self.len,
                marker: PhantomData,
            }))
            .field(&self.len)
            .finish()
    }
}

impl<K, V> IterMut<'_, K, V> {
    fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &mut *ent.as_ptr();
                self.len -= 1;
                self.head = ent.next;
                (&(ent.key), &mut (ent.val))
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &mut *ent.as_ptr();
                self.len -= 1;
                self.tail = ent.prev;
                (&(ent.key), &mut (ent.val))
            })
        }
    }
}

impl<K, V> FusedIterator for IterMut<'_, K, V> {}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {}

/// `DefaultEvictCallback` is a noop evict callback.
#[derive(Debug, Clone)]
pub struct DefaultEvictCallback;

impl OnEvictCallback for DefaultEvictCallback {
    fn on_evict<K: Hash + Eq, V>(&self, _: &K, _: &V) {}
}

pub trait OnEvictCallback {
    fn on_evict<K: Hash + Eq, V>(&self, key: &K, val: &V);
}

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
