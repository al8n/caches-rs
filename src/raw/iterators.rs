use core::fmt::{Debug, Formatter};
use core::hash::{BuildHasher, Hash};
use core::iter::{FromIterator, FusedIterator};
use core::marker::PhantomData;
use core::mem;
use core::ptr::NonNull;

use crate::raw::core::RawLRU;
use crate::raw::ll::{Entry, EntryLinkedList};
use crate::OnEvictCallback;

impl<K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> RawLRU<K, V, E, S> {
    /// `iter` returns an iter of the key-value pairs in the cache, from newest to oldest
    pub fn iter(&self) -> Iter<'_, K, V> {
        self.evict_list.iter()
    }

    /// `iter_mut` returns an iter of the key-value pairs(mutable) in the cache, from newest to oldest
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        self.evict_list.iter_mut()
    }

    /// `reversed_iter` returns an iter of the key-value pairs in the cache, from oldest to newest
    pub fn reversed_iter(&self) -> ReversedIter<'_, K, V> {
        self.evict_list.reversed_iter()
    }

    /// `reversed_iter_mut` returns an iter of the key-value pairs(mutable) in the cache, from oldest to newest
    pub fn reversed_iter_mut(&mut self) -> ReversedIterMut<'_, K, V> {
        self.evict_list.reversed_iter_mut()
    }

    /// `keys` returns an iter of the keys in the cache, from newest to oldest
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys {
            inner: self.evict_list.iter(),
        }
    }

    /// `reversed_keys` returns an iter of the keys in the cache, from oldest to newest
    pub fn reversed_keys(&self) -> ReversedKeys<'_, K, V> {
        ReversedKeys {
            inner: self.evict_list.reversed_iter(),
        }
    }

    /// `values` returns an iter of the values in the cache, from newest to oldest
    pub fn values(&self) -> Values<'_, K, V> {
        Values {
            inner: self.evict_list.iter(),
        }
    }

    /// `reversed_values` returns an iter of the values in the cache, from oldest to newest
    pub fn reversed_values(&self) -> ReversedValues<'_, K, V> {
        ReversedValues {
            inner: self.evict_list.reversed_iter(),
        }
    }

    /// `values_mut` returns an iter of the values(mutable) in the cache, from newest to oldest
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.evict_list.iter_mut(),
        }
    }

    /// `reversed_values_mut` returns an iter of the values(mutable) in the cache, from oldest to newest
    pub fn reversed_values_mut(&mut self) -> ReversedValuesMut<'_, K, V> {
        ReversedValuesMut {
            inner: self.evict_list.reversed_iter_mut(),
        }
    }
}

impl<K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> IntoIterator for RawLRU<K, V, E, S> {
    type Item = (K, V);
    type IntoIter = RawLRUIntoIter<K, V, E, S>;

    fn into_iter(self) -> Self::IntoIter {
        RawLRUIntoIter { list: self }
    }
}

impl<'a, K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> IntoIterator
    for &'a RawLRU<K, V, E, S>
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K: Hash + Eq, V, E: OnEvictCallback, S: BuildHasher> IntoIterator
    for &'a mut RawLRU<K, V, E, S>
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct Keys<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<K, V> Clone for Keys<'_, K, V> {
    #[inline]
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

    fn next(&mut self) -> Option<&'a K> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((k, _)) => Some(k),
            None => None,
        }
    }
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
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for Keys<'_, K, V> {}

pub struct ReversedKeys<'a, K: 'a, V: 'a> {
    inner: ReversedIter<'a, K, V>,
}

impl<K, V> Clone for ReversedKeys<'_, K, V> {
    #[inline]
    fn clone(&self) -> Self {
        ReversedKeys {
            inner: self.inner.clone(),
        }
    }
}

impl<K: Debug, V> Debug for ReversedKeys<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K, V> Iterator for ReversedKeys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((k, _)) => Some(k),
            None => None,
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for ReversedKeys<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.inner.next_back() {
            None => None,
            Some((k, _)) => Some(k),
        }
    }
}

impl<K, V> ExactSizeIterator for ReversedKeys<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for ReversedKeys<'_, K, V> {}

pub struct Values<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<K, V> Clone for Values<'_, K, V> {
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

    fn next(&mut self) -> Option<&'a V> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }
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
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for Values<'_, K, V> {}

pub struct ReversedValues<'a, K: 'a, V: 'a> {
    inner: ReversedIter<'a, K, V>,
}

impl<K, V> Clone for ReversedValues<'_, K, V> {
    fn clone(&self) -> Self {
        ReversedValues {
            inner: self.inner.clone(),
        }
    }
}

impl<K: Debug, V: Debug> Debug for ReversedValues<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K, V> Iterator for ReversedValues<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for ReversedValues<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.inner.next_back() {
            None => None,
            Some((_, v)) => Some(v),
        }
    }
}

impl<K, V> ExactSizeIterator for ReversedValues<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for ReversedValues<'_, K, V> {}

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

    fn next(&mut self) -> Option<Self::Item> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }
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
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

pub struct ReversedValuesMut<'a, K: 'a, V: 'a> {
    inner: ReversedIterMut<'a, K, V>,
}

impl<K: Debug, V: Debug> Debug for ReversedValuesMut<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.inner.iter()).finish()
    }
}

impl<'a, K, V> Iterator for ReversedValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for ReversedValuesMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.inner.next_back() {
            None => None,
            Some((_, v)) => Some(v),
        }
    }
}

impl<K, V> ExactSizeIterator for ReversedValuesMut<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for ReversedValuesMut<'_, K, V> {}

impl<K, V> EntryLinkedList<K, V> {
    pub(crate) fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    pub(crate) fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    pub(crate) fn iter_entry(&self) -> IterEntry<'_, K, V> {
        IterEntry {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    pub(crate) fn iter_entry_mut(&mut self) -> IterEntryMut<'_, K, V> {
        IterEntryMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    fn reversed_iter(&self) -> ReversedIter<'_, K, V> {
        ReversedIter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    fn reversed_iter_mut(&self) -> ReversedIterMut<'_, K, V> {
        ReversedIterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }
}

impl<K, V> FromIterator<Entry<K, V>> for EntryLinkedList<K, V> {
    fn from_iter<T: IntoIterator<Item = Entry<K, V>>>(iter: T) -> Self {
        let mut list = Self::new();
        list.extend(iter);
        list
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

pub struct RawLRUIntoIter<K, V, E, S> {
    list: RawLRU<K, V, E, S>,
}

impl<K: Debug, V: Debug, E, S> Debug for RawLRUIntoIter<K, V, E, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("RawLRUIntoIter")
            .field(&self.list.evict_list)
            .finish()
    }
}

impl<K, V, E, S> Iterator for RawLRUIntoIter<K, V, E, S> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.list.evict_list.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.evict_list.len, Some(self.list.evict_list.len))
    }
}

impl<K, V, E, S> DoubleEndedIterator for RawLRUIntoIter<K, V, E, S> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.evict_list.pop_back()
    }
}

impl<K, V, E, S> ExactSizeIterator for RawLRUIntoIter<K, V, E, S> {}

impl<K, V, E, S> FusedIterator for RawLRUIntoIter<K, V, E, S> {}

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
                (&(*(*ent).key.as_ptr()), &(*(*ent).val.as_ptr()))
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
                (&(*(*ent).key.as_ptr()), &(*(*ent).val.as_ptr()))
            })
        }
    }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {}

pub struct ReversedIter<'a, K: 'a, V: 'a> {
    head: Option<NonNull<Entry<K, V>>>,
    tail: Option<NonNull<Entry<K, V>>>,
    len: usize,
    marker: PhantomData<&'a Entry<K, V>>,
}

impl<'a, K, V> Clone for ReversedIter<'a, K, V> {
    fn clone(&self) -> Self {
        ReversedIter { ..*self }
    }
}

impl<K: Debug, V: Debug> Debug for ReversedIter<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("ReversedIter")
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

impl<'a, K, V> Iterator for ReversedIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &*ent.as_ptr();
                self.len -= 1;
                self.tail = ent.prev;
                (&(*(*ent).key.as_ptr()), &(*(*ent).val.as_ptr()))
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

impl<'a, K, V> DoubleEndedIterator for ReversedIter<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &*ent.as_ptr();
                self.len -= 1;
                self.head = ent.next;
                (&(*(*ent).key.as_ptr()), &(*(*ent).val.as_ptr()))
            })
        }
    }
}

impl<K, V> FusedIterator for ReversedIter<'_, K, V> {}

impl<K, V> ExactSizeIterator for ReversedIter<'_, K, V> {}

pub struct IterMut<'a, K: 'a, V: 'a> {
    pub(crate) head: Option<NonNull<Entry<K, V>>>,
    pub(crate) tail: Option<NonNull<Entry<K, V>>>,
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
                (&(*(*ent).key.as_ptr()), &mut (*(*ent).val.as_mut_ptr()))
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
                (&(*(*ent).key.as_ptr()), &mut (*(*ent).val.as_mut_ptr()))
            })
        }
    }
}

impl<K, V> FusedIterator for IterMut<'_, K, V> {}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {}

pub(crate) struct IterEntryMut<'a, K: 'a, V: 'a> {
    head: Option<NonNull<Entry<K, V>>>,
    tail: Option<NonNull<Entry<K, V>>>,
    len: usize,
    marker: PhantomData<&'a Entry<K, V>>,
}

impl<'a, K, V> Iterator for IterEntryMut<'a, K, V> {
    type Item = &'a mut Entry<K, V>;

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
                ent
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterEntryMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &mut *ent.as_ptr();
                self.len -= 1;
                self.tail = ent.prev;
                ent
            })
        }
    }
}

impl<K, V> FusedIterator for IterEntryMut<'_, K, V> {}

impl<K, V> ExactSizeIterator for IterEntryMut<'_, K, V> {}

pub(crate) struct IterEntry<'a, K: 'a, V: 'a> {
    head: Option<NonNull<Entry<K, V>>>,
    tail: Option<NonNull<Entry<K, V>>>,
    len: usize,
    marker: PhantomData<&'a Entry<K, V>>,
}

impl<K, V> IterEntry<'_, K, V> {
    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<'a, K, V> Iterator for IterEntry<'a, K, V> {
    type Item = &'a Entry<K, V>;

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
                ent
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterEntry<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &*ent.as_ptr();
                self.len -= 1;
                self.tail = ent.prev;
                ent
            })
        }
    }
}

impl<K, V> FusedIterator for IterEntry<'_, K, V> {}

impl<K, V> ExactSizeIterator for IterEntry<'_, K, V> {}

pub struct ReversedIterMut<'a, K: 'a, V: 'a> {
    head: Option<NonNull<Entry<K, V>>>,
    tail: Option<NonNull<Entry<K, V>>>,
    len: usize,
    marker: PhantomData<&'a Entry<K, V>>,
}

impl<K: Debug, V: Debug> Debug for ReversedIterMut<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("ReversedIterMut")
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

impl<K, V> ReversedIterMut<'_, K, V> {
    fn iter(&self) -> ReversedIterMut<'_, K, V> {
        ReversedIterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }
}

impl<'a, K, V> Iterator for ReversedIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &mut *ent.as_ptr();
                self.len -= 1;
                self.tail = ent.prev;
                (&(*(*ent).key.as_ptr()), &mut (*(*ent).val.as_mut_ptr()))
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for ReversedIterMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|ent| unsafe {
                // Need an unbound lifetime to get 'a
                let ent = &mut *ent.as_ptr();
                self.len -= 1;
                self.head = ent.next;
                (&(*(*ent).key.as_ptr()), &mut (*(*ent).val.as_mut_ptr()))
            })
        }
    }
}

impl<K, V> FusedIterator for ReversedIterMut<'_, K, V> {}

impl<K, V> ExactSizeIterator for ReversedIterMut<'_, K, V> {}
