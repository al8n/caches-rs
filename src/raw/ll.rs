use alloc::boxed::Box;
use core::borrow::Borrow;
use core::fmt::{Debug, Formatter};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem;
use core::mem::MaybeUninit;
use core::ptr::NonNull;

#[derive(Copy, Clone)]
pub struct KeyRef<T> {
    pub(crate) ptr: *const T,
}

impl<T> KeyRef<T> {
    pub(crate) fn new(ptr: *const T) -> Self {
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
pub(crate) struct Entry<K, V> {
    pub(crate) key: MaybeUninit<K>,
    pub(crate) val: MaybeUninit<V>,
    pub(crate) prev: Option<NonNull<Entry<K, V>>>,
    pub(crate) next: Option<NonNull<Entry<K, V>>>,
}

impl<K: Clone, V: Clone> Clone for Entry<K, V> {
    fn clone(&self) -> Self {
        unsafe {
            Self {
                key: MaybeUninit::new(self.key.as_ptr().read().clone()),
                val: MaybeUninit::new(self.val.as_ptr().read().clone()),
                prev: self.prev.clone(),
                next: self.next.clone(),
            }
        }
    }
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
    pub(crate) fn new(key: K, val: V) -> Self {
        Self {
            key: MaybeUninit::new(key),
            val: MaybeUninit::new(val),
            prev: None,
            next: None,
        }
    }
}

/// `EntryLinkedList` is a double direction linked list.
///
/// For LRU, read and write should be O(1), so we need a
/// double direct linked list.
pub(crate) struct EntryLinkedList<K, V> {
    pub(crate) head: Option<NonNull<Entry<K, V>>>,
    pub(crate) tail: Option<NonNull<Entry<K, V>>>,
    pub(crate) len: usize,
    pub(crate) marker: PhantomData<Box<Entry<K, V>>>,
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
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// `move_to_front` moves `ent` to the front of `EntryLinkedList`.
    /// If `ent` is not an element of the list, the list is not modified.
    /// The element must not be nil.
    pub(crate) fn move_to_front(&mut self, ent: *mut Entry<K, V>) {
        self.detach(ent);
        self.attach(ent);
    }

    pub(crate) fn detach(&mut self, ent: *mut Entry<K, V>) {
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
    pub(crate) fn attach(&mut self, mut ent: *mut Entry<K, V>) {
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

    pub(crate) fn pop_front(&mut self) -> Option<(K, V)> {
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
            (ent.key.assume_init(), ent.val.assume_init())
        })
    }

    pub(crate) fn pop_back(&mut self) -> Option<(K, V)> {
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
            (ent.key.assume_init(), ent.val.assume_init())
        })
    }

    /// Adds the given node to the back of the list.
    #[inline]
    pub(crate) fn push_back(&mut self, mut ent: Box<Entry<K, V>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            ent.next = None;
            ent.prev = self.tail;
            let ent = Some(Box::leak(ent).into());

            match self.tail {
                None => self.head = ent,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = ent,
            }

            self.tail = ent;
            self.len += 1;
        }
    }

    pub(crate) fn back(&self) -> Option<&K> {
        unsafe {
            self.tail
                .as_ref()
                .map(|ent| &(*(*ent.as_ref()).key.as_ptr()) as &K)
        }
    }

    pub(crate) fn back_key_value(&self) -> Option<(&K, &V)> {
        unsafe {
            self.tail.as_ref().map(|ent| {
                let ent_ref = ent.as_ref();
                (
                    &(*(*ent_ref).key.as_ptr()) as &K,
                    &(*(*ent_ref).val.as_ptr()) as &V,
                )
            })
        }
    }

    pub(crate) fn back_key_value_mut(&mut self) -> Option<(&K, &mut V)> {
        unsafe {
            self.tail.as_mut().map(|ent| {
                let ent_ref = ent.as_mut();
                (
                    &(*(*ent_ref).key.as_ptr()),
                    &mut (*(*ent_ref).val.as_mut_ptr()),
                )
            })
        }
    }

    pub(crate) fn clear(&mut self) {
        *self = Self::new();
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub fn append(&mut self, other: &mut Self) {
        match self.tail {
            None => mem::swap(self, other),
            Some(mut tail) => {
                // `as_mut` is okay here because we have exclusive access to the entirety
                // of both lists.
                if let Some(mut other_head) = other.head.take() {
                    unsafe {
                        tail.as_mut().next = Some(other_head);
                        other_head.as_mut().prev = Some(tail);
                    }

                    self.tail = other.tail.take();
                    self.len += mem::replace(&mut other.len, 0);
                }
            }
        }
    }

    /// Splits the list into two at the given index. Returns everything after the given index,
    /// including the index.
    pub fn split_off(&mut self, at: usize) -> EntryLinkedList<K, V> {
        let len = self.len();
        assert!(at <= len, "Cannot split off at a nonexistent index");
        if at == 0 {
            return mem::take(self);
        } else if at == len {
            return Self::new();
        }

        // Below, we iterate towards the `i-1`th node, either from the start or the end,
        // depending on which would be faster.
        let split_node = if at - 1 <= len - 1 - (at - 1) {
            let mut iter = self.iter_mut();
            // instead of skipping using .skip() (which creates a new struct),
            // we skip manually so we can access the head field without
            // depending on implementation details of Skip
            for _ in 0..at - 1 {
                iter.next();
            }
            iter.head
        } else {
            // better off starting from the end
            let mut iter = self.iter_mut();
            for _ in 0..len - 1 - (at - 1) {
                iter.next_back();
            }
            iter.tail
        };
        unsafe { self.split_off_after_node(split_node, at) }
    }

    #[inline]
    unsafe fn split_off_after_node(
        &mut self,
        split_node: Option<NonNull<Entry<K, V>>>,
        at: usize,
    ) -> Self {
        // The split node is the new tail node of the first part and owns
        // the head of the second part.
        if let Some(mut split_node) = split_node {
            let second_part_head;
            let second_part_tail;
            second_part_head = split_node.as_mut().next.take();
            if let Some(mut head) = second_part_head {
                head.as_mut().prev = None;
                second_part_tail = self.tail;
            } else {
                second_part_tail = None;
            }

            let second_part = EntryLinkedList {
                head: second_part_head,
                tail: second_part_tail,
                len: self.len - at,
                marker: PhantomData,
            };

            // Fix the tail ptr of the first part
            self.tail = Some(split_node);
            self.len = at;

            second_part
        } else {
            mem::replace(self, EntryLinkedList::new())
        }
    }
}

impl<K: Clone, V: Clone> Clone for EntryLinkedList<K, V> {
    fn clone(&self) -> Self {
        self.iter_entry().cloned().collect()
    }

    fn clone_from(&mut self, other: &Self) {
        let mut iter_other = other.iter_entry();
        if self.len() > other.len() {
            self.split_off(other.len());
        }
        for (elem, elem_other) in self.iter_entry_mut().zip(&mut iter_other) {
            elem.clone_from(elem_other);
        }
        if !iter_other.is_empty() {
            self.extend(iter_other.cloned());
        }
    }
}

impl<K, V> Extend<Entry<K, V>> for EntryLinkedList<K, V> {
    fn extend<I: IntoIterator<Item = Entry<K, V>>>(&mut self, iter: I) {
        <Self as SpecExtend<I>>::spec_extend(self, iter);
    }

    // #[inline]
    // fn extend_one(&mut self, elem: Entry<K, V>) {
    //     self.push_back(Box::new(elem));
    // }
}

impl<K, V, I: IntoIterator<Item = Entry<K, V>>> SpecExtend<I> for EntryLinkedList<K, V> {
    fn spec_extend(&mut self, iter: I) {
        iter.into_iter()
            .for_each(move |elt| self.push_back(Box::new(elt)));
    }
}

/// An intermediate trait for specialization of `Extend`.
#[doc(hidden)]
trait SpecExtend<I: IntoIterator> {
    /// Extends `self` with the contents of the given iterator.
    fn spec_extend(&mut self, iter: I);
}

impl<K, V> SpecExtend<EntryLinkedList<K, V>> for EntryLinkedList<K, V> {
    fn spec_extend(&mut self, ref mut other: EntryLinkedList<K, V>) {
        self.append(other);
    }
}
