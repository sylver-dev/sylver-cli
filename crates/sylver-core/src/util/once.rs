use std::{
    collections::{HashSet, VecDeque},
    hash::Hash,
    ops::Index,
};

use derive_more::From;
use rustc_hash::FxHashSet;
use smallvec::SmallVec;

/// Queue in which elements can be inserted at most once.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct OnceQueue<T: Hash + Clone + Eq> {
    seen: FxHashSet<T>,
    queue: VecDeque<T>,
}

impl<T: Hash + Clone + Eq> OnceQueue<T> {
    /// Create a new `OnceSet`.
    pub fn new() -> Self {
        OnceQueue {
            seen: HashSet::default(),
            queue: VecDeque::new(),
        }
    }

    /// Push `elem` at the back of the queue if it was never inserted before. Return whether or not the element was inserted.
    pub fn push(&mut self, elem: T) -> bool {
        if self.seen.contains(&elem) {
            return false;
        }

        self.seen.insert(elem.clone());
        self.queue.push_back(elem);

        true
    }

    /// Pop an element from the queue.
    pub fn pop(&mut self) -> Option<T> {
        self.queue.pop_front()
    }
}

impl<T: Hash + Clone + Eq> Default for OnceQueue<T> {
    fn default() -> Self {
        OnceQueue::new()
    }
}

impl<T: Hash + Clone + Eq> Extend<T> for OnceQueue<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for elem in iter {
            self.push(elem);
        }
    }
}

impl<T: Hash + Clone + Eq> FromIterator<T> for OnceQueue<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut queue = OnceQueue::new();
        queue.extend(iter);
        queue
    }
}

impl<T: Hash + Clone + Eq, C: IntoIterator<Item = T>> From<C> for OnceQueue<T> {
    fn from(elems: C) -> Self {
        let mut queue = OnceQueue::new();
        queue.extend(elems.into_iter());
        queue
    }
}

/// Small vec containing unique values.
#[derive(Debug, Clone, Eq, Hash, From)]
pub struct UniqueSmallVec<T: Eq, const N: usize = 3> {
    values: SmallVec<[T; N]>,
}

impl<T: Eq, const N: usize> UniqueSmallVec<T, N> {
    /// Create a new, empty `UniqueSmallVec`.
    pub fn new() -> Self {
        UniqueSmallVec {
            values: SmallVec::new(),
        }
    }

    /// If `value` is not already in the current vec, push it at the end.
    /// No-op otherwise.
    pub fn push(&mut self, value: T) {
        if !self.values.contains(&value) {
            self.values.push(value)
        }
    }

    /// Retrieve the value at the given index, if it exists.
    pub fn get(&self, n: usize) -> Option<&T> {
        self.values.get(n)
    }
}

impl<T: Eq, const N: usize, const M: usize> PartialEq<UniqueSmallVec<T, M>>
    for UniqueSmallVec<T, N>
{
    fn eq(&self, other: &UniqueSmallVec<T, M>) -> bool {
        self.values.eq(&other.values)
    }
}

impl<T: Eq, const N: usize> Index<usize> for UniqueSmallVec<T, N> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.values[index]
    }
}

impl<T: Eq, const N: usize> From<[T; N]> for UniqueSmallVec<T, N> {
    fn from(values: [T; N]) -> Self {
        UniqueSmallVec {
            values: SmallVec::from(values),
        }
    }
}

impl<T: Eq, const N: usize> std::ops::Deref for UniqueSmallVec<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.values.deref()
    }
}

impl<T: Eq, const N: usize> Default for UniqueSmallVec<T, N> {
    fn default() -> Self {
        UniqueSmallVec {
            values: Default::default(),
        }
    }
}

impl<T: Eq, const N: usize> IntoIterator for UniqueSmallVec<T, N> {
    type Item = T;
    type IntoIter = smallvec::IntoIter<[T; N]>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.into_iter()
    }
}

impl<'a, T: Eq, const N: usize> IntoIterator for &'a UniqueSmallVec<T, N> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.iter()
    }
}

#[cfg(test)]
mod test {
    use std::iter::FromIterator;

    use super::*;

    #[test]
    fn first_insert_inserts() {
        let mut queue = OnceQueue::new();
        assert!(queue.push(1));
        assert_eq!(VecDeque::from_iter([1].into_iter()), queue.queue);
        assert_eq!(HashSet::from_iter([1].into_iter()), queue.seen);
    }

    #[test]
    fn second_insert_same_value() {
        let mut queue = OnceQueue::new();
        queue.push(1);
        assert!(!queue.push(1));
        assert_eq!(VecDeque::from_iter([1].into_iter()), queue.queue);
        assert_eq!(HashSet::from_iter([1].into_iter()), queue.seen);
    }

    #[test]
    fn second_insert_different_value() {
        let mut queue = OnceQueue::new();
        queue.push(1);
        assert!(queue.push(2));
        assert_eq!(VecDeque::from_iter([1, 2].into_iter()), queue.queue);
        assert_eq!(HashSet::from_iter([1, 2].into_iter()), queue.seen);
    }

    #[test]
    fn pop() {
        let mut queue = OnceQueue::new();
        queue.push(1);
        queue.push(2);
        assert_eq!(Some(1), queue.pop());
        assert_eq!(Some(2), queue.pop());
        assert_eq!(None, queue.pop())
    }

    #[test]
    fn once_queue_from_iter() {
        let mut queue = OnceQueue::from_iter([1, 2, 3].into_iter());
        assert_eq!(Some(1), queue.pop());
        assert_eq!(Some(2), queue.pop());
        assert_eq!(Some(3), queue.pop());
        assert_eq!(None, queue.pop());
    }

    #[test]
    fn new_empty_unique_small_vec() {
        let v: UniqueSmallVec<usize, 3> = UniqueSmallVec::new();

        assert_eq!(
            v,
            UniqueSmallVec::<usize, 3> {
                values: SmallVec::new()
            }
        )
    }

    #[test]
    fn new_unique_small_vec() {
        let v = UniqueSmallVec::from([1, 2, 3]);
        assert_eq!(
            v,
            UniqueSmallVec {
                values: SmallVec::from([1, 2, 3])
            }
        );
    }

    #[test]
    fn unique_small_vec_push_unseen() {
        let mut v = UniqueSmallVec::from([1, 3, 4]);
        v.push(5);
        assert_eq!(v, UniqueSmallVec::from([1, 3, 4, 5]))
    }

    #[test]
    fn unique_small_vec_push_seen() {
        let mut v = UniqueSmallVec::from([1, 2, 3]);
        v.push(1);
        assert_eq!(v, UniqueSmallVec::from([1, 2, 3]));
    }

    #[test]
    fn unique_small_vec_get() {
        let v = UniqueSmallVec::from([1, 2, 3]);
        assert_eq!(v.get(0), Some(&1));
        assert_eq!(v.get(3), None);
    }

    #[test]
    fn unique_small_vec_index_ok() {
        let v = UniqueSmallVec::from([1, 2, 3]);
        assert_eq!(v[2], 3);
    }

    #[test]
    #[should_panic]
    fn unique_small_vec_index_notok() {
        let v = UniqueSmallVec::from([1, 2, 3]);
        v[3];
    }
}
