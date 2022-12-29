use std::{borrow::Borrow, collections::HashMap, hash::Hash};

use id_vec::{Id, IdVec};

pub type StrIdMap<T> = InternMap<String, T>;

/// Map with automatic key interning.
#[derive(Debug, Clone, Eq)]
pub struct InternMap<K, V>
where
    K: Hash,
{
    keys: IdVec<K>,
    values: HashMap<Id<K>, V>,
    key_to_ids: HashMap<K, Id<K>>,
}

impl<K, V> InternMap<K, V>
where
    K: Hash + Eq + Clone,
{
    /// Create an empty `InternMap`.
    #[allow(dead_code)]
    pub fn new() -> Self {
        InternMap {
            keys: IdVec::new(),
            values: HashMap::new(),
            key_to_ids: HashMap::new(),
        }
    }

    /// Insert a kay-value pair into the `InternMap`.
    pub fn insert(&mut self, key: K, value: V) -> (Id<K>, Option<V>) {
        let id = self.get_or_create_key_id(key);
        (id, self.values.insert(id, value))
    }

    /// Return the insertion order.
    pub fn insertion_order(&self, id: Id<K>) -> usize {
        id.index_value()
    }

    fn get_or_create_key_id(&mut self, key: K) -> Id<K> {
        if let Some(&id) = self.key_to_ids.get(&key) {
            return id;
        }

        let id = self.keys.insert(key.clone());
        self.key_to_ids.insert(key, id);
        id
    }

    /// Given a key id, return the matching value, if any.
    pub fn get(&self, id: Id<K>) -> Option<&V> {
        self.values.get(&id)
    }

    /// Given a key, return the matching value, if any.
    pub fn get_key<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.key_to_ids.get(key).map(|id| &self.values[id])
    }

    /// Iterator over the values.
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.values.values()
    }

    /// Iterator over mutable references to the values.
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.values.values_mut()
    }

    /// Return the id associated with the given key.
    pub fn get_id<Q>(&self, key: &Q) -> Option<Id<K>>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.key_to_ids.get(key).copied()
    }

    /// Given an id, return the associated key if it exists.
    pub fn key_for_id(&self, id: Id<K>) -> Option<&K> {
        self.keys.get(id)
    }

    /// Return an iterator of couples of the form (key, value).
    pub fn iter(&self) -> impl Iterator<Item = (Id<K>, &V)> {
        self.values.iter().map(|(id, val)| (*id, val))
    }
}

impl<K, V> Default for InternMap<K, V>
where
    K: Hash + Eq + Clone,
{
    fn default() -> InternMap<K, V> {
        InternMap {
            keys: IdVec::new(),
            values: HashMap::new(),
            key_to_ids: HashMap::new(),
        }
    }
}

impl<K: Eq + PartialEq + Hash, V: PartialEq> PartialEq for InternMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.values.eq(&other.values)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use maplit::*;

    #[test]
    fn empty_map() {
        let map: InternMap<i64, i64> = InternMap::new();
        assert_eq!(hashmap! {}, map.key_to_ids);
        assert_eq!(IdVec::new(), map.keys);
        assert_eq!(hashmap! {}, map.values);
    }

    #[test]
    fn insert_in_empty() {
        let mut map = InternMap::new();
        let (id, val) = map.insert("key", 1);
        assert_eq!(hashmap! { "key" => Id::from_index(0) }, map.key_to_ids);
        assert_eq!(IdVec::from(vec!["key"]), map.keys);
        assert_eq!(hashmap! { Id::from_index(0) => 1 }, map.values);
        assert_eq!(Id::from_index(0), id);
        assert_eq!(None, val);
    }

    #[test]
    fn get() {
        let mut map = InternMap::new();
        let (id1, _) = map.insert("key1", 1);
        let (id2, _) = map.insert("key2", 2);
        assert_eq!(&1, map.get_key(&"key1").unwrap());
        assert_eq!(&2, map.get_key(&"key2").unwrap());
        assert_eq!(&1, map.get(id1).unwrap());
        assert_eq!(&2, map.get(id2).unwrap());
    }

    #[test]
    fn replace() {
        let mut map = InternMap::new();
        let (id1, _) = map.insert("key", 1);
        let (id2, prev_val) = map.insert("key", 2);
        assert_eq!(id1, id2);
        assert_eq!(Some(1), prev_val);
    }

    #[test]
    fn get_key() {
        let mut map = InternMap::new();
        let (id, _) = map.insert("key", 1);
        assert_eq!(Some(id), map.get_id("key"));
    }

    #[test]
    fn entries() {
        let mut map: InternMap<String, usize> = InternMap::new();

        assert_eq!(
            vec![] as Vec<(Id<String>, &usize)>,
            map.iter().collect::<Vec<_>>()
        );

        map.insert("key1".into(), 1);
        map.insert("key2".into(), 2);

        let entries = map.iter().collect::<Vec<_>>();

        assert_eq!(2, entries.len());
        assert!(entries.contains(&(Id::from_index(0), &1usize)));
        assert!(entries.contains(&(Id::from_index(1), &2usize)));
    }

    #[test]
    fn key_from_id_ok() {
        let mut map: InternMap<String, usize> = InternMap::new();
        let (id, _) = map.insert("hello".into(), 1);
        assert_eq!(Some(&"hello".into()), map.key_for_id(id));
    }

    #[test]
    fn key_from_id_missing() {
        let map: InternMap<String, usize> = InternMap::new();
        assert_eq!(None, map.key_for_id(Id::from_index(0)));
    }
}
