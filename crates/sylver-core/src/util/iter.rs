use std::{collections::HashMap, hash::Hash};

pub fn first_and_last<T: Clone>(i: impl IntoIterator<Item = T>) -> Option<(T, T)> {
    let mut items = i.into_iter();

    items
        .next()
        .map(|first| (first.clone(), items.last().unwrap_or(first)))
}

pub fn group_by<K: Hash + Eq, V>(
    i: impl IntoIterator<Item = V>,
    key: impl Fn(&V) -> K,
) -> HashMap<K, Vec<V>> {
    let mut groups: HashMap<K, Vec<V>> = HashMap::new();

    for v in i {
        groups.entry(key(&v)).or_default().push(v);
    }

    groups
}
