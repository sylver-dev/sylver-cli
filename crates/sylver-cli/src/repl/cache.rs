use std::collections::{HashSet, VecDeque};

static DEFAULT_MAX_GENS: usize = 10;

#[derive(Debug, Clone)]
pub struct GenCache<T> {
    values: Vec<Option<T>>,
    max_gens: usize,
    gen_indices: VecDeque<HashSet<usize>>,
    free_indices: VecDeque<usize>,
}

impl<T> GenCache<T> {
    /// Create a new `GenCache`.
    pub fn new(max_gens: usize) -> GenCache<T> {
        let mut cache = GenCache {
            max_gens,
            values: Vec::new(),
            gen_indices: VecDeque::new(),
            free_indices: VecDeque::new(),
        };

        cache.start_generation();

        cache
    }

    /// Return the value with the given index.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.values.get(index).and_then(|x| x.as_ref())
    }

    /// Push a new value into the current generation.
    /// # Panics
    /// If no generation has been started.
    pub fn push(&mut self, value: T) -> usize {
        let id = match self.reserve_index() {
            Some(id) => {
                self.values[id] = Some(value);
                id
            }
            None => {
                let id = self.values.len();
                self.values.push(Some(value));
                id
            }
        };

        let current_gen_index = self.gen_indices.len();
        self.gen_indices[current_gen_index - 1].insert(id);

        id
    }

    fn reserve_index(&mut self) -> Option<usize> {
        self.free_indices.pop_front()
    }

    /// Start a new generation.
    /// If the maximum number of generations has been reached, remove the values
    /// from the oldest generation.
    pub fn start_generation(&mut self) {
        if self.gen_indices.len() >= self.max_gens {
            self.remove_oldest_gen()
        }

        self.gen_indices.push_back(HashSet::new());
    }

    fn remove_oldest_gen(&mut self) {
        if let Some(indices) = self.gen_indices.pop_front() {
            for i in indices {
                self.values[i] = None;
                self.free_indices.push_back(i);
            }
        }
    }
}

impl<T> Default for GenCache<T> {
    fn default() -> Self {
        GenCache::new(DEFAULT_MAX_GENS)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_first_value() {
        let mut cache = GenCache::default();
        let value_id = cache.push(42);
        assert_eq!(Some(&42), cache.get(value_id));
    }

    #[test]
    fn remove_oldest_gen_when_full() {
        let mut cache = GenCache::new(2);

        let value_gen1_id = cache.push(1);

        cache.start_generation();
        let _value_gen2_id = cache.push(2);

        // Will remove the gen 1
        cache.start_generation();
        assert_eq!(None, cache.get(value_gen1_id));

        // The first id is available, so it is recycled.
        let value_gen3_id = cache.push(3);

        assert_eq!(value_gen1_id, value_gen3_id);
        assert_eq!(Some(&3), cache.get(value_gen3_id));
    }

    #[test]
    fn non_contiguous_gen() {
        let mut cache = GenCache::new(2);

        let value_gen1_id = cache.push(1);

        cache.start_generation();
        let _value_gen2_id = cache.push(2);

        // Will remove the gen 1
        cache.start_generation();
        // The first id is available, so it is recycled.
        let value1_gen3_id = cache.push(31);
        let value2_gen3_id = cache.push(32);

        assert_eq!(value_gen1_id, value1_gen3_id);
        assert_eq!(2, value2_gen3_id);
    }
}
