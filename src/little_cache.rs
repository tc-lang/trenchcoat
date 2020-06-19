/// A little cache for storing a little number of little things
pub struct Cache<K: PartialEq + Ord + Clone, V: Clone> {
    expected_size: usize,
    //entries: RefCell<Vec<(K, V)>>,
    entries: Vec<(K, V)>,
}

impl<K: PartialEq + Ord + Clone, V: Clone> Cache<K, V> {
    pub fn new(expected_size: usize) -> Cache<K, V> {
        Cache {
            expected_size,
            entries: Vec::new(),
        }
    }

    pub fn get(&self, key: &K) -> Option<V> {
        return match self.entries.binary_search_by_key(&key, |(k, _)| k) {
            Ok(idx) => Some(self.entries[idx].1.clone()),
            Err(_) => None,
        };
    }

    pub fn set(&mut self, key: K, value: V) {
        if self.entries.len() > 0 {
            match self.entries.binary_search_by_key(&&key, |(k, _)| k) {
                Ok(idx) => {
                    self.entries[idx] = (key, value);
                }
                Err(idx) => {
                    self.entries.insert(idx, (key, value));
                }
            }
        } else {
            self.entries = Vec::with_capacity(self.expected_size);
            self.entries.push((key, value));
        }
    }

    pub fn get_or_else(&mut self, key: &K, or_else: impl Fn() -> V) -> V {
        match self.get(key) {
            Some(v) => return v,
            None => (),
        }
        let v = or_else();
        self.set(key.clone(), v.clone());
        v
    }
}

#[cfg(test)]
mod tests {
    use super::Cache;

    #[test]
    fn little_cache_test() {
        let mut cache = Cache::new(2);
        assert!(cache.get(&"foo").is_none());
        assert!(cache.get(&"bar").is_none());
        assert!(cache.get(&"baz").is_none());
        cache.set(&"foo", 5);
        assert!(cache.get(&"foo").unwrap() == 5);
        assert!(cache.get(&"baz").is_none());
        assert!(cache.get(&"baz").is_none());
        cache.set(&"bar", 7);
        assert!(cache.get(&"foo").unwrap() == 5);
        assert!(cache.get(&"bar").unwrap() == 7);
        assert!(cache.get(&"baz").is_none());
        cache.set(&"bar", 8);
        assert!(cache.get(&"foo").unwrap() == 5);
        assert!(cache.get(&"bar").unwrap() == 8);
        assert!(cache.get(&"baz").is_none());
        assert!(cache.get_or_else(&"bar", || unreachable!()) == 8);
        assert!(cache.get_or_else(&"baz", || 1) == 1);
        assert!(cache.get_or_else(&"baz", || unreachable!()) == 1);
        assert!(cache.get(&"baz").unwrap() == 1);
        assert!(cache.get(&"bar").unwrap() == 8);
        assert!(cache.get(&"foo").unwrap() == 5);
        cache.set(&"foo", 11);
        cache.set(&"bar", 10);
        assert!(cache.get(&"foo").unwrap() == 11);
        assert!(cache.get(&"bar").unwrap() == 10);
        assert!(cache.get(&"baz").unwrap() == 1);
    }
}
