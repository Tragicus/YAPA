use std::vec::Vec;
use std::hash::Hash;
use std::hash::BuildHasher;
use std::hash::RandomState;
use std::collections::HashMap;

pub fn iota(n: usize) -> Vec<usize> {
    let mut v = vec![0; n];
    if n != 0 {
        for i in 0..(n-1) {
            v[i] = i;
        };
    };
    v
}

// HashMap supporting shadowing
#[derive(Debug, Clone)]
pub struct ShadowHashMap<K, V, S = RandomState> {
    map: HashMap<K, Vec<V>, S>
}

impl<K, V> ShadowHashMap<K, V, RandomState> {
    pub fn new() -> Self {
        Self { map: { HashMap::new() } }
    }
}
impl<K: Hash + Eq, V, S: BuildHasher> ShadowHashMap<K, V, S> {
    pub fn get(&self, k: &K) -> Option<&V> {
        self.map.get(k).map(|r| &r[r.len()-1])
    }
}

impl<K: Hash + Eq + Clone, V, S: BuildHasher> ShadowHashMap<K, V, S> {
    pub fn insert(&mut self, k: K, v: V) -> () {
        match self.map.get_mut(&k) {
            None => { self.map.insert(k.clone(), vec![v]); },
            Some(vs) => vs.push(v)
        }
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> ShadowHashMap<K, V, S> {
    pub fn remove(&mut self, k: &K) -> Option<V> {
        let mut b = false;
        let v = self.map.get_mut(&k).map(|vs| {
            b = vs.len() == 1;
            vs.pop().unwrap()
        });
        if b { self.map.remove(&k); };
        v
    }
}
