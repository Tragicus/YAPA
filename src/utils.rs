use std::vec::Vec;
use std::hash::Hash;
use std::hash::BuildHasher;
use std::hash::RandomState;
use std::collections::HashMap;
use std::collections::BTreeMap;
use std::cmp::Ordering;

pub type VarType = usize;

pub fn iota(n: usize) -> Vec<usize> {
    (0..n).collect()
}

/*pub trait MergeOption {
    type T;

    fn merge<F : FnOnce(T, T) -> T>(self, other: Self, f: F) -> Self;
}

impl<T> MergeOption for Option<T> {
    type T = T

    pub fn merge<F : FnOnce(T, T) -> T>(self, other: Self, f: F) {
        match (self, other) {
            (None, None) => None,
            (x, None) | (None, x) => x,
            (Some(x), Some(y)) => Some(f(x, y))
        }
    }
}

pub trait MergeMap {
    type K;
    type V;

    pub fn merge<V0, V1, F : Fn(K, Option<V>, Option<V0>) -> Option<V1>>(self, f: F, other: BTreeMap<K, V0>) -> BTreeMap<K, V1> {
    
}

impl<K, V> BTreeMap<K, V> {*/
pub fn merge_map<K : std::cmp::Ord + std::clone::Clone, V, V0, V1, F : Fn(K, Option<V>, Option<V0>) -> Option<V1>>(orig: BTreeMap<K, V>, f: F, other: BTreeMap<K, V0>) -> BTreeMap<K, V1> {
    let mut m1 = orig.into_iter().peekable();
    let mut m2 = other.into_iter().peekable();
    let mut r = BTreeMap::<K, V1>::new();

    loop {
        match (m1.peek(), m2.peek()) {
            (None, None) => return r,
            (Some(_), None) => {
                let (k, v) = m1.next().unwrap();
                f(k.clone(), Some(v), None).map(|v| r.insert(k, v));
            }
            (None, Some(_)) => {
                let (k, v) = m2.next().unwrap();
                f(k.clone(), None, Some(v)).map(|v| r.insert(k, v));
            }
            (Some((k1, _)), Some((k2, _))) => {
                match k1.cmp(k2) {
                    Ordering::Less => {
                        let (k1, v1) = m1.next().unwrap();
                        f(k1.clone(), Some(v1), None).map(|v| r.insert(k1, v));
                    }
                    Ordering::Equal => {
                        let (k1, v1) = m1.next().unwrap();
                        let (_, v2) = m2.next().unwrap();
                        f(k1.clone(), Some(v1), Some(v2)).map(|v| r.insert(k1, v));
                    }
                    Ordering::Greater => {
                        let (k2, v2) = m2.next().unwrap();
                        f(k2.clone(), None, Some(v2)).map(|v| r.insert(k2, v));
                    }
                }
            }
        }
    }
}
//}

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
