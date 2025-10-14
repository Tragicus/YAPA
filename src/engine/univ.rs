use std::cmp;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Univ { val: usize }

impl Univ {
    pub fn succ(&self) -> Self {
        Univ { val: self.val + 1 }
    }

    pub fn max(&self, v: &Self) -> Self {
        Univ { val: cmp::max(self.val.clone(), v.val.clone()) }
    }

    pub fn exact(i: usize) -> Self {
        Univ { val: i }
    }
}

impl std::fmt::Display for Univ {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

