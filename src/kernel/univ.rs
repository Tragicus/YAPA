use std::collections::BTreeMap;
use std::cmp;
use crate::utils::*;

/* A universe is given by a sort among SProp, Prop and Type and a level in NN.
 * Cumulativity allows to type any term of type S_i with type S_j for any sort S and any j > i.
 * Elimination is allowed when the return type's sort is lower than the subject's type's sort,
 * according to the relation SProp <= Prop <= Type. */

/* Atomic (or explicit) universes. */


/* A sort is either explicitly SProp, Prop or Type, or a sort variable. */
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Sort {
    SProp(),
    Prop(),
    Type(),
    Var(VarType)
}

/* A level is the maximum of a family of shifted level variables. */
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Level {
    vars: BTreeMap<VarType, usize>
}

/* A universe is given by a sort and a level. */
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Univ {
    sort: Sort,
    level: Level
}

impl Level {
    /* shift a level by a natural number. */
    pub fn add(mut self, i: usize) -> Self {
        self.vars = self.vars.into_iter().map(|(v, u)| (v, u + i)).collect();
        self
    }

    /* Successor of a level */
    pub fn succ(mut self) -> Self {
        self.add(1)
    }

    /* max of two levels */
    pub fn max(mut self, other: Self) -> Self {
        self.vars = merge_map(self.vars, |_, u, u0| std::cmp::max(u, u0), other.vars);
        self
    }
}

impl Univ {
    /* shift a universe by a natural number. */
    pub fn add(mut self, i: usize) -> Self {
        if i == 0 { return self; };
        self.sort = Sort::Type();
        self.level = self.level.add(i);
        self
    }

    /* Successor of a universes. This gives the type of an instance of Type. We copy-paste the code to avoid the test. */
    pub fn succ(mut self) -> Self {
        self.sort = Sort::Type();
        self.level = self.level.succ();
        self
    }

    /* max of two universes. This gives the type of a product type. */
    pub fn max(mut self, other: Self) -> Self {
        self.sort = other.sort;
        self.level = self.level.max(other.level);
        self
    }

    pub fn sprop() -> Self {
        Univ { sort: Sort::SProp(), level: Level { vars: BTreeMap::from([(0, 0)]) } }
    }

    pub fn prop() -> Self {
        Univ { sort: Sort::Prop(), level: Level { vars: BTreeMap::from([(0, 0)]) } }
    }

    pub fn set() -> Self {
        Univ { sort: Sort::Type(), level: Level { vars: BTreeMap::from([(0, 0)]) } }
    }

}

impl std::fmt::Display for Level {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let fmt_atom = |f: &mut std::fmt::Formatter<'_>, v: (&VarType, &usize)| {
            let (v, n) = v;
            if *v == 0 { write!(f, "{}", n) } else {
                if *n == 0 { write!(f, "u_{}", v) } else {
                    write!(f, "u_{} + {}", v, n)
                }
            }
        };
        if self.vars.len() == 1 {
            fmt_atom(f, self.vars.iter().next().unwrap())
        } else {
            write!(f, "max(")?;
            let mut it = self.vars.iter();
            /* Might explode if the level is ill-formed. */
            fmt_atom(f, it.next().unwrap())?;
            for x in it {
                write!(f, ", ")?;
                fmt_atom(f, x)?;
            };
            write!(f, ")")
        }
    }
}

impl std::fmt::Display for Univ {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.sort {
            Sort::Type() => write!(f, "Type@{{{}}}", self.level),
            Sort::Prop() => write!(f, "Prop"),
            Sort::SProp() => write!(f, "SProp"),
            Sort::Var(v) => write!(f, "s_{}@{{{}}}", v, self.level)
        }
    }
}

/*pub struct Context {
    sorts 
}*/
