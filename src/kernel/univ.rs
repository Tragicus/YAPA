use std::collections::BTreeMap;
use std::collections::HashSet;
use std::cmp::max;
use crate::utils::*;
use crate::kernel::error::Error;

/* A universe is given by a sort among SProp, Prop and Type and a level in NN.
 * Cumulativity allows to type any term of type S_i with type S_j for any sort S and any j > i.
 * Elimination is allowed when the return type's sort is lower than the subject's type's sort,
 * according to the relation SProp <= Prop <= Type. */

/* Atomic (or explicit) universes. */


/* A sort is either explicitly SProp, Prop or Type, or a sort variable. */
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    SProp(),
    Prop(),
    Type(),
    Var(VarType)
}

/* A level is the maximum of a family of shifted level variables.
 * Variable `0` stands for the bottom of the hierarchy. */
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
    pub fn succ(self) -> Self {
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

impl std::fmt::Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::Type() => write!(f, "Type"),
            Sort::SProp() => write!(f, "SProp"),
            Sort::Prop() => write!(f, "Prop"),
            Sort::Var(s) => write!(f, "s_{}", s),
        }
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

/* Universes context, containing
 * - a context of sorts as a function which associates to each sort variable its lower and upper
 *   bounds and the set of sort variables that are larger than it, according to the order
 *   SProp < Prop < Type,
 * - a context of levels as a function which associates to each level variable v the set of
 *   pairs (n, l) such that v + n <= l.
 *   In particular, with v the 0 level variable, we have v <= w for every level variable w.
 * - a model for the previous set of constraints. */
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    sorts: BTreeMap<VarType, (Sort, Sort, HashSet<VarType>)>,
    levels: BTreeMap<VarType, Vec<(usize, Level)>>,
    model: BTreeMap<VarType, usize>,
}

impl Context {
    /* Empty context.
     * We initialize the 0 level variable, which is always defined. */
    pub fn new() -> Context {
        Context {
            sorts: BTreeMap::new(),
            levels: BTreeMap::from([(0, vec![])]),
            model: BTreeMap::from([(0, 0)])
        }
    }

    pub fn new_sort(&mut self) -> VarType {
        let s = self.sorts.last_key_value().map_or(0, |(s, _)| s + 1);
        self.sorts.insert(s.clone(), (Sort::SProp(), Sort::Type(), HashSet::new()));
        s
    }

    pub fn new_level(&mut self) -> VarType {
        let u = self.sorts.last_key_value().map_or(0, |(u, _)| u + 1);
        self.levels.insert(u.clone(), vec![]);
        self.model.insert(u.clone(), 0);
        let cstrs0 = self.levels.get_mut(&0).unwrap();
        cstrs0.push((0, Level { vars: BTreeMap::from([(u.clone(), 0)]) }));
        u
    }

    pub fn new_univ(&mut self) -> Univ {
        let s = self.new_sort();
        let u = self.new_level();
        Univ { sort: Sort::Var(s), level: Level { vars: BTreeMap::from([(u, 0)]) } }
    }

    /* Adding a constraint [s1 <= s2] to the context of sorts. */
    pub fn add_sort_constraint(&mut self, s1: Sort, s2: Sort) -> Result<&mut Self, Error> {
        match s1 {
            Sort::Var(s1) => {
                let (_, u, v) = self.sorts.get_mut(&s1).ok_or(Error::UnboundSort(s1))?;
                match s2 {
                    Sort::Var(s2) => { v.insert(s2); },
                    s2 => *u = s2.max(u.clone()),
                }
            }
            s1 => match s2 {
                Sort::Var(s2) => {
                    let (l, _, _) = self.sorts.get_mut(&s2).ok_or(Error::UnboundSort(s2))?;
                    *l = s1.max(l.clone())
                }
                s2 => { if s2 < s1 { Err(Error::SortInconsistency(s2, s1))? }; }
            }
        }
        Ok(self)
    }

    /* Adding a constraint [u1 <= u2] to the context of universes. */
    pub fn add_univ_constraint(&mut self, u1: Univ, u2: Univ) -> Result<&mut Self, Error> {
        // Let's destruct u1 and u2.
        let Univ { sort: s1, level: u1 } = u1;
        let Univ { sort: s2, level: u2 } = u2;
        // We assert that s1 = s2.
        self.add_sort_constraint(s1.clone(), s2.clone())?;
        self.add_sort_constraint(s2.clone(), s1.clone())?;
        /* For every level variable u in the domain of u1, we add the constraint u + u1(u) <= u2.
         * We only add a constraint if it is not obviously redundant, and we remove constraints
         * that become obviously redundant.
         * We compute the set [updt] of level variables for which we add a constraint. */ 
        let mut updt = HashSet::new();
        u1.clone().vars.into_iter().map(|(u, n)| {
            let cstrs = self.levels.get_mut(&u).ok_or(Error::UnboundUniv(u))?;
            let mut ditch = false;
            *cstrs = cstrs.iter().filter(|(m, v)| {
                if ditch { true } else {
                    // If v + n <= u2 + m, u2 - n is redundant.
                    if v.vars.iter().all(|(i, k)| u2.vars.get(i).map_or(false, |j| k + n <= j + m)) {
                        ditch = true;
                        true
                    } else {
                        // If u2 + m <= v + n, v - m becomes redundant.
                        !u2.vars.iter().all(|(i, k)| v.vars.get(i).map_or(false, |j| k + m <= j + n))
                    }
                }
            }).map(|x| x.clone()).collect();
            if !ditch {
                updt.insert(u);
                cstrs.push((n, u2.clone()));
            };
            Ok(())
        }).collect::<Result<(), _>>()?;
        self.saturate_model(/*updt*/).map_err(|_| Error::UnivInconsistency(Univ { sort: s1, level: u1 }, Univ { sort: s2, level: u2 }))
    }

    /* Auxiliary function for saturate_model, where we only consider constraints that have their
     * conclusion in the given domain. */
    fn saturate_onto(&mut self, dom: &HashSet<VarType>) -> Result<&mut Self, HashSet<VarType>> {
        loop {
            self.saturate_over(dom)?;

            let mut done = true;

            for (u, cstrs) in self.levels.iter().filter(|(u, _)| dom.contains(&u)) {
                for (n, v) in  cstrs.iter() {
                    let _ = v.vars.iter().map(|(m, v)| {
                        let kv = self.model.get(&v).unwrap();
                        if *kv < *m { Err(()) } else { Ok(kv - m) }
                    }).collect::<Result<Vec<_>, _>>().map(|it| {
                        let k = it.into_iter().min().unwrap();
                        let ku = self.model.get(&u).unwrap();
                        if *ku < k + n {
                            self.model.insert(u.clone(), k + n);
                            done = false;
                        }
                    });
                }
            }

            if done { break; }
        }

        Ok(self)
    }


    /* Auxiliary function for saturate_model, where we only consider constraints that are over the
     * elements of the given domain. */
    fn saturate_over(&mut self, dom: &HashSet<VarType>) -> Result<&mut Self, HashSet<VarType>> {
        let mut updt = HashSet::new();
        let mut n = 0;

        loop {
            for (u, cstrs) in self.levels.iter().filter(|(u, _)| dom.contains(&u)) {
                for (n, v) in  cstrs.iter() {
                    let _ = v.vars.iter().map(|(m, v)| {
                        if !dom.contains(&v) { return Err(()) };
                        let kv = self.model.get(&v).unwrap();
                        if *kv < *m { Err(()) } else { Ok(kv - m) }
                    }).collect::<Result<Vec<_>, _>>().map(|it| {
                        let k = it.into_iter().min().unwrap();
                        let ku = self.model.get(&u).unwrap();
                        if *ku < k + n {
                            self.model.insert(u.clone(), k + n);
                            updt.insert(u.clone());
                        }
                    });
                }
            }

            if updt.len() == dom.len() { return Err(updt); } else {
                if updt.len() == n { break; } else {
                    n = updt.len();
                    self.saturate_onto(&updt)?;
                }
            }
        }
        Ok(self)
    }

    /* Computes the smallest interpretation larger than self's current interpretation, which is a
     * model of self's constraints. */
    // TODO: Check if only considering the updated constraints in the first pass is useful.
    fn saturate_model(&mut self/*, updt: HashSet<VarType>*/) -> Result<&mut Self, HashSet<VarType>> {

        let dom = self.model.iter().map(|(u, _)| u.clone()).collect();
        self.saturate_over(&dom)
    }
}
