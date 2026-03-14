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
 * Variable `0` stands for the bottom of the hierarchy.
 * We allow shifting down to make the theory well-behaved. */
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Level {
    pub vars: BTreeMap<VarType, isize>
}

/* A universe is given by a sort and a level. */
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Univ {
    pub sort: Sort,
    pub level: Level
}

impl Level {
    /* shift a level by an integer. */
    pub fn add(mut self, i: isize) -> Self {
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

    /* Weak comparison, where u <= v iff u <= v pointwise.
     * This may return Less or Greater even when assignations do not enforce said inequality. */
    pub fn wcmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let mut cmp = None;
        let mut assign = |x| {
            if cmp == None {
                cmp = Some(x);
            } else if cmp != Some(x) {
                return Err(());
            }
            Ok(())
        };
        let mut it = self.vars.iter().peekable();
        let mut it2 = other.vars.iter().peekable();
        loop {
            match (it.peek(), it2.peek()) {
                (None, None) => { return Some(cmp.unwrap_or(std::cmp::Ordering::Equal)); },
                (None, _) => { return Some(cmp.unwrap_or(std::cmp::Ordering::Less)); },
                (_, None) => { return Some(cmp.unwrap_or(std::cmp::Ordering::Greater)); },
                (Some((u, n)), Some((v, m))) => {
                    match u.cmp(v) {
                        std::cmp::Ordering::Less => {
                            assign(std::cmp::Ordering::Greater).ok()?;
                            it.next();
                        }
                        std::cmp::Ordering::Greater => {
                            assign(std::cmp::Ordering::Less).ok()?;
                            it2.next();
                        }
                        std::cmp::Ordering::Equal => {
                            match n.cmp(m) {
                                std::cmp::Ordering::Less => { assign(std::cmp::Ordering::Less).ok()?; }
                                std::cmp::Ordering::Greater => { assign(std::cmp::Ordering::Greater).ok()?; }
                                std::cmp::Ordering::Equal => { () }
                            }
                            it.next();
                            it2.next();
                        }
                    }
                }
            }
        }
    }
}

impl Univ {
    /* shift a universe by a natural number. */
    pub fn add(mut self, i: isize) -> Self {
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
        let fmt_atom = |f: &mut std::fmt::Formatter<'_>, v: (&VarType, &isize)| {
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
 *   bounds and the set of sort variables that are smaller/larger than it, according to the order
 *   SProp < Prop < Type,
 * - a context of levels as a function which associates to each level variable v the set of its
 *   upper bounds.
 *   In particular, with v the 0 level variable, we have v <= w for every level variable w.
 * - a model for the previous set of constraints. */
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    pub sorts: Vec<(Sort, Sort, HashSet<VarType>, HashSet<VarType>)>,
    pub levels: Vec<Vec<Level>>,
    pub model: Vec<usize>,
}

impl Context {
    /* Empty context.
     * We initialize the 0 level variable, which is always defined. */
    pub fn new() -> Context {
        Context {
            sorts: vec![],
            levels: vec![vec![]],
            model: vec![0]
        }
    }

    pub fn new_sort(&mut self) -> VarType {
        let s = self.sorts.len();
        self.sorts.push((Sort::SProp(), Sort::Type(), HashSet::new(), HashSet::new()));
        s
    }

    pub fn new_level(&mut self) -> VarType {
        let u = self.model.len();
        self.levels.push(vec![]);
        self.model.push(0);
        self.levels.get_mut(0).unwrap().push(Level { vars: BTreeMap::from([(u.clone(), 0)]) });
        u
    }

    pub fn new_univ(&mut self) -> Univ {
        let s = self.new_sort();
        let u = self.new_level();
        Univ { sort: Sort::Var(s), level: Level { vars: BTreeMap::from([(u, 0)]) } }
    }

    /* Adding a constraint [s1 <= s2] to the context of sorts. */
    pub fn add_sort_constraint(&mut self, s1: Sort, s2: Sort) -> Result<&mut Self, Error> {
        // Propagates the constaint l <= s in the graph of sort variables constraints
        fn propagate_up(univ: &mut Context, s: &VarType, l: &Sort) -> Result<(), Error> {
            let (ls, _, _, ub) = univ.sorts.get_mut(*s).ok_or(Error::UnboundSort(s.clone()))?;
            if *ls < *l {
                *ls = l.clone();
                ub.clone().iter().map(|s| propagate_up(univ, s, l)).collect::<Result<(), Error>>()?;
            }
            Ok(())
        }

        // Propagates the constaint s <= u in the graph of sort variables constraints
        fn propagate_down(univ: &mut Context, s: &VarType, u: &Sort) -> Result<(), Error> {
            let (_, us, lb, _) = univ.sorts.get_mut(*s).ok_or(Error::UnboundSort(s.clone()))?;
            if *u < *us {
                *us = u.clone();
                lb.clone().iter().map(|s| propagate_down(univ, s, u)).collect::<Result<(), Error>>()?;
            }
            Ok(())
        }

        match (s1, s2) {
            (Sort::Var(s1), Sort::Var(s2)) => {
                let (l1, _, _, _) = self.sorts.get(s1).ok_or(Error::UnboundSort(s1))?;
                let (_, u2, _, _) = self.sorts.get(s2).ok_or(Error::UnboundSort(s2))?;
                if u2 < l1 { Err(Error::SortInconsistency(u2.clone(), l1.clone()))? };

                let (l1, _, _, ub1) = self.sorts.get_mut(s2).unwrap();
                ub1.insert(s2);
                let l1 = l1.clone();
                propagate_up(self, &s2, &l1)?;

                let (_, u2, lb2, _) = self.sorts.get_mut(s1).unwrap();
                lb2.insert(s1);
                let u2 = u2.clone();
                propagate_down(self, &s1, &u2)?;
            }
            (Sort::Var(s1), s2) => {
                let (l, u, _, _) = self.sorts.get_mut(s1).ok_or(Error::UnboundSort(s1))?;
                if s2 < *l { Err(Error::SortInconsistency(s2, l.clone()))? };
                let u = u.clone();
                propagate_down(self, &s1, &u)?;
            }
            (s1, Sort::Var(s2)) => {
                let (l, u, _, _) = self.sorts.get_mut(s2).ok_or(Error::UnboundSort(s2))?;
                if *u < s1 { Err(Error::SortInconsistency(u.clone(), s1))? };
                let l = l.clone();
                propagate_up(self, &s2, &l)?;
            }
            (s1, s2) => { if s2 < s1 { Err(Error::SortInconsistency(s2, s1))? }; }
        }
        Ok(self)
    }

    /* Adding a constraint [u1 <= u2] to the context of universe levels. */
    pub fn add_level_constraint(&mut self, u1: Level, u2: Level) -> Result<&mut Self, Error> {
        /* For every level variable u in the domain of u1, we add the constraint u + u1(u) <= u2.
         * We only add a constraint if it is not obviously redundant, and we remove constraints
         * that become obviously redundant.
         * We compute the set [updt] of level variables for which we add a constraint. */ 
        let mut updt = HashSet::new();
        u1.clone().vars.into_iter().map(|(u, n)| {
            let u2 = u2.clone().add(-n);
            let ubs = self.levels.get_mut(u).ok_or(Error::UnboundUniv(u))?;
            let mut ditch = false;
            *ubs = ubs.iter().filter(|v| {
                if ditch { true } else {
                    match v.wcmp(&u2) {
                        None => { true }
                        // If v <= u2 , u2 is redundant.
                        Some(x) if x != std::cmp::Ordering::Greater => {
                            ditch = true;
                            true
                        }
                        // If u2 <= v , v becomes redundant.
                        _ => { false }
                    }
                }
            }).map(|x| x.clone()).collect();
            if !ditch {
                updt.insert(u);
                ubs.push(u2);
            };
            Ok(())
        }).collect::<Result<(), _>>()?;
        self.saturate_model(/*updt*/).map_err(|_| Error::UnivInconsistency(Univ { sort: Sort::Type(), level: u1 }, Univ { sort: Sort::Type(), level: u2 }))
    }

    /* Adding a constraint [u1 <= u2] to the context of universes. */
    pub fn add_constraint(&mut self, u1: Univ, u2: Univ) -> Result<&mut Self, Error> {
        // Let's destruct u1 and u2.
        let Univ { sort: s1, level: u1 } = u1;
        let Univ { sort: s2, level: u2 } = u2;
        // We assert that s1 = s2.
        self.add_sort_constraint(s1.clone(), s2.clone())?;
        self.add_sort_constraint(s2.clone(), s1.clone())?;
        self.add_level_constraint(u1, u2)
    }

    /* Auxiliary function for saturate_model, where we only consider constraints that have their
     * conclusion in the given domain. */
    fn saturate_onto(&mut self, dom: &HashSet<VarType>) -> Result<&mut Self, HashSet<VarType>> {
        loop {
            self.saturate_over(dom)?;

            let mut done = true;

            for u in dom.iter() {
                let ubs = self.levels.get(*u).unwrap();
                for v in ubs.iter() {
                    let k = v.vars.iter().map(|(v, m)| {
                        (*self.model.get(*v).unwrap() as isize) - m
                    }).min().unwrap();
                    if k <= 0 || *self.model.get(*u).unwrap() < (k as usize) {
                        self.model.insert(u.clone(), k as usize);
                        done = false;
                    };
                }
            }

            if done { break; }
        }

        Ok(self)
    }


    /* Auxiliary function for saturate_model, where we only consider constraints that are over the
     * elements of the given domain. */
    fn saturate_over(&mut self, dom: &HashSet<VarType>) -> Result<&mut Self, HashSet<VarType>> {
        if dom.len() == 0 { return Ok(self) };
        let mut updt = HashSet::new();
        let mut n = 0;

        loop {
            for u in dom.iter() {
                let ubs = self.levels.get(*u).unwrap();
                for v in ubs.iter() {
                    let k = v.vars.iter().map(|(v, m)| {
                        (*self.model.get(*v).unwrap() as isize) - m
                    }).min().unwrap();
                    if k <= 0 || *self.model.get(*u).unwrap() < k as usize {
                        self.model.insert(u.clone(), k as usize);
                        updt.insert(u.clone());
                    };
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
        self.saturate_over(&(0..self.model.len()).into_iter().collect())
    }

    /* Removes a level variable from the context, returning a minimal level that may be equal to
     * that level variable according to the current constraints. */
    pub fn minimize_level(&mut self, u: VarType) -> Level {
        let mut lb = Level { vars: BTreeMap::new() };

        for v in 0..self.model.len() {
            if v == u { continue; }
            for i in 0..(self.levels.get(v).unwrap().len()) {
                let w = self.levels.get_mut(v).unwrap().get_mut(i).unwrap();
                if !w.vars.contains_key(&u) { continue; }
                let n = w.vars.remove(&u).unwrap();
                let w = w.clone();
                self.levels.get_mut(u).unwrap().push(w);
                let model = self.model.clone();
                if !self.saturate_model().is_ok() {
                    self.model = model.clone();
                    self.levels.get_mut(u).unwrap().pop();
                    let w = self.levels.get_mut(v).unwrap().get_mut(i).unwrap();
                    let mut w0 = Level { vars: BTreeMap::from([(v.clone(), n)]) };
                    std::mem::swap(w, &mut w0);
                    lb = lb.max(w0.succ());
                }
            }
        }

        lb
    }

    pub fn minimize_model(&mut self) -> &mut Self {
        for v in self.model.iter_mut() { *v = 0 }

        self.saturate_model().unwrap()
    }

    pub fn append(&mut self, ctx: Context) -> (Vec<Sort>, Vec<Level>) {
        let Context { sorts, levels, mut model } = ctx;

        let ns = self.sorts.len();
        let nu = self.model.len();
        
        let mut sorts: Vec<_> = sorts.into_iter().map(|(lb, ub, lbs, ubs)| (lb, ub, lbs.into_iter().map(|s| s + ns).collect(), ubs.into_iter().map(|s| s + ns).collect())).collect();
        self.sorts.append(&mut sorts);

        self.levels.append(&mut levels.into_iter().map(|ubs| ubs.into_iter().map(|u| Level { vars: u.vars.into_iter().map(|(u, i)| (u + nu, i)).collect() } ).collect()).collect());

        self.model.append(&mut model);

        ((0..sorts.len()).map(|s| Sort::Var(s + ns)).collect(),
            (0..model.len()).map(|u| Level { vars: BTreeMap::from([(u + nu, 0)]) }).collect())
    }
}
