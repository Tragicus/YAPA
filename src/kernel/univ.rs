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

impl Sort {
    pub fn is_var(&self) -> bool {
        match self {
            Sort::Var(_) => true,
            _ => false
        }
    }
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

impl IntoIterator for Level {
    type Item = <BTreeMap<VarType, isize> as IntoIterator>::Item;
    type IntoIter = <BTreeMap<VarType, isize> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        assert!(self.vars.len() != 0);
        self.vars.into_iter()
    }
}

impl Level {
    pub fn iter<'a>(&'a self) -> std::collections::btree_map::Iter<'a, VarType, isize> {
        assert!(self.vars.len() != 0);
        self.vars.iter()
    }

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
        let mut it = self.iter().peekable();
        let mut it2 = other.iter().peekable();
        loop {
            match (it.peek(), it2.peek()) {
                (None, None) => { return Some(cmp.unwrap_or(std::cmp::Ordering::Equal)); },
                (None, _) => { assign(std::cmp::Ordering::Less).ok()?; return cmp; },
                (_, None) => { assign(std::cmp::Ordering::Greater).ok()?; return cmp; },
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

    pub fn wle(&self, other: &Self) -> bool {
        match self.wcmp(other) {
            Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal) => true,
            _ => false
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
            fmt_atom(f, self.iter().next().unwrap())
        } else {
            write!(f, "max(")?;
            let mut it = self.iter();
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
    pub sorts: Vec<(Option<String>, Sort, Sort, HashSet<VarType>, HashSet<VarType>)>,
    pub levels: Vec<(Option<String>, Vec<Level>)>,
    pub model: Vec<usize>,
}

impl Context {
    /* Empty context.
     * We initialize the 0 level variable, which is always defined. */
    pub fn new() -> Context {
        Context {
            sorts: vec![],
            levels: vec![(Some("".to_string()), vec![])],
            model: vec![0]
        }
    }

    pub fn new_sort(&mut self, name: Option<String>) -> VarType {
        let s = self.sorts.len();
        self.sorts.push((name, Sort::SProp(), Sort::Type(), HashSet::new(), HashSet::new()));
        s
    }

    pub fn new_level(&mut self, name: Option<String>) -> VarType {
        let u = self.model.len();
        self.levels.push((name, vec![]));
        self.model.push(0);
        self.levels.get_mut(0).unwrap().1.push(Level { vars: BTreeMap::from([(u.clone(), 0)]) });
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        u
    }

    pub fn new_univ(&mut self, s: Option<String>, u: Option<String>) -> Univ {
        let s = self.new_sort(s);
        let u = self.new_level(u);
        Univ { sort: Sort::Var(s), level: Level { vars: BTreeMap::from([(u, 0)]) } }
    }

    /* Adding a constraint [s1 <= s2] to the context of sorts. */
    pub fn add_sort_constraint(&mut self, s1: Sort, s2: Sort) -> Result<&mut Self, Error> {
        // Propagates the constraint l <= s in the graph of sort variables constraints
        fn propagate_up(univ: &mut Context, s: &VarType, l: &Sort) -> Result<(), Error> {
            let (_, ls, _, _, ub) = univ.sorts.get_mut(*s).ok_or(Error::UnboundSort(s.clone()))?;
            if *ls < *l {
                *ls = l.clone();
                ub.clone().iter().map(|s| propagate_up(univ, s, l)).collect::<Result<(), Error>>()?;
            }
            Ok(())
        }

        // Propagates the constraint s <= u in the graph of sort variables constraints
        fn propagate_down(univ: &mut Context, s: &VarType, u: &Sort) -> Result<(), Error> {
            let (_, _, us, lb, _) = univ.sorts.get_mut(*s).ok_or(Error::UnboundSort(s.clone()))?;
            if *u < *us {
                *us = u.clone();
                lb.clone().iter().map(|s| propagate_down(univ, s, u)).collect::<Result<(), Error>>()?;
            }
            Ok(())
        }

        match (s1, s2) {
            (Sort::Var(s1), Sort::Var(s2)) => {
                let (_, l1, _, _, _) = self.sorts.get(s1).ok_or(Error::UnboundSort(s1))?;
                let (_, _, u2, _, _) = self.sorts.get(s2).ok_or(Error::UnboundSort(s2))?;
                if u2 < l1 { Err(Error::SortInconsistency(u2.clone(), l1.clone()))? };

                let (_, l1, _, _, ub1) = self.sorts.get_mut(s2).unwrap();
                ub1.insert(s2);
                let l1 = l1.clone();
                propagate_up(self, &s2, &l1)?;

                let (_, _, u2, lb2, _) = self.sorts.get_mut(s1).unwrap();
                lb2.insert(s1);
                let u2 = u2.clone();
                propagate_down(self, &s1, &u2)?;
            }
            (Sort::Var(s1), s2) => {
                let (_, l, u, _, _) = self.sorts.get_mut(s1).ok_or(Error::UnboundSort(s1))?;
                if s2 < *l { Err(Error::SortInconsistency(s2, l.clone()))? };
                let u = u.clone();
                propagate_down(self, &s1, &u)?;
            }
            (s1, Sort::Var(s2)) => {
                let (_, l, u, _, _) = self.sorts.get_mut(s2).ok_or(Error::UnboundSort(s2))?;
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
        assert!(u1.vars.len() != 0);
        let mut updt = HashSet::new();
        u1.clone().into_iter().map(|(u, n)| {
            let mut u2 = u2.clone().add(-n);
            if u2.vars.contains_key(&u) {
                if 0 <= *u2.vars.get(&u).unwrap() { return Ok(()); }
                u2.vars.remove(&u);
            }
            if u2.vars.len() == 0 { return Ok(()); }
            let ubs = &mut self.levels.get_mut(u).ok_or(Error::UnboundUniv(u))?.1;
            let mut ditch = false;
            *ubs = ubs.iter().filter(|v| {
                if ditch { true } else {
                    match v.wcmp(&u2) {
                        None => { true }
                        // If v <= u2, u2 is redundant.
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
        //println!("saturate in {:?}", self);
        self.saturate_model(/*updt*/).map_err(|_| Error::UnivInconsistency(Univ { sort: Sort::Type(), level: u1 }, Univ { sort: Sort::Type(), level: u2 }))
    }

    /* Adding a constraint [u1 <= u2] to the context of universes.
     * In case of error, the context is returned in an invalid state. */
    pub fn add_constraint(&mut self, u1: Univ, u2: Univ) -> Result<&mut Self, Error> {
        //println!("{:?} <= {:?}\n in {:?}", u1, u2, self);
        // Let's destruct u1 and u2.
        let Univ { sort: s1, level: u1 } = u1;
        let Univ { sort: s2, level: u2 } = u2;
        // We assert that s1 = s2.
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        self.add_sort_constraint(s1.clone(), s2.clone())?;
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        self.add_sort_constraint(s2.clone(), s1.clone())?;
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        self.add_level_constraint(u1, u2)?;
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        Ok(self)
    }

    /* Auxiliary function for saturate_model, where we only consider constraints that have their
     * conclusion in the given domain. */
    fn saturate_onto(&mut self, dom: &HashSet<VarType>) -> Result<&mut Self, HashSet<VarType>> {
        loop {
            self.saturate_over(dom)?;

            let mut done = true;

            for u in dom.iter() {
                let ubs = &self.levels.get(*u).unwrap().1;
                for v in ubs.iter() {
                    let k = v.iter().map(|(v, m)| {
                        (*self.model.get(*v).unwrap() as isize) - m
                    }).min().unwrap();
                    if 0 <= k && *self.model.get(*u).unwrap() < (k as usize) {
                        self.model[*u] = k as usize;
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
                let ubs = &self.levels.get(*u).unwrap().1;
                for v in ubs.iter() {
                    let k = v.iter().map(|(v, m)| {
                        (*self.model.get(*v).unwrap() as isize) - m
                    }).min().unwrap();
                    if 0 <= k && *self.model.get(*u).unwrap() < k as usize {
                        self.model[*u] = k as usize;
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

    /* Removes `l` from the graph of sort levels. */
    fn instantiate_sort(&mut self, l: VarType) {
        let mut lbs = HashSet::<VarType>::new();
        let mut ubs = HashSet::<VarType>::new();
        std::mem::swap(&mut lbs, &mut self.sorts[l].3);
        std::mem::swap(&mut ubs, &mut self.sorts[l].4);
        lbs.remove(&l);
        ubs.remove(&l);

        for v in 0..self.sorts.len() {
            if self.sorts[v].3.contains(&l) {
                self.sorts[v].3 = self.sorts[v].3.union(&lbs).map(|u| u.clone()).collect();
            }
            if self.sorts[v].4.contains(&l) {
                self.sorts[v].4 = self.sorts[v].4.union(&ubs).map(|u| u.clone()).collect();
            }
        }
    }

    /* Replaces `l` by `u` in the graph of universe level variables (except from the upper bounds of `0`).
     * Assumes that this instantiation is correct, i.e. does not change the set of valid
     * instantiations for the other level variables. */
    fn instantiate_level(&mut self, l: VarType, u: &Level) {
        for v in 1..self.levels.len() {
            if v == l {
                self.levels[v].1 = Vec::new();
            } else {
                let mut ubs = Vec::new();
                std::mem::swap(&mut ubs, &mut self.levels[v].1);
                self.levels[v].1 = ubs.into_iter().filter_map(|mut ub|
                    match ub.vars.remove(&l) {
                        None => Some(ub),
                        Some(n) => {
                            let mut u = u.clone().add(n);
                            match u.vars.remove(&v) {
                                Some(n) if 0 <= n => None,
                                _ => Some(ub.max(u)),
                            }
                        }
                    }).collect();
            }
        }
    }

    /* Removes a level variable from the context, returning a minimal level that may be equal to
     * that level variable according to the current constraints. */
    pub fn minimize_level(&mut self, u: VarType) -> Level {
        assert!(u != 0);
        //println!("minimize {} in {:?}", u, self);
        let mut lb = Level { vars: BTreeMap::new() };

        for v in (0..self.model.len()).filter(|v| *v != u) {
            for i in 0..(self.levels[v].1.len()) {
                let w = &mut self.levels[v].1[i];
                if !w.vars.contains_key(&u) { continue; }
                if w.vars.len() == 1 {
                    lb = lb.max(Level { vars: BTreeMap::from([(v.clone(), - w.vars[&u].clone())]) });
                    continue;
                }
                let n = w.vars.remove(&u).unwrap();
                let w = w.clone().add(-n);
                self.levels[u].1.push(w);
                let model = self.model.clone();
                if !self.saturate_model().is_ok() {
                    self.model = model;
                    self.levels[u].1.pop();
                    let w = &mut self.levels[v].1[i];
                    let mut w0 = Level { vars: BTreeMap::from([(v.clone(), n)]) };
                    std::mem::swap(w, &mut w0);
                    lb = lb.max(w0.succ()).max(Level { vars: BTreeMap::from([(u.clone(), -n)]) });
                }
            }
        }

        assert!(lb.vars.len() != 0);

        lb
    }

    pub fn minimize_model(&mut self) -> &mut Self {
        for v in self.model.iter_mut() { *v = 0 }

        self.saturate_model().expect("Anomaly: minimizing the universe model should not fail.")
    }

    pub fn append(&mut self, ctx: Context) -> (Vec<Sort>, Vec<Level>) {
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        //println!("append {:?} in {:?}", ctx, self);
        let Context { sorts, levels, model } = ctx;

        let ns = self.sorts.len();
        let nu = self.model.len();

        // We build the output now before destroying sorts and model.
        let su = ((0..sorts.len()).map(|s| Sort::Var(s + ns)).collect(),
            std::iter::once(Level { vars: BTreeMap::from([(0, 0)]) }).chain((1..model.len()).map(|u| Level { vars: BTreeMap::from([(u + nu - 1, 0)]) })).collect());
        
        let mut sorts: Vec<_> = sorts.into_iter().map(|(n, lb, ub, lbs, ubs)| (n, lb, ub, lbs.into_iter().map(|s| s + ns).collect(), ubs.into_iter().map(|s| s + ns).collect())).collect();
        self.sorts.append(&mut sorts);

        let mut levels = levels.into_iter().map(|(v, ubs)| (v, ubs.into_iter().map(|u| Level { vars: u.into_iter().map(|(u, i)| (if u == 0 { 0 } else { u + nu - 1 }, i)).collect() } ).collect::<Vec<_>>()));
        levels.next().map(|(_, mut ubs)| self.levels[0].1.append(&mut ubs));
        self.levels.append(&mut levels.collect());

        self.model.append(&mut model.into_iter().skip(1).collect());

        assert!(self.levels[0].1.len() + 1 == self.model.len());

        su
    }

    // Prunes the sort and level variables that do not appear in fs and fu respectively, returning
    // the substitutions to apply to term from the input context.
    pub fn keep_univs(&mut self, fs: HashSet<VarType>, mut fu: HashSet<VarType>) -> Result<(Vec<Sort>, Vec<Level>), Error> {
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        fu.insert(0);
        //println!("fu: {:?} in {:?}", fu, self);

        // We instantiate every sort variable outside of fs by its upper bound.
        // We also rename the sort variables we keep so that they form an initial segment of NN.
        let mut k = 0;
        let mut substs : Vec<_> = (0..self.sorts.len()).map(|s|
            if !fs.contains(&s) {
                self.instantiate_sort(s); self.sorts[s].1.clone()
            } else {
               k = k+1;
               Sort::Var(k-1)
            }).collect();
        // For any s < self.sorts.len(), if fs contains s then substs[s] contains the new name
        // of s. Otherwise, either substs[s] is an explicit sort, or s was removed from fs in the
        // line above and substs[s] is Var(s0) with s0 > s.

        // We compute the substitutions of the old sort variables in terms of the new sort
        // variables.
        for s in (0..self.sorts.len()).rev().filter(|s| !fs.contains(&s)) {
            if let Sort::Var(s0) = substs[s] {
                substs[s] = substs[s0].clone();
            }
        }

        // We minimize every level variable outside of fu.
        // We also rename the level variables we keep so that they form an initial segment of NN.
        let mut k = 0;
        let mut substu: Vec<_> = std::iter::once(Level { vars: BTreeMap::from([(0, 0)]) }).chain((1..self.model.len()).map(|u|
            if !fu.contains(&u) { 
                let v = self.minimize_level(u.clone());
                self.levels[u].1 = vec![];
                v
            } else {
                k = k+1;
                Level { vars: BTreeMap::from([(k, 0)]) }
            })).collect();
        //println!("substu: {:?}", substu);
        // For any u < self.model.len(), if fu contains u then substu[u] contains the new name
        // of u. Otherwise, either substs[u] is an explicit level in terms of kept level variables
        // and larger variables.

        // We compute the substitutions of the old level variables in terms of the new level
        // variables.
        for i in (0..substu.len()).rev().filter(|i| !fu.contains(&i)) {
            let mut v = BTreeMap::new();
            std::mem::swap(&mut substu[i].vars, &mut v);
            //println!("v: {:?}", v);
            substu[i] = v.into_iter().map(|(u, i)| substu[u].clone().add(i)).reduce(Level::max).unwrap();
            //println!("substu: {:?}", substu);
        }

        let mut sorts = Vec::new();
        std::mem::swap(&mut self.sorts, &mut sorts);
        self.sorts = sorts.into_iter().enumerate().filter(|(i, _)| fs.contains(&i)).map(|(_, (v, lb, ub, lbs, ubs))|
            (v, lb, ub,
             lbs.into_iter().map(|i| if let Sort::Var(j) = substs[i] { j } else { unreachable!() }).collect(),
             ubs.into_iter().map(|i| if let Sort::Var(j) = substs[i] { j } else { unreachable!() }).collect())
        ).collect();

        let mut levels = Vec::new();
        std::mem::swap(&mut self.levels, &mut levels);
        self.levels = levels.into_iter().enumerate().filter(|(i, _)| fu.contains(&i)).map(|(_, (v, ubs))| (v,
            ubs.into_iter().map(|u| 
                u.into_iter().map(|(u, i)| substu[u].clone().add(i)).reduce(Level::max).unwrap()
            ).collect()
        )).collect();
        self.levels[0].1 = (1..k+1).map(|i| Level { vars: BTreeMap::from([(i, 0)]) }).collect();

        let mut model = Vec::new();
        std::mem::swap(&mut self.model, &mut model);
        self.model = model.into_iter().enumerate().filter(|(i, _)| fu.contains(&i)).map(|(_, u)| u).collect();

        self.minimize_model();
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        Ok((substs, substu))
    }

    // Prunes the sort and level variables that are provably equal to some other sort and levels, returning
    // the substitutions to apply to term from the input context.
    pub fn optimize(&mut self) -> Result<(Vec<Sort>, Vec<Level>), Error> {
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        //println!("optimize {:?}", self);
        let mut fu = HashSet::new();
        let mut fs = HashSet::new();

        // We instantiate every sort variable which is provably equal to a greater one by this other one.
        // These variables are added to fs.
        // We also rename the sort variables we keep so that they form an initial segment of NN.
        let mut k = 0;
        let mut substs : Vec<_> = (0..self.sorts.len()).map(|s| {
            let (_, _, _, lbs, ubs) = &self.sorts[s];
            match lbs.intersection(ubs).filter(|s0| s < **s0).next().map(|s0| s0.clone()) {
                None => { k = k+1; Sort::Var(k-1) }
                Some(s0) => { self.instantiate_sort(s); fs.insert(s.clone()); Sort::Var(s0) }
            }
        }).collect();
        // For any s < self.sorts.len(), if fs contains s then substs[s] contains the new name
        // of s. Otherwise, either substs[s] is an explicit sort, or s was removed from fs in the
        // line above and substs[s] is Var(s0) with s0 > s.

        // We compute the substitutions of the old sort variables in terms of the new sort
        // variables.
        for s in (0..self.sorts.len()).rev().filter(|s| fs.contains(&s)) {
            if let Sort::Var(s0) = substs[s] {
                substs[s] = substs[s0].clone();
            }
        }

        // We minimize every level variable outside of fu and instantiate every other level
        // variable which is provably equal to some universe level this level. The latter variables
        // are removed from fu.
        // We also rename the level variables we keep so that they form an initial segment of NN.
        let mut k = 0;
        let mut substu: Vec<_> = std::iter::once(Level { vars: BTreeMap::from([(0, 0)]) }).chain((1..self.model.len()).map(|u| {
            let mut lb = Level { vars: BTreeMap::new() };
            for v in 0..self.model.len() {
                if let Some(n) = self.levels[v].1.iter().filter(|ub| ub.vars.len() == 1 && ub.vars.keys().next() == Some(&u)).map(|ub| - ub.vars[&u]).reduce(std::cmp::max) {
                    lb.vars.insert(v.clone(), n);
                }
            }
            assert!(lb.vars.len() != 0);
            if self.levels[u].1.iter().any(|ub| ub.wle(&lb)) {
                fu.insert(u.clone());
                let mut itlb = lb.vars.iter();
                let lb0 = itlb.next().unwrap().1;
                if itlb.any(|(_, n)| lb0 <= n) {
                    lb.vars.remove(&0);
                }
                self.instantiate_level(u, &lb);
                lb
            } else {
                k = k+1;
                Level { vars: BTreeMap::from([(k, 0)]) }
            }
        })).collect();
        //println!("substu: {:?}", substu);
        // For any u < self.model.len(), if fu contains u then substu[u] contains the new name
        // of u. Otherwise, either substs[u] is an explicit level in terms of kept level variables
        // and larger variables.

        // We compute the substitutions of the old level variables in terms of the new level
        // variables.
        for i in (0..substu.len()).rev().filter(|i| fu.contains(&i)) {
            let mut v = BTreeMap::new();
            std::mem::swap(&mut substu[i].vars, &mut v);
            //println!("v: {:?}", v);
            substu[i] = v.into_iter().map(|(u, i)| substu[u].clone().add(i)).reduce(Level::max).unwrap();
            //println!("substu: {:?}", substu);
        }

        let mut sorts = Vec::new();
        std::mem::swap(&mut self.sorts, &mut sorts);
        self.sorts = sorts.into_iter().enumerate().filter(|(i, _)| !fs.contains(&i)).map(|(_, (v, lb, ub, lbs, ubs))|
            (v, lb, ub,
             lbs.into_iter().map(|i| if let Sort::Var(j) = substs[i] { j } else { unreachable!() }).collect(),
             ubs.into_iter().map(|i| if let Sort::Var(j) = substs[i] { j } else { unreachable!() }).collect())
        ).collect();

        let mut levels = Vec::new();
        std::mem::swap(&mut self.levels, &mut levels);
        self.levels = levels.into_iter().enumerate().filter(|(i, _)| !fu.contains(&i)).map(|(_, (v, ubs))| (v,
            ubs.into_iter().map(|u| 
                u.into_iter().map(|(u, i)| substu[u].clone().add(i)).reduce(Level::max).unwrap()
            ).collect()
        )).collect();
        self.levels[0].1 = (1..k+1).map(|i| Level { vars: BTreeMap::from([(i, 0)]) }).collect();

        let mut model = Vec::new();
        std::mem::swap(&mut self.model, &mut model);
        self.model = model.into_iter().enumerate().filter(|(i, _)| !fu.contains(&i)).map(|(_, u)| u).collect();

        self.minimize_model();
        assert!(self.levels[0].1.len() + 1 == self.model.len());
        Ok((substs, substu))
    }

}
