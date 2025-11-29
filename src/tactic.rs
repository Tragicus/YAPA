use crate::engine::term::*;
use crate::engine::error::*;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::collections::HashSet;
use crate::command::Status;

#[derive(Clone, Debug)]
pub struct Goal {
    ctx: Telescope,
    goal: VarType
}

impl PartialEq for Goal {
    fn eq(&self, other: &Self) -> bool {
        self.goal == other.goal
    }
}

impl Eq for Goal {}

impl Ord for Goal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.goal.cmp(&other.goal)
    }
}

impl PartialOrd for Goal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for Goal {
    fn hash<H : Hasher>(&self, state: &mut H) {
        self.goal.hash(state)
    }
}

impl Goal {
    pub fn of_hole(h: VarType) -> Self {
        Goal { ctx: VecDeque::new(), goal: h }
    }
}

impl Term {
    pub fn collect_goals(&self, ctx: &mut crate::engine::context::Context) -> Result<HashSet<Goal>, crate::engine::error::Error> {
        let goals = HashSet::<Goal>::new();
        self.fold(ctx, |ctx, t, mut goals| {
            if let Term::Hole(h) = t.head() {
                if !goals.contains(&Goal::of_hole(h.clone())) {
                    let (_, n) = match t {
                        Term::App(args) => args.iter().skip(1).fold((true, 0), |(b, i), t|
                            if b && (**t == Term::Var(ctx.var.len() - i - 1)) { (b, i + 1) } else { (false, i) }),
                        _ => (true, 0)
                    };
                    goals.insert(Goal { ctx: ctx.var.iter().take(n).map(|x| x.clone()).collect(), goal: h.clone() });
                }
            };
            goals
        }, goals)
    }
}

#[derive(Debug)]
pub enum Tactic {
    Exact(crate::parser::Term),
    Refine(crate::parser::Term)
}

impl Tactic {
    pub fn exec(self, ctx: &mut crate::command::Context) -> () {
        if let Status::Proofmode(_, _, _, goals) = &mut ctx.status {
            match self {
                Tactic::Exact(t) => {
                    let mut g = match goals.pop_front() { None => { return (); } Some(g) => g };
                    std::mem::swap(&mut ctx.engine.var, &mut g.ctx);
                    let t = t.capture_vars(&mut ctx.engine);
                    if t.has_hole(&ctx.engine) {
                        Err(Error { ctx: ctx.engine.clone(), err: TypeError::NotGround(t.clone()) }).unwrap()
                    };
                    let args = crate::utils::iota(g.ctx.len()).into_iter().map(|i| Term::Var(g.ctx.len() - i - 1).into()).collect();
                    ctx.engine.instantiate_hole(&Term::Hole(g.goal).apps(args), t).unwrap();
                    std::mem::swap(&mut ctx.engine.var, &mut g.ctx);
                }
                Tactic::Refine(t) => {
                    let mut g = match goals.pop_front() { None => { return (); } Some(g) => g };
                    std::mem::swap(&mut ctx.engine.var, &mut g.ctx);
                    let t = t.capture_vars(&mut ctx.engine);
                    let args = crate::utils::iota(g.ctx.len()).into_iter().map(|i| Term::Var(g.ctx.len() - i - 1).into()).collect();
                    let mut newgoals = t.collect_goals(&mut ctx.engine).unwrap().into_iter().collect::<VecDeque<_>>();
                    ctx.engine.instantiate_hole(&Term::Hole(g.goal).apps(args), t.fun(ctx.engine.var.clone())).unwrap();
                    newgoals.append(goals);
                    *goals = newgoals;
                    std::mem::swap(&mut ctx.engine.var, &mut g.ctx);
                }
            }
        } else { panic!("Cannot apply tactic when not in proof mode.") }
    }
}
