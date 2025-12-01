use crate::engine::term::*;
use crate::engine::error::*;
use crate::kernel::reduction::WhdFlags;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct Goal {
    pub ctx: Telescope,
    pub goal: VarType
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

    pub fn target(&self, ctx: &mut crate::engine::context::Context) -> Term {
        let args = crate::utils::iota(ctx.var.len()).into_iter().map(|i| Term::Var(ctx.var.len() - i - 1).into()).collect();
        Term::Hole(self.goal.clone()).apps(args)
    }

    // Sets the correct context to work on the provided goal. The closure takes said context and
    // the target of the goal (i.e. the term to instantiate).
    pub fn enter<T, F : FnOnce(&mut crate::engine::context::Context, Term) -> T>(&mut self, ctx: &mut crate::engine::context::Context, f: F) -> T {
        std::mem::swap(&mut ctx.var, &mut self.ctx);
        let target = self.target(ctx);
        let t = f(ctx, target);
        std::mem::swap(&mut ctx.var, &mut self.ctx);
        t
    }

    pub fn pp(&self, ctx: &mut crate::engine::context::Context) -> Result<String, Error> {
        let tg = self.target(ctx).type_of(ctx)?.whd(ctx, WhdFlags::empty().beta())?;
        let s = ctx.var.clone().into_iter();
        let (s, ctx) = s.fold(Ok(("".to_string(), ctx)), |s, (v, t, b)| {
            let (s, ctx) = s?;
            let st = t.pp(ctx)?;
            Ok((s + &v + " : " + &st + &b.map_or(Ok("".to_string()), |b| Ok(" := ".to_string() + &b.pp(ctx)?))? + "\n", ctx))
        })?;
        Ok(s + "\n==========================\n\n" + &tg.pp(ctx)? + "\n")
    }
}

impl Term {
    pub fn collect_goals(&self, ctx: &mut crate::engine::context::Context) -> Result<HashSet<Goal>, crate::engine::error::Error> {
        let goals = HashSet::<Goal>::new();
        self.fold(ctx, |ctx, t, goals| {
            let mut goals = goals?;
            if let Term::Hole(h) = t.clone().whd(ctx, WhdFlags::empty())?.head() {
                if !goals.contains(&Goal::of_hole(h.clone())) {
                    let (_, n) = match t {
                        Term::App(args) => args.iter().skip(1).fold((true, 0), |(b, i), t|
                            if b && (**t == Term::Var(ctx.var.len() - i - 1)) { (b, i + 1) } else { (false, i) }),
                        _ => (true, 0)
                    };
                    goals.insert(Goal { ctx: ctx.var.iter().take(n).map(|x| x.clone()).collect(), goal: h.clone() });
                }
            };
            Ok(goals)
        }, Ok(goals)).flatten()
    }
}

