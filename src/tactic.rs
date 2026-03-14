use crate::engine::term::*;
use crate::kernel::reduction::WhdFlags;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::collections::HashSet;
use crate::command::Context;
use crate::command::Status;
use crate::goal::Goal;
use crate::error::*;

#[derive(Debug, Clone)]
pub enum Tactic {
    Exact(crate::parser::Term),
    Refine(crate::parser::Term),
    Apply(Vec<crate::parser::Term>),
    Intro(Vec<String>),
    Clear(Vec<String>),
    Assumption(),
    Seq(VecDeque<Tactic>),
}

pub fn exec_seq(tacs: &VecDeque<Tactic>, ctx: &mut crate::engine::context::Context, goal: Goal, i: usize) -> Result<VecDeque<Goal>, Error> {
    Ok(if i == tacs.len() { VecDeque::from([goal]) } else {
        tacs[i].clone().exec(ctx, goal)?.into_iter().filter_map(|g| {
            if ctx.get_hole_body(&g.goal).unwrap().is_some() { None } else {
                Some(exec_seq(tacs, ctx, g, i+1))
            }
        }).into_iter().collect::<Result<VecDeque<_>, _>>()?.into_iter().flatten().collect()
    })
}

impl Tactic {
    pub fn exec(self, ctx: &mut crate::engine::context::Context, mut goal: Goal) -> Result<VecDeque<Goal>, Error> {
        let subgoals = match self {
            Tactic::Exact(t) => {
                goal.enter(ctx, |ctx, g| {
                    let t = t.capture_vars(ctx)?;
                    ctx.instantiate_hole(&g, t.clone())?;
                    if t.has_hole(&ctx) {
                        Err(crate::engine::error::Error::NotGround(t.clone()))
                    } else { Ok(()) }
                })?;
                Ok(VecDeque::from([goal]))
            }
            Tactic::Refine(t) => {
                Ok(goal.enter(ctx, |ctx, g| {
                    let t = t.capture_vars(ctx)?;
                    let mut newgoals = t.collect_goals(ctx)?.into_iter().collect::<VecDeque<_>>();
                    newgoals.make_contiguous().sort();
                    ctx.instantiate_hole(&g, t)?;
                    Ok::<_, Error>(newgoals)
                })?)
            }
            Tactic::Apply(mut t) => {
                if t.len() == 0 {
                    Tactic::Seq(VecDeque::from([
                        Tactic::Intro(vec!["__".to_string()]),
                        Tactic::Apply(vec![crate::parser::Term::Const("__".to_string())]),
                        Tactic::Clear(vec!["__".to_string()])])).exec(ctx, goal)
                } else {
                    if t.len() != 1 {
                        Tactic::Seq(t.into_iter().map(|t| Tactic::Apply(vec![t])).collect()).exec(ctx, goal)
                    } else {
                        let t = t.pop().unwrap();
                        Ok(goal.enter(ctx, |ctx, g| {
                            let mut t = t.capture_vars(ctx)?;
                            let tg = g.type_of(ctx)?;
                            let mut newgoals: VecDeque<_>;
                            loop {
                                let ty = t.type_of(ctx)?;
                                if crate::engine::typing::unify(ctx, &ty, &tg)? {
                                    newgoals = t.collect_goals(ctx)?.into_iter().collect();
                                    newgoals.make_contiguous().sort();
                                    ctx.instantiate_hole(&g, t)?;
                                    break;
                                }
                                let (n, ty, _) = &ty.whd(ctx, WhdFlags::default())?.dest_forall()?.0[0];
                                let h = ctx.new_hole(n.clone(), Some(ty.clone()), true);
                                t = t.app(h);
                            }
                            Ok::<_, Error>(newgoals)
                        })?)
                    }
                }
            }
            Tactic::Intro(names) => {
                goal.enter(ctx, |ctx, g| {
                    let mut tg = g.type_of(ctx)?;
                    names.into_iter().fold(Ok::<_, Error>(()), |ok, name| {
                        ok?;
                        let (mut tele, concl) = tg.clone().whd(ctx, WhdFlags::default())?.dest_forall()?;
                        let (_, ty, body) = tele.pop_front().ok_or(crate::engine::error::Error::NotAForall(tg.clone()))?;
                        ctx.push_var((name, ty, body));
                        tg = concl.forall(tele);
                        Ok(())
                    })
                })?;
                Ok(VecDeque::from([goal]))
            }
            Tactic::Clear(names) => {
                goal.enter(ctx, |ctx, g| {
                    if let Term::App(hyps) = crate::parser::Term::App(names.into_iter().map(|v| crate::parser::Term::Const(v)).collect()).capture_vars(ctx)? {
                        let hyps: HashSet<_> = hyps.into_iter().map(|h| {
                            match &*h {
                                Term::Var(i) => Ok(i.clone()),
                                Term::Const(c, _, _) => Err(crate::engine::error::Error::UnboundConst(c.clone())),
                                _ => unreachable!()
                            }
                        }).collect::<Result<_, _>>()?;
                        let n = ctx.var.len();
                        for i in 0..n {
                            if !hyps.contains(&(n - i - 1)) {
                                ctx.var[i].1.clone().free_vars(ctx).into_iter().map(|j| j + i+1).collect::<HashSet<_>>().intersection(&hyps).next().map_or(Ok(()), |j|
                                    Err(Error::InvalidGeneralization(*j, Some(i)))
                                )?;
                                ctx.var[i].2.clone().as_ref().map_or(Ok(()), |t| t.free_vars(ctx).into_iter().map(|j| j + i+1).collect::<HashSet<_>>().intersection(&hyps).next().map_or(Ok(()), |j|
                                    Err(Error::InvalidGeneralization(*j, Some(i))))
                                )?;
                            };
                        }
                        let tg = g.type_of(ctx)?;
                        tg.free_vars(ctx).intersection(&hyps).next().map_or(Ok(()), |j|
                            Err(Error::InvalidGeneralization(*j, None)))?;
                        let mut vars = ctx.var.clone().into_iter().enumerate().filter_map(|(i, h)| if hyps.contains(&(n - i - 1)) { None } else { Some(h) }).collect();
                        let newargs = (0..ctx.var.len()).filter_map(|i| if hyps.contains(&i) { None } else { Some(Term::Var(i).into()) }).rev().collect();
                        let mut hyps = hyps.into_iter().collect::<VecDeque<_>>();
                        hyps.make_contiguous().sort();
                        let tg = tg.subst(|i| {
                            // i can still appear in tg as an argument of a defined hole.
                            // This is an optimization that delays the unfolding of such holes.
                            // FIXME: Do I not risk producing ill-typed terms?
                            let hi = hyps.binary_search(&i).err().unwrap_or(0);
                            Term::Var(i - hi)
                        });
                        std::mem::swap(&mut vars, &mut ctx.var);
                        let v = ctx.get_hole_name(&g.head().clone().dest_hole()?)?;
                        let g0 = ctx.new_hole(v.clone(), Some(tg), true);
                        let newgoals = g0.collect_goals(ctx)?.into_iter().collect::<VecDeque<_>>();
                        std::mem::swap(&mut vars, &mut ctx.var);
                        let (g0, _) = g0.behead();
                        ctx.instantiate_hole(&g, g0.apps(newargs))?;
                        Ok(newgoals)
                    } else { unreachable!() }
                })
            }
            Tactic::Assumption() => {
                goal.enter(ctx, |ctx, g| {
                    let n = ctx.var.len();
                    for i in 0..n {
                        match ctx.instantiate_hole(&g, Term::Var(i)) {
                            Ok(_) => { break; }
                            _ => ()
                        };
                    }
                });
                Ok(VecDeque::new())
            }
            Tactic::Seq(tacs) => exec_seq(&tacs, ctx, goal, 0),
        }?;
        Ok(subgoals.into_iter().filter(|g| !ctx.get_hole_body(&g.goal).map_or(false, |x| x.is_some())).collect())
    }
}
