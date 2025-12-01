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
    Apply(crate::parser::Term),
    Intro(Vec<String>),
    Assumption(),
    Seq(VecDeque<Tactic>),
}

pub fn exec_seq(tacs: &VecDeque<Tactic>, ctx: &mut Context, i: usize) -> Result<VecDeque<Goal>, Error> {
    Ok(if i == tacs.len() { VecDeque::new() } else {
        tacs[i].clone().exec(ctx)?.into_iter().map(|g| {
            if let Status::Proofmode(_, _, _, goals) = &mut ctx.status {
                goals.push_front(g);
            } else { unreachable!() }
            let subgoals = exec_seq(tacs, ctx, i+1)?;
            if let Status::Proofmode(_, _, _, goals) = &mut ctx.status {
                goals.pop_front();
            } else { unreachable!() }
            Ok::<_, Error>(subgoals.into_iter())
        }).collect::<Result<VecDeque<_>, _>>()?.into_iter().rev().flatten().collect()
    })
}

impl Tactic {
    pub fn exec(self, ctx: &mut Context) -> Result<VecDeque<Goal>, Error> {
        if let Status::Proofmode(_, _, _, goals) = &mut ctx.status {
            match self {
                Tactic::Exact(t) =>
                    Ok(goals[0].enter(&mut ctx.engine, |ctx, g| {
                        let t = t.capture_vars(ctx);
                        ctx.instantiate_hole(&g, t.clone())?;
                        if t.has_hole(&ctx) {
                            Err(crate::engine::error::Error::NotGround(t.clone()))
                        } else { Ok(VecDeque::new()) }
                    })?),
                Tactic::Refine(t) => {
                    Ok(goals[0].enter(&mut ctx.engine, |ctx, g| {
                        let t = t.capture_vars(ctx);
                        let mut newgoals = t.collect_goals(ctx)?.into_iter().collect::<VecDeque<_>>();
                        newgoals.make_contiguous().sort();
                        ctx.instantiate_hole(&g, t)?;
                        Ok::<_, Error>(newgoals)
                    })?)
                }
                Tactic::Apply(t) => {
                    Ok(goals[0].enter(&mut ctx.engine, |ctx, g| {
                        let mut t = t.capture_vars(ctx);
                        let tg = g.type_of(ctx)?;
                        let mut newgoals = VecDeque::new();
                        loop {
                            let ty = t.type_of(ctx)?;
                            if crate::engine::typing::unify(ctx, &ty, &tg)? {
                                println!("refining {}\n", t.pp(ctx)?);
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
                Tactic::Intro(names) => {
                    goals[0].enter(&mut ctx.engine, |ctx, g| {
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
                    Ok(VecDeque::new())
                }
                Tactic::Assumption() => {
                    goals[0].enter(&mut ctx.engine, |ctx, g| {
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
                Tactic::Seq(tacs) => exec_seq(&tacs, ctx, 0),
            }
        } else { Err(Error::NoGoal()) }
    }
}
