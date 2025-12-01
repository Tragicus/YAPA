use crate::parser::Term;
use crate::engine;
use crate::engine::reduction::*;
use crate::engine::typing::*;
use crate::kernel::reduction::WhdFlags;
use crate::goal::Goal;
use crate::tactic::*;
use crate::error::*;
use std::collections::VecDeque;

#[derive(Clone, Debug, PartialEq)]
pub enum Status {
    Idle(),
    Proofmode(String, engine::term::Term, engine::term::Term, VecDeque<Goal>)
}

#[derive(Clone, Debug, PartialEq)]
pub struct Context {
    pub engine: engine::context::Context,
    pub status: Status
}

impl Context {
    pub fn new() -> Self {
        Context { engine: engine::context::Context::new(), status: Status::Idle() }
    }
}

#[derive(Debug)]
pub enum Command {
    Print(Term),
    Check(Term),
    Define(String, Term, Term),
    Tac(Tactic),
    Qed(bool),
    Whd(Term),
    Set(String, Option<String>), //Set option
    Skip(),
    Stop()
}

impl Command {
    pub fn exec(self, ctx: &mut Context) -> Result<(), Error> {
        println!("exec {:?}", self);
        match self {
            Command::Print(Term::Const(c)) => {
                let t = ctx.engine.get_const_body(&c)?.ok_or(crate::engine::error::Error::NoBody(crate::engine::term::Term::Const(c)))?;
                println!("{}", t.pp(&mut ctx.engine)?);
                Ok(())
            }
            Command::Print(_) => Err(crate::engine::error::Error::NoBody(crate::engine::term::Term::Const("_".to_string())))?,
            Command::Check(t) => {
                let t = t.capture_vars(&mut ctx.engine);
                let ty = t.type_of(&mut ctx.engine)?;
                println!("{} : {}", t.pp(&mut ctx.engine)?, ty.pp(&mut ctx.engine)?);
                Ok(())
            }
            Command::Define(_, _, _) if ctx.status != Status::Idle() => Err(Error::OpenGoals()),
            Command::Define(v, oty, t) => {
                let oty = oty.capture_vars(&mut ctx.engine);
                oty.type_of(&mut ctx.engine)?.dest_type(&mut ctx.engine)?;
                let t = t.capture_vars(&mut ctx.engine);
                let ty = t.type_of(&mut ctx.engine)?;
                let ty = if let Ok(true) = unify(&mut ctx.engine, &ty, &oty) {
                    oty
                } else {
                    Err(crate::engine::error::Error::TypeMismatch(t.clone(), oty.clone()))?
                };
                if t.has_hole(&ctx.engine) {
                    let mut goals : VecDeque<_> = t.collect_goals(&mut ctx.engine)?.into_iter().collect();
                    goals.make_contiguous().sort();
                    ctx.status = Status::Proofmode(v, ty, t, goals)
                } else {
                    ctx.engine.push_const(v, (ty, Some(t)))?;
                    ctx.engine.reset_holes();
                }
                Ok(())
            }
            Command::Tac(tac) => {
                tac.exec(ctx)?;
                let Status::Proofmode(_, _, _, ref mut goals) = ctx.status else { unreachable!() };
                let mut fgoals : VecDeque<_> = goals.into_iter().filter(|g| ctx.engine.get_hole_body(&g.goal).unwrap().is_none()).map(|g| g.clone()).collect();
                std::mem::swap(goals, &mut fgoals);
                Ok(())
            }
            Command::Qed(transparent) => {
                if let Status::Proofmode(v, ty, t, goals) = &ctx.status {
                    if goals.len() != 0 { Err(Error::OpenGoals())? };
                    let ty0 = t.type_of(&mut ctx.engine)?;
                    if unify(&mut ctx.engine, &ty, &ty0)? {
                        ctx.engine.push_const(v.clone(), (ty.clone(), if transparent { Some(t.clone()) } else { None }))?;
                    } else {
                        Err(crate::engine::error::Error::TypeMismatch(t.clone(), ty.clone()))?
                    }
                } else { 
                    Err(Error::InvalidCommand())?
                }
                ctx.status = Status::Idle();
                Ok(())
            }
            Command::Whd(t) => {
                let t = t.capture_vars(&mut ctx.engine).whd(&mut ctx.engine, WhdFlags::default())?;
                println!("{}", t.pp(&mut ctx.engine)?);
                Ok(())
            }
            Command::Set(o, v) => {
                ctx.engine.set_option(o, v.unwrap_or("".to_string()));
                Ok(())
            }
            Command::Skip() => Ok(()),
            Command::Stop() => Err(Error::Stop())
        }
    }
}
