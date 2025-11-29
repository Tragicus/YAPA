use crate::parser::Term;
use crate::engine::error::*;
use crate::engine;
use crate::engine::reduction::*;
use crate::engine::typing::*;
use crate::kernel::reduction::WhdFlags;
use crate::tactic::*;
use std::collections::VecDeque;

#[derive(Clone, Debug, PartialEq)]
pub enum Status {
    Idle(),
    Proofmode(String, engine::term::Term, engine::term::Term, VecDeque<Goal>)
}

#[derive(Clone, Debug)]
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
    pub fn exec(self, ctx: &mut Context) -> () {
        println!("exec {:?}", self);
        match self {
            Command::Print(Term::Const(c)) => {
                let t = ctx.engine.get_const_body(&c).unwrap().expect("Constant has no body");
                println!("{}", t.pp(&mut ctx.engine).unwrap());
            }
            Command::Print(_) => panic!("I can only print the body of constants."),
            Command::Check(t) => {
                let t = t.capture_vars(&mut ctx.engine);
                let ty = t.type_of(&mut ctx.engine).unwrap();
                println!("{} : {}", t.pp(&mut ctx.engine).unwrap(), ty.pp(&mut ctx.engine).unwrap());
            }
            Command::Define(_, _, _) if ctx.status != Status::Idle() => panic!("Cannot define constant during proof."),
            Command::Define(v, oty, t) => {
                let oty = oty.capture_vars(&mut ctx.engine);
                let t = t.capture_vars(&mut ctx.engine);
                let ty = t.type_of(&mut ctx.engine).unwrap();
                let ty = if let Ok(true) = unify(&mut ctx.engine, &ty, &oty) {
                    oty
                } else {
                    Err(Error { ctx: ctx.engine.clone(), err: TypeError::TypeMismatch(t.clone(), oty.clone()) }).unwrap()
                };
                if t.has_hole(&ctx.engine) {
                    let goals = t.collect_goals(&mut ctx.engine).unwrap().into_iter().collect();
                    ctx.status = Status::Proofmode(v, ty, t, goals)
                } else {
                    ctx.engine.push_const(v, (ty, Some(t))).unwrap();
                    ctx.engine.reset_holes();
                }
            }
            Command::Tac(tac) => tac.exec(ctx),
            Command::Qed(transparent) => {
                if let Status::Proofmode(v, ty, t, goals) = &ctx.status {
                    if goals.len() != 0 { panic!("Cannot conclude, open goals remain.") };
                    let ty0 = t.type_of(&mut ctx.engine).unwrap();
                    if unify(&mut ctx.engine, &ty, &ty0).unwrap() {
                        ctx.engine.push_const(v.clone(), (ty.clone(), if transparent { Some(t.clone()) } else { None })).unwrap();
                    } else {
                        Err(Error { ctx: ctx.engine.clone(), err: TypeError::TypeMismatch(t.clone(), ty.clone()) }).unwrap()
                    }
                } else { 
                    panic!("Cannot conclude without a proof.")
                }
                ctx.status = Status::Idle();
            }
            Command::Whd(t) => {
                let t = t.capture_vars(&mut ctx.engine).whd(&mut ctx.engine, WhdFlags::default()).unwrap();
                println!("{}", t.pp(&mut ctx.engine).unwrap());
            }
            Command::Set(o, v) => {
                ctx.engine.set_option(o, v.unwrap_or("".to_string()));
            }
            Command::Skip() => (),
            Command::Stop() => panic!("Stop")
        }
    }
}
