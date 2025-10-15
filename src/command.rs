use crate::parser::Term;
use crate::engine::error::*;
use crate::engine::context::*;
use crate::engine::reduction::*;
use crate::engine::typing::*;
use crate::kernel::reduction::WhdFlags;

#[derive(Debug)]
pub enum Command {
    Print(Term),
    Check(Term),
    Define(String, Option<Term>, Term),
    Whd(Term),
    Set(String, Option<String>), //Set option
    Stop()
}

impl Command {
    pub fn exec(self, ctx: &mut Context) -> () {
        //println!("exec {:?}", self);
        match self {
            Command::Print(Term::Const(c)) => {
                let t = ctx.get_const_body(&c).unwrap();
                println!("{}", t.pp(&mut ctx.clone()).unwrap());
            }
            Command::Print(_) => panic!("I can only print the body of constants."),
            Command::Check(t) => {
                let t = t.capture_vars(ctx);
                let ty = t.type_of(ctx).unwrap();
                println!("{} : {}", t.pp(ctx).unwrap(), ty.pp(ctx).unwrap());
            }
            Command::Define(v, oty, t) => {
                let t = t.capture_vars(ctx);
                let ty = t.type_of(ctx).unwrap();
                oty.map(|oty| oty.capture_vars(ctx)).map(|oty| if unify(ctx, &ty, &oty)? {
                    Ok(ctx.push_const(v, (oty, t))?)
                } else {
                    Err(Error { ctx: ctx.clone(), err: TypeError::TypeMismatch(t.clone(), oty.clone()) })
                }).transpose().unwrap();
            }
            Command::Whd(t) => {
                let t = t.capture_vars(ctx).whd(ctx, WhdFlags::default()).unwrap();
                println!("{}", t.pp(ctx).unwrap());
            }
            Command::Set(o, v) => {
                ctx.set_option(o, v.unwrap_or("".to_string()));
            }
            Command::Stop() => panic!("Stop")
        }
    }
}
