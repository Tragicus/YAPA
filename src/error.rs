use crate::utils::*;
use crate::command::Context;
use crate::command::Status;

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    TypeError(crate::engine::error::Error),
    OpenGoals(),
    NoGoal(),
    InvalidCommand(),
    Stop(),
    InvalidGeneralization(VarType, Option<VarType>),
}

impl From<crate::engine::error::Error> for Error {
    fn from(value: crate::engine::error::Error) -> Error {
        Error::TypeError(value)
    }
}

impl Error {
    pub fn pp<'a>(&self, ctx: &'a mut Context) -> Result<String, Error> {
        let g = match ctx.status {
            Status::Proofmode(_, _, _, ref mut goals) if goals.len() != 0 => {
                std::mem::swap(&mut ctx.engine.var, &mut goals[0].ctx);
                Some(goals[0].clone())
            }
            _ => None
        };
        let s = g.map_or(Ok("".to_string()), |g| g.pp(&mut ctx.engine))?;
        Ok(s + "\n" + &(match self {
            Error::TypeError(e) => e.pp(&mut ctx.engine)?,
            Error::OpenGoals() => "Open goals remain.".to_string(),
            Error::NoGoal() => "No such goal.".to_string(),
            Error::InvalidCommand() => "Invalid command".to_string(),
            Error::Stop() => "Stop".to_string(),
            Error::InvalidGeneralization(i, j) => "Cannot generalize over ".to_string() + &crate::engine::term::Term::Var(*i).pp(&mut ctx.engine)? + " as it is used in " + &j.map_or(Ok("the goal".to_string()), |j| crate::engine::term::Term::Var(j).pp(&mut ctx.engine))?,
        }))
    }
}
