use super::term::*;
use super::context::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    UnboundVar(VarType),
    UnboundConst(Name),
    UnboundHole(VarType),
    NotAVar(Term),
    NotAConst(Term),
    NotAFun(Term),
    NotAForall(Term),
    NotAType(Term),
    NotAHole(Term),
    IllegalApplication(Term),
    TypeMismatch(Term, Term),
    IllFormed(Term),
    NoBody(Term),
    NotGround(Term),
    HO(Term)
}

impl Error {
    pub fn pp<'a>(&self, ctx: &'a mut Context) -> Result<String, Error> {
        Ok(match self {
            Error::UnboundVar(i) => "Variable ".to_string() + &i.to_string() + " is unbound",
            Error::UnboundConst(i) => "Unknown constant ".to_string() + &i,
            Error::UnboundHole(i) => "Hole ".to_string() + &i.to_string() + " is unbound",
            Error::NotAVar(t) => t.pp(ctx)? + " is not a variable",
            Error::NotAConst(t) => t.pp(ctx)? + " is not a constant",
            Error::NotAFun(t) => t.pp(ctx)? + " is not a function",
            Error::NotAForall(t) => t.pp(ctx)? + " is not a forall",
            Error::NotAType(t) => t.pp(ctx)? + " is not a type",
            Error::NotAHole(t) => t.pp(ctx)? + " is not a hole",
            Error::IllegalApplication(t) => "Illegal application in ".to_string() + &t.pp(ctx)?,
            Error::TypeMismatch(ty, t) => t.pp(ctx)? + " does not have type " + &ty.pp(ctx)?,
            Error::IllFormed(t) => t.pp(ctx)? + " is ill-formed",
            Error::NoBody(t) => t.pp(ctx)? + " does not have a body",
            Error::NotGround(t) => t.pp(ctx)? + " contains holes",
            Error::HO(t) => "Higher order instantiation in ".to_string() + &t.pp(ctx)?
        })
    }
}
