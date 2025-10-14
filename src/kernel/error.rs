use super::term::*;
use super::context::*;

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    UnboundVar(VarType),
    UnboundConst(Name),
    NotAVar(Term),
    NotAConst(Term),
    NotAFun(Term),
    NotAForall(Term),
    NotAType(Term),
    IllegalApplication(Term),
    TypeMismatch(Term, Term),
    IllFormed(Term),
    NoBody(Term)
}

impl TypeError {
    pub fn pp<'a>(&self, ctx: &'a mut Context) -> Result<String, Error> {
        Ok(match self {
            TypeError::UnboundVar(i) => "Variable ".to_string() + &i.to_string() + " is unbound",
            TypeError::UnboundConst(i) => "Unknown constant ".to_string() + &i,
            TypeError::NotAVar(t) => t.pp(ctx)? + " is not a variable",
            TypeError::NotAConst(t) => t.pp(ctx)? + " is not a constant",
            TypeError::NotAFun(t) => t.pp(ctx)? + " is not a function",
            TypeError::NotAForall(t) => t.pp(ctx)? + " is not a forall",
            TypeError::NotAType(t) => t.pp(ctx)? + " is not a type",
            TypeError::IllegalApplication(t) => "Illegal application in ".to_string() + &t.pp(ctx)?,
            TypeError::TypeMismatch(ty, t) => t.pp(ctx)? + " does not have type " + &ty.pp(ctx)?,
            TypeError::IllFormed(t) => t.pp(ctx)? + " is ill-formed",
            TypeError::NoBody(t) => t.pp(ctx)? + " does not have a body",
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Error {
    pub ctx: Context,
    pub err: TypeError
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ctx = self.ctx.clone();
        write!(f, "{}", self.err.pp(&mut ctx).unwrap_or_else(|e| "Error while printing typing error: ".to_string() + &e.err.pp(&mut ctx).unwrap()))
    }
}
