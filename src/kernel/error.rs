use crate::utils::*;
use crate::kernel::univ::{Sort, Univ};
use super::term::*;
use super::context::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
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
    NoBody(Term),
    UnboundSort(VarType),
    UnboundUniv(VarType),
    SortInconsistency(Sort, Sort),
    UnivInconsistency(Univ, Univ),
}

impl Error {
    pub fn pp<'a>(&self, ctx: &'a mut Context) -> Result<String, Error> {
        Ok(match self {
            Error::UnboundVar(i) => "Variable ".to_string() + &i.to_string() + " is unbound",
            Error::UnboundConst(i) => "Unknown constant ".to_string() + &i,
            Error::NotAVar(t) => t.pp(ctx)? + " is not a variable",
            Error::NotAConst(t) => t.pp(ctx)? + " is not a constant",
            Error::NotAFun(t) => t.pp(ctx)? + " is not a function",
            Error::NotAForall(t) => t.pp(ctx)? + " is not a forall",
            Error::NotAType(t) => t.pp(ctx)? + " is not a type",
            Error::IllegalApplication(t) => "Illegal application in ".to_string() + &t.pp(ctx)?,
            Error::TypeMismatch(ty, t) => t.pp(ctx)? + " does not have type " + &ty.pp(ctx)?,
            Error::IllFormed(t) => t.pp(ctx)? + " is ill-formed",
            Error::NoBody(t) => t.pp(ctx)? + " does not have a body",
            Error::UnboundSort(i) => "Sort s_".to_string() + &i.to_string() + " is unbound",
            Error::UnboundUniv(i) => "Universe u_".to_string() + &i.to_string() + " is unbound",
            Error::SortInconsistency(s1, s2) => "Cannot have ".to_string() + &s1.to_string() + " < " + &s2.to_string(),
            Error::UnivInconsistency(u1, u2) => "Cannot have ".to_string() + &u1.to_string() + " <= " + &u2.to_string(),
        })
    }
}
