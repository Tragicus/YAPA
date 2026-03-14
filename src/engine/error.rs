use crate::utils::*;
use crate::kernel::univ::{Sort, Univ};
use super::term::*;
use super::context::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    UnboundVar(VarType),
    UnboundConst(Name),
    UnboundHole(VarType),
    NotAVar(Term),
    NotAConst(Term),
    NotAnApp(Term),
    NotAFun(Term),
    NotAForall(Term),
    NotAType(Term),
    NotAHole(Term),
    IllegalApplication(Term),
    TypeMismatch(Term, Term),
    IllFormed(Term),
    NoBody(Term),
    NotGround(Term),
    UnboundSort(VarType),
    UnboundUniv(VarType),
    SortInconsistency(Sort, Sort),
    UnivInconsistency(Univ, Univ),
    PrintingError(std::fmt::Error),

    HO(Term),
    OccurCheck(Term, Term),
}

impl Error {
    pub fn pp<'a>(&self, ctx: &'a mut Context) -> Result<String, Error> {
        Ok(match self {
            Error::UnboundVar(i) => "Variable ".to_string() + &i.to_string() + " is unbound",
            Error::UnboundConst(i) => "Unknown constant ".to_string() + &i,
            Error::UnboundHole(i) => "Hole ".to_string() + &i.to_string() + " is unbound",
            Error::NotAVar(t) => t.pp(ctx)? + " is not a variable",
            Error::NotAConst(t) => t.pp(ctx)? + " is not a constant",
            Error::NotAnApp(t) => t.pp(ctx)? + " is not an application",
            Error::NotAFun(t) => t.pp(ctx)? + " is not a function",
            Error::NotAForall(t) => t.pp(ctx)? + " is not a forall",
            Error::NotAType(t) => t.pp(ctx)? + " is not a type",
            Error::NotAHole(t) => t.pp(ctx)? + " is not a hole",
            Error::IllegalApplication(t) => "Illegal application in ".to_string() + &t.pp(ctx)?,
            Error::TypeMismatch(ty, t) => t.pp(ctx)? + " does not have type " + &ty.pp(ctx)?,
            Error::IllFormed(t) => t.pp(ctx)? + " is ill-formed",
            Error::NoBody(t) => t.pp(ctx)? + " does not have a body",
            Error::UnboundSort(i) => "Sort s_".to_string() + &i.to_string() + " is unbound",
            Error::UnboundUniv(i) => "Universe u_".to_string() + &i.to_string() + " is unbound",
            Error::SortInconsistency(s1, s2) => "Cannot have ".to_string() + &s1.to_string() + " < " + &s2.to_string(),
            Error::UnivInconsistency(u1, u2) => "Cannot have ".to_string() + &u1.to_string() + " <= " + &u2.to_string(),
            Error::PrintingError(pp) => pp.to_string(),
            Error::NotGround(t) => t.pp(ctx)? + " contains holes",
            Error::HO(t) => "Higher order instantiation in ".to_string() + &t.pp(ctx)?,
            Error::OccurCheck(pat, t) => "Pattern ".to_string() + &pat.pp(ctx)? + " occurs in " + &t.pp(ctx)?
        })
    }
}

impl From<crate::kernel::error::Error> for Error {
    fn from(value: crate::kernel::error::Error) -> Error {
        match value {
            crate::kernel::error::Error::UnboundVar(v) => Error::UnboundVar(v),
            crate::kernel::error::Error::UnboundConst(n) => Error::UnboundConst(n),
            crate::kernel::error::Error::NotAVar(t) => Error::NotAVar(t.into()),
            crate::kernel::error::Error::NotAConst(t) => Error::NotAConst(t.into()),
            crate::kernel::error::Error::NotAFun(t) => Error::NotAFun(t.into()),
            crate::kernel::error::Error::NotAForall(t) => Error::NotAForall(t.into()),
            crate::kernel::error::Error::NotAType(t) => Error::NotAType(t.into()),
            crate::kernel::error::Error::IllegalApplication(t) => Error::IllegalApplication(t.into()),
            crate::kernel::error::Error::TypeMismatch(t1, t2) => Error::TypeMismatch(t1.into(), t2.into()),
            crate::kernel::error::Error::IllFormed(t) => Error::IllFormed(t.into()),
            crate::kernel::error::Error::NoBody(t) => Error::NoBody(t.into()),
            crate::kernel::error::Error::UnboundSort(v) => Error::UnboundSort(v),
            crate::kernel::error::Error::UnboundUniv(v) => Error::UnboundUniv(v),
            crate::kernel::error::Error::SortInconsistency(s1, s2) => Error::SortInconsistency(s1, s2),
            crate::kernel::error::Error::UnivInconsistency(u1, u2) => Error::UnivInconsistency(u1, u2),
            crate::kernel::error::Error::PrintingError(e) => Error::PrintingError(e)
        }
    }
}
