use super::term::*;
use super::context::*;
use super::error::*;
use super::reduction::*;
use crate::kernel::reduction::WhdFlags;
use std::iter;
use std::rc::Rc;
use std::collections::VecDeque;

// Reduction heuristic for unification.
fn unify_reduce(ctx: &mut Context, t: Term) -> Result<Term, Error> {
    t.whd(ctx, WhdFlags::empty().delta().once())?
     .whd(ctx, WhdFlags::empty().beta().zeta().eta())
}

fn unify_stacks<'a>(ctx: &'a mut Context, sk1: &VecDeque<Rc<Term>>, sk2: &VecDeque<Rc<Term>>) -> Result<bool, Error> {
    Ok(if sk1.len() != sk2.len() { false } else {
        let mut res = Ok(false);
        iter::zip(sk1.iter(), sk2.iter()).all(|(x, y)| {
            res = unify(ctx, x, y, false);
            res == Ok(true)
        })
    })
}

/* unifies t1 and t2 without reducing either. */
pub fn unify_rigid(ctx: &mut Context, t1: &Term, t2: &Term, cumul: bool) -> Result<bool, Error> {
    Ok(t1.stack_len() == t2.stack_len() && (match (t1.head(), t2.head()) {
        (Term::Var(v), Term::Var(w)) => v == w,
        // This updates the model every time we add a constraint. Maybe I should add them all at
        // once and update later, but then what is the error message?
        (Term::Const(c1, s1, u1), Term::Const(c2, s2, u2)) =>
            c1 == c2 &&
            s1.len() == s2.len() &&
            u1.len() == u2.len() && {
                for (s1, s2) in s1.iter().zip(s2.iter()) {
                    match ctx.add_sort_constraint(s1.clone(), s2.clone()) {
                        Err(Error::SortInconsistency(_, _)) => return Ok(false),
                        Err(x) => return Err(x),
                        _ => ()
                    };
                    match ctx.add_sort_constraint(s2.clone(), s1.clone()) {
                        Err(Error::SortInconsistency(_, _)) => return Ok(false),
                        Err(x) => return Err(x),
                        _ => ()
                    };
                }
                for (u1, u2) in u1.iter().zip(u2.iter()) {
                    match ctx.add_level_constraint(u1.clone(), u2.clone()) {
                        Err(Error::UnivInconsistency(_, _)) => return Ok(false),
                        Err(x) => return Err(x),
                        _ => ()
                    };
                    match ctx.add_level_constraint(u2.clone(), u1.clone()) {
                        Err(Error::UnivInconsistency(_, _)) => return Ok(false),
                        Err(x) => return Err(x),
                        _ => ()
                    };
                }
                true
            },
        (Term::Type(u1), Term::Type(u2)) => {
            match ctx.add_constraint(u1.clone(), u2.clone()) {
                Err(Error::SortInconsistency(_, _)) | Err(Error::UnivInconsistency(_, _)) => return Ok(false),
                Err(x) => return Err(x),
                _ => ()
            };
            if !cumul {
                match ctx.add_constraint(u2.clone(), u1.clone()) {
                Err(Error::SortInconsistency(_, _)) | Err(Error::UnivInconsistency(_, _)) => return Ok(false),
                Err(x) => return Err(x),
                _ => ()
                }
            };
            true
        }
        (Term::Fun(forall1, tele1, body1), Term::Fun(forall2, tele2, body2)) if forall1 == forall2 => {
            let mut tele1 = tele1.clone();
            let mut tele2 = tele2.clone();
            let (v1, ty1, b1) = tele1.pop_front().unwrap();
            let (_, ty2, b2) = tele2.pop_front().unwrap();
            unify(ctx, &ty1, &ty2, false)?
                && b1.map_or(Ok(b2.is_none()), |b1| b2.map_or(Ok(false), |b2| unify(ctx, &b1, &b2, false)))?
                && ctx.with_var((v1, ty1.clone(), None), |ctx|
                    unify(ctx, &(**body1).clone().forall_or_fun(*forall1, tele1), &(**body2).clone().forall_or_fun(*forall2, tele2), false))?
        }
        (Term::Hole(i), Term::Hole(j)) => i == j,
        (_, _) => false
    }) && unify_stacks(ctx, &t1.stack(), &t2.stack())?)
}

pub fn unify_instantiate(ctx: &mut Context, t1: &Term, t2: &Term) -> Result<bool, Error> {
    match ctx.instantiate_hole(t1, t2.clone()) {
        Ok(_) => Ok(true),
        Err(Error::HO(_)) => Ok(false),
        Err(e) => Err(e)
    }
}

// Main loop of the unification algorithm
pub fn unify_loop(ctx: &mut Context, o1: &Term, o2: &Term, cumul: bool, t1: &Term, t2: &Term) -> Result<bool, Error> {
    //println!("{} =?= {}", t1, t2);
    let ctx_commit = ctx.save();
    if unify_rigid(ctx, t1, t2, cumul)? { return Ok(true); }
    ctx.restore(ctx_commit.clone());
    if t2.may_reduce(ctx)? { let t2 = unify_reduce(ctx, t2.clone())?; return unify_loop(ctx, o1, o2, cumul, t1, &t2) };
    if t1.may_reduce(ctx)? { let t1 = unify_reduce(ctx, t1.clone())?; return unify_loop(ctx, o1, o2, cumul, &t1, t2) };
    Ok(match (t1.head(), t2.head()) {
        (Term::Hole(_), Term::Hole(_)) => {
            //TODO: save ctx
            if unify_instantiate(ctx, t2, o1)? { return Ok(true) };
            ctx.restore(ctx_commit.clone());
            if unify_instantiate(ctx, t1, o2)? { return Ok(true) };
            ctx.restore(ctx_commit);
            ctx.register_constraint(t2.clone(), t1.clone())?;
            true
        }
        (Term::Hole(_), _) => {
            if unify_instantiate(ctx, t1, o2)? { return Ok(true) };
            ctx.restore(ctx_commit);
            ctx.register_constraint(t1.clone(), t2.clone())?;
            true
        }
        (_, Term::Hole(_)) => {
            if unify_instantiate(ctx, t2, o1)? { return Ok(true) };
            ctx.restore(ctx_commit);
            ctx.register_constraint(t2.clone(), t1.clone())?;
            true
        }
        (_, _) => false
    })
}

//Unifies `t1` and `t2` in context `ctx`, using cumulativity if `cumul` is set to true.
pub fn unify(ctx: &mut Context, t1: &Term, t2: &Term, cumul: bool) -> Result<bool, Error> {
    assert!(ctx.univ.levels[0].1.len() + 1 == ctx.univ.model.len());
    let u = unify_loop(ctx, t1, t2, cumul, t1, t2);
    assert!(ctx.univ.levels[0].1.len() + 1 == ctx.univ.model.len());
    u
}

impl Term {
    pub fn type_of(&self, ctx: &mut Context) -> Result<Term, Error> {
        fn check_let(ctx: &mut Context, b : &Term, ty: &Term) -> Result<(), Error> {
            let bty = b.type_of(ctx)?;
            if unify(ctx, ty, &bty, true)? { Ok(()) } else {
            Err(Error::TypeMismatch(b.clone(), ty.clone()))}
        }
        //println!("type_of {}", self);
        assert!(ctx.univ.levels[0].1.len() + 1 == ctx.univ.model.len());
        Ok(match self {
            Term::Var(v) => ctx.get_var_type(v)?.clone(),
            Term::Const(c, s, u) => ctx.get_const_type(c)?.clone().subst_univ(&s, &u)?,
            Term::App(args) => {
                let mut args = args.iter();
                let f = args.next().unwrap();
                let ty = f.type_of(ctx);
                args.fold(ty, |ty, arg| {
                    let (mut tele, body) = ty?.whd(ctx, WhdFlags::default())?.dest_forall()?;
                    let (_, ty, _) = tele.pop_front().unwrap();
                    let argty = arg.type_of(ctx)?;
                    if unify(ctx, &ty, &argty, true)? { 
                        Ok(body.forall(tele).subst0(&**arg))
                    } else {
                        Err(Error::IllegalApplication(self.clone()))
                    }
                })?
            }
            Term::Fun(false, tele, body) => {
                ctx.fold_telescope(|ctx, (_, ty, b), _| {
                    ty.type_of(ctx)?.whd(ctx, WhdFlags::default())?.dest_type(ctx)?;
                    b.as_ref().map_or(Ok(()), |b| check_let(ctx, &b, ty))?;
                    Ok(())
                }, &mut tele.iter(), (), |ctx, _| {
                    Ok::<_, Error>((**body).clone().type_of(ctx)?.forall(tele.clone()))
                })?
            }
            Term::Fun(true, tele, body) => {
                ctx.fold_telescope(|ctx, (_, ty, b), mut univs| {
                    let u = ty.clone().type_of(ctx)?;
                    match b {
                        None => {
                            let u = u.whd(ctx, WhdFlags::default())?.dest_type(ctx)?;
                            univs.push_front(u)
                        }
                        Some(b) => check_let(ctx, &b, ty)?
                    };
                    Ok(univs)
                }, &mut tele.iter(), VecDeque::new(), |ctx, univs| {
                    let v = (**body).clone().type_of(ctx)?.whd(ctx, WhdFlags::default())?.dest_type(ctx)?;
                    Ok::<_, Error>(Term::Type(univs.into_iter().fold(v, |v, u| u.max(v))))
                })?
            }
            Term::Type(u) => Term::Type(u.clone().succ()),
            Term::Hole(v) => ctx.get_hole_type(v)?.clone()
        })
    }
}

