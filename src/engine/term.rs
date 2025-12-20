use crate::kernel::univ::*;
use super::context::*;
use super::error::*;
use super::typing::*;
use crate::kernel::reduction::WhdFlags;
use std::rc::Rc;
use std::collections::VecDeque;
use std::collections::HashSet;
use std::iter::Map;

/* Abstractions for local and global variable names:
 * - local variables are represented using De Bruijn indices
 * - global variables are represented using strings
 */
pub type VarType = usize;
pub type Name = String;

/* A binder is given as a variable name, its type, and its body in case of a let. */
pub type Binder = (Name, Term, Option<Term>);

/* Sequence of binders, typically used in functions and forall. */
pub type Telescope = VecDeque<Binder>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Var(VarType),
    Const(Name),
    App(VecDeque<Rc<Term>>),
    /* The Fun constructor packages the \lambda, \Pi and let constructs. Lets
     * are represented using defined binders. The boolean is true whenever the
     * constructor represents a \Pi, false when it represents a \lambda. */
    Fun(bool, Telescope, Rc<Term>),
    Type(Univ),
    Hole(VarType)
}

impl Term {
    pub fn is_atomic(&self) -> bool {
        match self {
            Term::Var(_) | Term::Const(_) | Term::Type(_) | Term::Hole(_) => true,
            _ => false
        }
    }

    pub fn fmt_atom(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_atomic() {
            write!(f, "{}", self)
        } else {
            write!(f, "({})", self)
        }
    }
}

pub fn fmt_binder(bind: &Binder, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
   let (v, t, b) = bind;
   write!(f, "({} : {}", v, t)?;
   b.as_ref().map_or(write!(f, ""), |b| { write!(f, " := {}", b) })?;
   write!(f, ")")
}

pub fn fmt_telescope<'a, T : Iterator<Item = &'a Binder>>(tele: T, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    tele.fold(Ok(()), |ok, b| {
        ok?;
        write!(f, " ")?;
        fmt_binder(b, f)
    })
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(i) => write!(f, "x_{}", i),
            Term::Const(s) => write!(f, "{}", s),
            Term::App(args) => {
                let mut it = args.iter();
                it.next().map_or(Ok(()), |t| t.fmt_atom(f))?;
                for t in it { write!(f, " ")?; t.fmt_atom(f)?; }
                Ok(())
            }
            Term::Fun(forall, tele, body) => {
                write!(f, "{}", if *forall { "forall" } else { "fun" })?;
                fmt_telescope(tele.iter(), f)?;
                write!(f, "{} {}", if *forall { "," } else { " =>" }, body)
            }
            Term::Type(u) => write!(f, "Type@({})", u),
            Term::Hole(i) => write!(f, "?{}", i),
        }
    }
}

impl Term {
    pub fn app(self, arg: Term) -> Term {
        match self {
            Term::App(mut args) => {
                args.push_back(arg.into());
                Term::App(args)
            }
            _ => Term::App(VecDeque::from([self.into(), arg.into()])),
        }
    }

    pub fn apps(self, mut args: VecDeque<Rc<Term>>) -> Term {
        if args.is_empty() { return self; }
        match self {
            Term::App(mut largs) => {
                largs.append(&mut args);
                Term::App(largs)
            }
            _ => {
                args.push_front(self.into());
                Term::App(args)
            }
        }
    }

    pub fn forall_or_fun(self, forall: bool, mut tele: Telescope) -> Term {
        if tele.len() == 0 { return self; }
        match self {
            Term::Fun(forall0, mut tele0, body) if forall0 == forall => {
                tele.append(&mut tele0);
                Term::Fun(forall, tele, body)
            }
            _ => Term::Fun(forall, tele, self.into())
        }
    }

    pub fn forall(self, tele: Telescope) -> Term {
        self.forall_or_fun(true, tele)
    }

    pub fn fun(self, tele: Telescope) -> Term {
        self.forall_or_fun(false, tele)
    }

    pub fn is_let(&self) -> bool {
        if let Term::Fun(_, tele, _) = self {
            tele.get(0).map_or(false, |(_, _, b)| b.is_some())
        } else { false }
    }

    /* Replaces self by (\lambda^k. self), avoiding capture. */
    pub fn bump(self, k: usize) -> Term {
        if k == 0 { self } else { self.subst(|i| Term::Var(i + k)) }
    }

    fn subst_aux<F>(self, f: &F, k: usize) -> Term
        where F: Fn(VarType) -> Term {
        match self {
            Term::Var(i) => if i < k { self } else { (f (i - k)).bump(k) },
            Term::App(args) => Term::App(args.iter().map(|x| (**x).clone().subst_aux(f, k).into()).collect()),
            Term::Fun(forall, tele, body) => {
                let mut k = k;
                let mut tele0 = VecDeque::new();
                for (v, ty, b) in tele {
                    tele0.push_back((v, ty.subst_aux(f, k), b.map(|b| b.subst_aux(f, k))));
                    k = k+1;
                }
                Term::Fun(forall, tele0, Rc::unwrap_or_clone(body).subst_aux(f, k).into())
            }
            _ => self
        }
    }

    //Substitutes every occurrence of `Var(i)` by `f(i)` in `self`
    pub fn subst<F>(self, f: F) -> Term
        where F: Fn(VarType) -> Term {
        self.subst_aux(&f, 0)
    }

    //Substitutes every occurrence of `Var(0)` by `t` and decrements every other variable in `self`
    pub fn subst0(self, t: &Term) -> Term {
        self.subst(|i| if i == 0 { t.clone() } else { Term::Var(i - 1) })
    }

    pub fn fold<'a, T, F : Fn(&mut Context, &Term, T) -> T>(&self, ctx: &mut Context, f: F, init: T) -> Result<T, Error> {
        let init = f(ctx, self, init);
        Ok(match self {
            Term::Var(v) => {
                let t = ctx.get_hole_body(v)?;
                let t = match t { Some(t) => t.clone(), None => Term::Var(*v) };
                f(ctx, &t, init)
            }
            Term::Const(_) | Term::Type(_) => init,
            Term::App(args) => args.iter().fold(init, |t, arg| f(ctx, &*arg, t)),
            Term::Fun(_, tele, body) =>
                ctx.fold_telescope(|ctx, (_, ty, t), x| { let x = f(ctx, ty, x); match t { None => x, Some(t) => f(ctx, t, x) } }, &mut tele.iter(), init, |ctx, x| f(ctx, &*body, x)),
            Term::Hole(h) => {
                let t = ctx.get_hole_body(h)?;
                let t = match t { Some(t) => t.clone(), None => Term::Var(*h) };
                f(ctx, &t, init)
            }
        })
    }

    pub fn free_vars(&self, ctx: &mut Context) -> HashSet<VarType> {
        fn aux(t: &Term, ctx: &mut Context, k: usize, fv: &mut HashSet<VarType>) -> () {
            match t {
                Term::Var(v) => if k <= *v { fv.insert(*v - k); },
                Term::App(args) => {
                    match t.head() {
                        Term::Hole(_) if t.may_reduce(ctx).unwrap() => {
                            let t = t.clone().whd(ctx, WhdFlags::empty()).unwrap();
                            aux(&t, ctx, k, fv)
                        }
                        _ => { for t in args { aux(t, ctx, k, fv) } }
                    } 
                }
                Term::Fun(_, tele, body) => {
                    let k = tele.iter().fold(k, |k, (_, ty, b)| {
                        aux(ty, ctx, k, fv);
                        b.as_ref().map(|b| aux(&b, ctx, k + 1, fv));
                        k + 1
                    });
                    aux(&*body, ctx, k, fv);
                }
                Term::Hole(v) => { ctx.get_hole_body(v).unwrap().clone().map(|t| aux(&t, ctx, k, fv)); },
                _ => ()
            }
        }
        let mut fv = HashSet::new();
        aux(self, ctx, 0, &mut fv);
        fv
    }

    pub fn occurs(&self, ctx: &mut Context, t : &Term) -> bool {
        self == t ||
        match self {
            Term::App(args) =>
                match self.head() {
                    Term::Hole(_) if self.may_reduce(ctx).unwrap() => 
                        self.clone().whd(ctx, WhdFlags::empty()).unwrap().occurs(ctx, t),
                    _ => !args.iter().all(|x| !x.occurs(ctx, t))
                },
            Term::Fun(_, tele, body) => !tele.iter().all(|(_, ty, b)| !(ty.occurs(ctx, t) || b.as_ref().map_or(false, |b| b.occurs(ctx, t)))) || body.occurs(ctx, t),
            Term::Hole(v) => { ctx.get_hole_body(v).unwrap().clone().map_or(false, |b| b.occurs(ctx, t)) },
            Term::Var(v) => { ctx.get_var_body(v).unwrap().clone().map_or(false, |b| b.occurs(ctx, t)) },
            _ => false
        }
    }

    // Reduces (deeply) self so that no pattern in pats occurs in self.
    pub fn eliminate_patterns(self, ctx: &mut Context, pats: &HashSet<Term>) -> Result<Term, Error> {
        if pats.contains(&self) {
            Err(Error::OccurCheck(self.clone(), self))
        } else {
            let r = match self {
                Term::Var(v) => {
                    let tv = ctx.get_var_body(&v)?.clone();
                    if tv.as_ref().map_or(false, |b| pats.iter().any(|pat| b.occurs(ctx, pat))) {
                        tv.unwrap().eliminate_patterns(ctx, pats)
                    } else { Ok(Term::Var(v)) }
                }
                Term::App(_) =>
                    match self.head() {
                        Term::Hole(_) if self.may_reduce(ctx).unwrap() => 
                            self.clone().whd(ctx, WhdFlags::empty()).unwrap().eliminate_patterns(ctx, pats),
                        _ => Ok(Term::App(self.dest_app()?.into_iter().map(|x| Rc::unwrap_or_clone(x).eliminate_patterns(ctx, pats)).collect::<Result<Vec<_>, _>>()?.into_iter().map(|x| x.into()).collect()))
                    },
                Term::Fun(forall, tele, body) => {
                    ctx.fold_telescope(|ctx, (v, t, b), tele| {
                        let mut tele = tele?;
                        let t = t.clone().eliminate_patterns(ctx, pats)?;
                        let b = b.clone().map(|b| b.eliminate_patterns(ctx, pats)).transpose()?;
                        tele.push_back((v.clone(), t, b));
                        Ok(tele)
                    }, &mut tele.iter(), Ok(VecDeque::new()), |ctx, tele|
                    Ok(Term::Fun(forall, tele?, Rc::unwrap_or_clone(body).eliminate_patterns(ctx, pats)?.into())))
                }
                Term::Hole(v) => {
                    let tv = ctx.get_hole_body(&v)?.clone();
                    if tv.as_ref().map_or(false, |b| pats.iter().any(|pat| b.occurs(ctx, pat))) {
                        tv.unwrap().eliminate_patterns(ctx, pats)
                    } else { Ok(Term::Hole(v)) }
                }
                t => Ok(t)
            };
            match r {
                Err(Error::OccurCheck(pat, t)) => {
                    // Very unoptimized, I should remember the location of the pattern.
                    let t = t.whd(ctx, WhdFlags::empty().beta().once())?;
                    t.eliminate_patterns(ctx, pats)
                }
                r => r
            }
        }
    }

    fn pp_atom<'a>(&self, ctx: &'a mut Context) -> Result<String, Error> {
        Ok(if self.is_atomic() {
            self.pp(ctx)?
        } else {
            "(".to_string() + &self.pp(ctx)? + ")"
        })
    }
    pub fn pp<'a>(&self, ctx: &'a mut Context) -> Result<String, Error> {
        Ok(match self.clone().whd(ctx, WhdFlags::empty())? {
            Term::Var(i) => ctx.get_var_name(&i)?.clone(),
            Term::Const(s) => s,
            Term::App(args) => {
                let mut it = args.into_iter();
                let mut s = it.next().unwrap().pp_atom(ctx)?;
                for t in it { s = s + " " + &t.pp_atom(ctx)?; }
                s
            }
            Term::Fun(forall, tele, body) => 
                ctx.fold_telescope(|ctx, (v, ty, b), s| {
                    Ok(s? + &(" (".to_string() + v + " : " + &ty.pp(ctx)? + &b.as_ref().map_or(Ok("".to_string()), |b| Ok(" := ".to_owned() + &b.pp(ctx)?))? + ")"))
                }, &mut tele.iter(), Ok((if forall { "forall" } else { "fun" }).to_string()), |ctx, s| {
                    Ok(s? + (if forall { ", " } else { " => " }) + &body.pp(ctx)?)
                })?,
            Term::Type(u) => "Type@(".to_string() + &u.to_string() + ")",
            Term::Hole(i) => "?".to_string() + &ctx.get_hole_name(&i)?.clone()
        })
    }

    /* [head(f a1 ... an)] returns [f] */
    pub fn head(&self) -> &Term {
        match self {
            Term::App(args) => { &*args[0] }
            t => t
        }
    }

    /* [stack(f a1 ... an)] returns [a1 ... an] */
    pub fn stack(&self) -> VecDeque<Rc<Term>> {
        match self {
            Term::App(args) => {
                let mut args = args.clone();
                args.pop_front();
                args
            }
            _ => VecDeque::new()
        }
    }

    /* [t.stack_len() = t.stack().len()] */
    pub fn stack_len(&self) -> usize {
        match self {
            Term::App(args) => { args.len() - 1}
            _ => 0
        }
    }

    /* [t.behead() = (t.head(), t.stack())] */
    pub fn behead(self) -> (Term, VecDeque<Rc<Term>>) {
        match self {
            Term::App(mut args) => {
                let t = args.pop_front().unwrap();
                (Rc::unwrap_or_clone(t), args)
            }
            t => (t, VecDeque::new())
        }
    }

    pub fn dest_var(self) -> Result<VarType, Error> {
        match self {
            Term::Var(v) => Ok(v),
            _ => Err(Error::NotAVar(self))
        }
    }

    pub fn dest_const(self) -> Result<Name, Error> {
        match self {
            Term::Const(c) => Ok(c),
            _ => Err(Error::NotAConst(self))
        }
    }

    pub fn dest_app(self) -> Result<VecDeque<Rc<Term>>, Error> {
        match self {
            Term::App(args) => Ok(args),
            _ => Err(Error::NotAnApp(self))
        }
    }


    pub fn dest_fun(self) -> Result<(Telescope, Term), Error> {
        match self {
            Term::Fun(false, tele, body) => Ok((tele, Rc::unwrap_or_clone(body))),
            _ => Err(Error::NotAFun(self))
        }
    }

    pub fn dest_forall(self) -> Result<(Telescope, Term), Error> {
        match self {
            Term::Fun(true, tele, body) => Ok((tele, Rc::unwrap_or_clone(body))),
            _ => Err(Error::NotAForall(self))
        }
    }

    /*
    pub fn dest_arity(self, ctx: &mut Context) -> Result<Telescope, Error> {
        match self.whd(ctx, WhdFlags::default())? {
            Term::Fun(true, tele, body) => {
                let (tele0, ret) = ctx.fold_telescope(|_, _, _| (), tele, (), |ctx, _| Rc::unwrap_or_clone(body).dest_arity(ctx))?;
                tele.append(tele0);
                Ok((tele, ret))
            }
            t => Ok((VecDeque::new(), t)) //TODO: return the non-reduced return type.
        }
    }*/

    pub fn dest_type(self, ctx: &mut Context) -> Result<Univ, Error> {
        match self {
            Term::Type(c) => Ok(c),
            t => {
                //TODO: generate fresh universe
                let u = Univ::exact(0);
                if unify(ctx, &Term::Type(u.clone()), &t)? { Ok(u) } else {
                    Err(Error::NotAType(t))
                }
            }
        }
    }
    
    pub fn dest_hole(self) -> Result<VarType, Error> {
        match self {
            Term::Hole(i) => Ok(i),
            _ => Err(Error::NotAHole(self))
        }
    }

    pub fn has_hole(&self, ctx: &Context) -> bool {
        match self {
            Term::Var(_) | Term::Const(_) | Term::Type(_) => false,
            Term::Hole(h) => ctx.get_hole_body(h).map_or(true, |t| t.as_ref().map_or(true, |t| t.has_hole(ctx))),
            Term::App(args) => !args.iter().all(|t| !t.has_hole(ctx)),
            Term::Fun(_, tele, body) => !tele.iter().all(|(_, t, b)| !(t.has_hole(ctx) || b.as_ref().map_or(false, |t| t.has_hole(ctx)))) || body.has_hole(ctx),
        }
    }

    pub fn to_kernel(self, ctx: &Context) -> Result<crate::kernel::term::Term, Error> {
        Ok(match self {
            Term::Var(v) => crate::kernel::term::Term::Var(v),
            Term::Const(c) => crate::kernel::term::Term::Const(c),
            Term::Type(u) => crate::kernel::term::Term::Type(u),
            Term::App(args) => crate::kernel::term::Term::App(
                args.into_iter()
                    .map(|t| Ok::<Rc<crate::kernel::term::Term>, Error>(Rc::unwrap_or_clone(t).to_kernel(ctx)?.into()))
                    .collect::<Result<_, _>>()?),
            Term::Fun(forall, tele, body) => crate::kernel::term::Term::Fun(
                forall,
                tele.into_iter()
                    .map(|(v, ty, b)| Ok::<crate::kernel::term::Binder, Error>((v, ty.to_kernel(ctx)?, b.map(|b| b.to_kernel(ctx)).transpose()?)))
                    .collect::<Result<_, Error>>()?,
                Rc::unwrap_or_clone(body).to_kernel(ctx)?.into()),
            Term::Hole(i) => ctx.get_hole_body(&i)?.clone().map_or(Err(Error::NoBody(self)), |b| b.clone().to_kernel(ctx))?
        })
    }
}

pub fn of_kernel(t: crate::kernel::term::Term) -> Term {
    match t {
        crate::kernel::term::Term::Var(v) => Term::Var(v),
        crate::kernel::term::Term::Const(c) => Term::Const(c),
        crate::kernel::term::Term::Type(u) => Term::Type(u),
        crate::kernel::term::Term::App(args) => Term::App(args.into_iter().map(|t| of_kernel(Rc::unwrap_or_clone(t)).into()).collect()),
        crate::kernel::term::Term::Fun(forall, tele, body) => Term::Fun(forall, tele.into_iter().map(|(v, ty, b)| (v, of_kernel(ty), b.map(of_kernel))).collect(), of_kernel(Rc::unwrap_or_clone(body)).into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Term::*;

    
    /*
    #[test]
    fn test_beta() {
        assert_eq!(
            App(VecDeque::from([Fun("x".to_string(), Rc::new(Type(0)), Box::new(Var("x".to_string()))), Type(1)])).beta(),
            Type(1));
        assert_eq!(
            App(VecDeque::from([Type(0), Fun("x".to_string(), Rc::new(Type(1)), Box::new(Var("x".to_string()))), Type(2)])).beta(),
            App(VecDeque::from([Type(0), Fun("x".to_string(), Rc::new(Type(1)), Box::new(Var("x".to_string()))), Type(2)])));
        assert_eq!(
            App(VecDeque::from([Fun("x".to_string(), Rc::new(Type(0)), Box::new(Var("x".to_string()))), Type(1), Type(2)])).beta(),
            App(VecDeque::from([Type(1), Type(2)])));
        assert_eq!(
            App(VecDeque::from([Fun("x".to_string(), Rc::new(Type(0)), Box::new(Var("y".to_string()))), Type(1), Type(2)])).beta(),
            App(VecDeque::from([Var("y".to_string()), Type(2)])));
    }

    #[test]
    fn test_betan() {
        assert_eq!(
            App(VecDeque::from([Fun("x".to_string(), Rc::new(Type(0)), Box::new(Var("x".to_string()))), Type(1)])).betan(),
            Type(1));
        assert_eq!(
            App(VecDeque::from([Type(0), Fun("x".to_string(), Rc::new(Type(1)), Box::new(Var("x".to_string()))), Type(2)])).betan(),
            App(VecDeque::from([Type(0), Fun("x".to_string(), Rc::new(Type(1)), Box::new(Var("x".to_string()))), Type(2)])));
        assert_eq!(
            App(VecDeque::from([Fun("x".to_string(), Rc::new(Type(0)), Box::new(Var("x".to_string()))), Type(1), Type(2)])).betan(),
            App(VecDeque::from([Type(1), Type(2)])));
        assert_eq!(
            App(VecDeque::from([Fun("x".to_string(), Rc::new(Type(0)), Box::new(Var("y".to_string()))), Type(1), Type(2)])).betan(),
            App(VecDeque::from([Var("y".to_string()), Type(2)])));
        assert_eq!(
            App(VecDeque::from([
                Fun("x".to_string(), Rc::new(Type(0)),
                    Box::new(Fun("y".to_string(), Rc::new(Type(1)),
                        Box::new(App(VecDeque::from([Var("x".to_string()), Var("y".to_string())])))))),
                Type(1), Type(2)])).betan(),
            App(VecDeque::from([Type(1), Type(2)])));
    }*/
}

