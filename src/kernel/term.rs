use super::univ::*;
use super::context::*;
use super::error::*;
use std::rc::Rc;
use std::collections::VecDeque;
use std::collections::HashSet;

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
}

impl Term {
    fn is_atomic(&self) -> bool {
        match self {
            Term::Var(_) | Term::Const(_) | Term::Type(_) => true,
            _ => false
        }
    }

    fn fmt_atom(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_atomic() {
            write!(f, "{}", self)
        } else {
            write!(f, "({})", self)
        }
    }

    fn fmt_telescope(tele: &Telescope, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        Ok(for (v, t, b) in tele.iter() {
            match b {
                None => write!(f, " ({} : {})", v, t)?,
                Some(b) => write!(f, " ({} : {} := {})", v, t, b)?
            };
        })
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(i) => write!(f, "x_{}", i),
            Term::Const(s) => write!(f, "{}", s),
            Term::App(args) => {
                let mut it = args.iter();
                it.next().map_or(Ok(()), |t| t.fmt_atom(f))?;
                for t in it { t.fmt_atom(f)?; }
                Ok(())
            }
            Term::Fun(forall, tele, body) => {
                write!(f, "{}", if *forall { "forall" } else { "fun" })?;
                Term::fmt_telescope(tele, f)?;
                write!(f, "{} {}", if *forall { "," } else { " =>" }, body)
            }
            Term::Type(u) => write!(f, "Type@({})", u)
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

    pub fn free_vars(&self) -> HashSet<VarType> {
        fn aux(t: &Term, k: usize, fv: &mut HashSet<VarType>) -> () {
            match t {
                Term::Var(v) => if k <= *v { fv.insert(*v - k); },
                Term::App(args) => for t in args { aux(t, k, fv) },
                Term::Fun(_, tele, body) => {
                    let k = tele.iter().fold(k, |k, (_, ty, b)| {
                        aux(ty, k, fv);
                        b.as_ref().map(|b| aux(&b, k + 1, fv));
                        k + 1
                    });
                    aux(&*body, k, fv);
                }
                _ => ()
            }
        }
        let mut fv = HashSet::new();
        aux(self, 0, &mut fv);
        fv
    }

    pub fn occurs(&self, t : &Term) -> bool {
        self == t ||
        match self {
            Term::App(args) => !args.iter().all(|x| !x.occurs(t)),
            Term::Fun(_, tele, body) => !tele.iter().all(|(_, ty, b)| !(ty.occurs(t) || b.as_ref().map_or(false, |b| b.occurs(t)))) || body.occurs(t),
            _ => false
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
        Ok(match self {
            Term::Var(i) => ctx.get_var_name(i)?.clone(),
            Term::Const(s) => s.clone(),
            Term::App(args) => {
                let mut it = args.iter();
                let mut s = it.next().unwrap().pp_atom(ctx)?;
                for t in it { s = s + " " + &t.pp_atom(ctx)?; }
                s
            }
            Term::Fun(forall, tele, body) => 
                ctx.fold_telescope(|ctx, (v, ty, b), s| {
                    Ok(s? + &(" (".to_string() + v + " : " + &ty.pp(ctx)? + &b.as_ref().map_or(Ok("".to_string()), |b| Ok(" := ".to_owned() + &b.pp(ctx)?))? + ")"))
                }, &mut tele.iter(), Ok((if *forall { "forall" } else { "fun" }).to_string()), |ctx, s| {
                    Ok(s? + (if *forall { ", " } else { " => " }) + &body.pp(ctx)?)
                })?,
            Term::Type(u) => "Type@(".to_string() + &u.to_string() + ")",
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

    pub fn dest_type(self) -> Result<Univ, Error> {
        match self {
            Term::Type(c) => Ok(c),
            _ => Err(Error::NotAType(self))
        }
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

