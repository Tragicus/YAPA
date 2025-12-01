use super::term::*;
use super::context::*;
use super::error::*;
use crate::kernel::reduction::WhdFlags;
use std::rc::Rc;
use std::collections::VecDeque;

impl Term {
    /* TOTHINK: Should I check or assert that self and args take the right form? */
    pub fn beta(self, mut args: VecDeque<Rc<Term>>) -> (bool, Term, VecDeque<Rc<Term>>) {
        if args.len() == 0 || self.is_let() { return (false, self, args) };
        if let Term::Fun(false, mut tele, body) = self {
            let arg = (*args.pop_front().unwrap()).clone();
            tele.pop_front();
            let (hd, mut args0) = Rc::unwrap_or_clone(body).fun(tele).subst0(&arg).behead();
            let args = if args0.len() == 0 { args } else { args0.append(&mut args); args0 };
            (true, hd, args)
        } else { (false, self, args) }
    }

    /* TOTHINK: Should I check or assert that self takes the right form? */
    pub fn eta(self) -> (bool, Term) {
        if self.is_let() { return (false, self) };
        if let Term::Fun(false, tele, body) = self {
            if tele.len() != 1 { (false, Term::Fun(false, tele, body)) } else {
            let body = Rc::unwrap_or_clone(body);
            if let Term::App(mut args) = body {
                let v = args.pop_back().unwrap();
                if let Term::Var(w) = &*v {
                    if *w == 0 {
                        if args.len() == 1 { (true, Rc::unwrap_or_clone(args.pop_front().unwrap())) } else { (false, Term::App(args)) }
                    } else { args.push_back(v); (false, Term::App(args).fun(tele)) }
                } else { args.push_back(v); (false, Term::App(args).fun(tele)) }
            } else { (false, Term::Fun(false, tele, body.into())) }}
        } else { (false, self) }
    }

    // Weak head reduction
    // N.B. Replacing a hole by its value from the context does not count as a reduction step. In
    // particular, whd(_, WhdFlags::empty()) replaces an evar by its definition
    pub fn whd(self, ctx: &mut Context, flags: WhdFlags) -> Result<Term, Error> {
        fn aux(hd: Term, mut args: VecDeque<Rc<Term>>, ctx: &mut Context, flags: &WhdFlags) -> Result<(bool, Term, VecDeque<Rc<Term>>), Error> {
            //println!("whd {:?}", hd.clone().apps(args.clone()));
            let (progress, hd, args) = match hd {
                Term::Var(v) if flags.delta => {
                    match ctx.get_var_body(&v)?.clone() {
                        None => (false, Term::Var(v), args),
                        Some(t) => {
                            let (t, args) = t.apps(args).behead();
                            if flags.once { (true, t, args) } else { aux(t, args, ctx, flags)? }
                        }
                    }
                }
                Term::Const(ref c) if flags.delta => {
                    match ctx.get_const_body(c)?.map(|hd| hd.clone()) {
                        None => (false, hd, args),
                        Some(hd) => {
                            let (hd, args) = hd.apps(args).behead();
                            let (_, hd, args) = if flags.once { (true, hd, args) } else { aux(hd, args, ctx, flags)? };
                            (true, hd, args)
                        }
                    }
                }
                Term::Fun(forall, mut tele, body) if flags.zeta && hd.is_let() => {
                    let (_, _, b) = tele.pop_front().unwrap();
                    let b = b.unwrap();
                    let hd = Rc::unwrap_or_clone(body).forall_or_fun(forall, tele).subst0(&b);
                    let (_, hd, args) = if flags.once { (true, hd, args) } else { aux(hd, args, ctx, flags)? };
                    (true, hd, args)
                }
                Term::Fun(false, ref tele, _) if flags.eta && tele.len() == 1 && !hd.is_let() => {
                    let (progress, hd) = hd.eta();
                    let (hd, mut args0) = hd.behead();
                    args0.append(&mut args);
                    let (progress0, hd, args0) = if flags.once || !progress { (progress, hd, args0) } else { aux(hd, args0, ctx, flags)? };
                    (progress || progress0, hd, args0)
                }
                Term::Fun(false, mut tele, body) if flags.eta && !hd.is_let() => {
                    let (v, ty, b) = tele.pop_front().unwrap();
                    let (progress, hd, args0) = ctx.with_var((v.clone(), ty.clone(), None), |ctx|
                        aux(Term::Fun(false, tele, body), VecDeque::new(), ctx, &WhdFlags::empty().eta().set_once(flags.once)))?;
                    let hd = hd.apps(args0).fun(VecDeque::from([(v, ty, b)]));
                    let (progress0, hd, args) = if flags.once || !progress { (progress, hd, args) } else { aux(hd, args, ctx, flags)? };
                    (progress || progress0, hd, args)
                }
                Term::Hole(i) => {
                    match ctx.get_hole_body(&i)?.clone() {
                        None => (false, Term::Hole(i), args),
                        Some(t) => {
                            let (t, args) = t.apps(args).behead();
                            let (_, t, args) = aux(t, args, ctx, &WhdFlags::empty().beta())?;
                            aux(t, args, ctx, flags)?
                        }
                    }
                }
                hd => (false, hd, args)
            };
            Ok(if !flags.beta || (progress && flags.once) { (progress, hd, args) } else {
                let (progress0, hd, args) = hd.beta(args);
                let progress = progress || progress0;
                let (progress0, hd, args) = if flags.once || !progress { (progress, hd, args) } else { aux(hd, args, ctx, flags)? };
                (progress || progress0, hd, args)
            })
        }
        let (hd, args) = self.behead();
        aux(hd, args, ctx, &flags).map(|(_, hd, args)| hd.apps(args))
    }

    /* [!t.may_reduce(ctx)] implies [t.whd(ctx, WhdFlags.default()) == t] */
    pub fn may_reduce(&self, ctx: &mut Context) -> Result<bool, Error> {
        Ok(match self.head() {
            Term::Type(_) => false,
            Term::Fun(_, _, _) => self.stack_len() != 0 || self.is_let(),
            Term::Var(v) => {
                match ctx.get_var_body(&v) {
                    Err(Error::NoBody(_)) => false,
                    Err(e) => Err(e)?,
                    Ok(b) => b.is_some()
                }
            }
            Term::Const(c) => ctx.get_const_body(c)?.is_some(),
            Term::Hole(h) => ctx.get_hole_body(h)?.is_some(),
            Term::App(_) => unreachable!()
        })
    }
}
