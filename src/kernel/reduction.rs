use super::term::*;
use super::context::*;
use super::error::*;
use std::rc::Rc;
use std::collections::VecDeque;

#[derive(Debug, Clone, PartialEq)]
pub struct WhdFlags {
    pub beta : bool,
    pub delta : bool,
    pub eta : bool,
    pub zeta : bool,
    pub once : bool,
}

impl WhdFlags {
    pub fn default() -> Self {
        WhdFlags {
            beta: true,
            delta: true,
            eta: true,
            zeta: true,
            once: false
        }
    }

    pub fn empty() -> Self {
        WhdFlags {
            beta: false,
            delta: false,
            eta: false,
            zeta: false,
            once: false
        }
    }

    pub fn beta(mut self) -> Self {
        self.beta = true;
        self
    }

    pub fn nobeta(mut self) -> Self {
        self.beta = false;
        self
    }

    pub fn delta(mut self) -> Self {
        self.delta = true;
        self
    }

    pub fn nodelta(mut self) -> Self {
        self.delta = false;
        self
    }

    pub fn eta(mut self) -> Self {
        self.eta = true;
        self
    }

    pub fn noeta(mut self) -> Self {
        self.eta = false;
        self
    }

    pub fn zeta(mut self) -> Self {
        self.zeta = true;
        self
    }

    pub fn nozeta(mut self) -> Self {
        self.zeta = false;
        self
    }

    pub fn once(mut self) -> Self {
        self.once = true;
        self
    }

    pub fn full(mut self) -> Self {
        self.once = false;
        self
    }

    pub fn set_once(mut self, b: bool) -> Self {
        self.once = b;
        self
    }
}

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
                    let hd = ctx.get_const_body(c)?.clone();
                    let (hd, args) = hd.apps(args).behead();
                    let (_, hd, args) = if flags.once { (true, hd, args) } else { aux(hd, args, ctx, flags)? };
                    (true, hd, args)
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
        Ok(match self.clone().whd(ctx, WhdFlags::empty())?.head() {
            Term::Type(_) => false,
            Term::Fun(_, _, _) => 1 < self.stack_len() || self.is_let(),
            Term::Var(v) => {
                match ctx.get_var_body(&v) {
                    Err(Error::NoBody(_)) => false,
                    Err(e) => Err(e)?,
                    Ok(b) => b.is_some()
                }
            }
            Term::Const(_) => true,
            Term::App(_) => unreachable!()
        })
    }
}
