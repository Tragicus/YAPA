use crate::kernel::univ::*;
use super::term::*;
use super::error::*;
use super::reduction::*;
use super::typing::*;
use crate::kernel::reduction::WhdFlags;
use std::rc::Rc;
use std::collections::VecDeque;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub struct HoleContext {
    pub name: Name,
    pub ty: Term,
    pub body: Option<Term>,
    pub cstr: Vec<(VecDeque<Rc<Term>>, Term)>
}

#[derive(Debug, Clone, PartialEq)]
pub enum Commit {
    PushHole(),
    ReinstantiateHole(VarType, Term),
    PushHoleConstraint(VarType)
}

#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    // local variables
    pub var: Telescope,

    // global variables
    pub cst: HashMap<Name, (crate::kernel::term::Term, Option<crate::kernel::term::Term>)>,

    // holes and unification constraints
    pub hole: Vec<HoleContext>,

    // history of movements of holes, so that we can reset without copy.
    pub commits: Vec<Commit>,

    pub options: HashMap<String, Vec<String>>,

    // Graph with an arc from v to w if v *-reduces to w when applied to enough arguments. Its
    // label tells the minimum number of beta-reductions needed to go from v to w.
    //pub reds: Graph<(Name, usize), usize>,

    // Graph with an arc from u to v if u <= v. The label of the arc tells if the inequality is
    // strict
    //pub universes: Graph<(), bool>,
}

impl std::fmt::Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ctx(vars:")?;
        fmt_telescope(self.var.iter(), f)?;
        write!(f, "\n holes:")?;
        self.hole.iter().fold(write!(f, ""), |ok, h| {
            let ok = ok?;
            write!(f, "({} : {}", h.name, h.ty)?;
            h.body.as_ref().map_or(Ok(ok), |b| { write!(f, " := {}", b) })?;
            write!(f, ")")
        })
    }
}

impl Context {
    pub fn new() -> Self {
     Context {
            var: VecDeque::new(),
            cst: HashMap::new(),
            hole: Vec::new(),
            commits: Vec::new(),
            options: HashMap::new(),
            //reds: Graph::new(),
            //universes: Graph::new(),
        }
    }

    pub fn find_var(&self, v: &VarType) -> Result<&(Name, Term, Option<Term>), Error> {
        self.var.get(self.var.len() - *v - 1).map_or(Err(Error { ctx: self.clone(), err: TypeError::UnboundVar(v.clone()) }), |x| Ok(x))
    }

    pub fn find_const(&self, v: &Name) -> Result<&(crate::kernel::term::Term, Option<crate::kernel::term::Term>), Error> {
        self.cst.get(v).ok_or(Error { ctx: self.clone(), err: TypeError::UnboundConst(v.clone()) })
    }

    pub fn find_hole(&self, v: &VarType) -> Result<&HoleContext, Error> {
        self.hole.get(*v).map_or(Err(Error { ctx: self.clone(), err: TypeError::UnboundHole(v.clone()) }), |x| Ok(x))
    }

    pub fn get_var_name(&self, v: &VarType) -> Result<&Name, Error> {
        let (s, _, _) = self.find_var(v)?;
        Ok(s)
    }

    pub fn get_var_type(&self, v: &VarType) -> Result<Term, Error> {
        let (_, t, _) = self.find_var(v)?;
        Ok(t.clone().bump(v + 1))
    }

    pub fn get_var_body(&self, v: &VarType) -> Result<Option<Term>, Error> {
        let (_, _, t) = self.find_var(v)?;
        Ok(t.clone().map(|t| t.bump(v + 1)))
    }

    pub fn get_const_type(&self, v: &Name) -> Result<Term, Error> {
        let (t, _) = self.find_const(v)?;
        Ok(of_kernel(t.clone()))
    }

    pub fn get_const_body(&self, v: &Name) -> Result<Option<Term>, Error> {
        let (_, t) = self.find_const(v)?;
        Ok(t.as_ref().map(|t| of_kernel(t.clone())))
    }

    pub fn get_hole_name(&self, v: &VarType) -> Result<&Name, Error> {
        Ok(&self.find_hole(v)?.name)
    }

    pub fn get_hole_type(&self, v: &VarType) -> Result<&Term, Error> {
        Ok(&self.find_hole(v)?.ty)
    }

    pub fn get_hole_body(&self, v: &VarType) -> Result<&Option<Term>, Error> {
        Ok(&self.find_hole(v)?.body)
    }

    pub fn get_hole_constraints(&self, v: &VarType) -> Result<&Vec<(VecDeque<Rc<Term>>, Term)>, Error> {
        Ok(&self.find_hole(v)?.cstr)
    }

    pub fn get_option(&self, v : &String) -> Option<&String> {
        self.options.get(v).map(|opts| opts.get(opts.len() - 1)).flatten()
    }

    pub fn push_var(&mut self, t: (Name, Term, Option<Term>)) -> &mut Self {
        self.var.push_back(t);
        self
    }

    pub fn push_const(&mut self, c: Name, t: (Term, Option<Term>)) -> Result<&mut Self, Error> {
        let (ty, t) = t;
        self.cst.insert(c, (ty.to_kernel(self)?, t.map_or(Ok(None), |t| Ok(Some(t.to_kernel(self)?)))?));
        Ok(self)
    }

    pub fn new_hole(&mut self, v: Name, ty: Option<Term>, with_ctx: bool) -> Term {
        let mut args = VecDeque::new();
        if with_ctx {
            self.var.iter().fold(self.var.len(), |i, (_, _, b)| {
                let i = i - 1;
                if b.is_none() { args.push_back(Term::Var(i).into()) };
                i
            });
        };
        let mut ty = ty.unwrap_or_else(|| {
            let t = Term::Hole(self.hole.len()).apps(args.clone());
            let mut ty = Term::Type(Univ::exact(0));
            if with_ctx { ty = ty.forall(self.var.clone().into_iter().collect()) };
            self.hole.push(HoleContext { name: v.clone() + "_ty", ty: ty, body: None, cstr: Vec::new() });
            self.commits.push(Commit::PushHole());
            t
        });
        if with_ctx { ty = ty.forall(self.var.clone().into_iter().collect()) };
        let t = Term::Hole(self.hole.len()).apps(args);
        self.hole.push(HoleContext { name: v, ty: ty, body: None, cstr: Vec::new() });
        self.commits.push(Commit::PushHole());
        t
    }

    pub fn instantiate_hole(&mut self, tv: &Term, t: Term) -> Result<&mut Self, Error> {
        //println!("instantiate_hole {:?} <- {:?}", tv, t);
        let tvty = tv.type_of(self)?;
        let ty = t.type_of(self)?;
        if !unify(self, &tvty, &ty)? { return Err(Error { ctx: self.clone(), err: TypeError::TypeMismatch(tvty, t) }) };
        let (v, args) = tv.clone().behead();
        let v = v.dest_hole()?;
        let nargs = args.len();
        let (_, map) = args.iter().fold(Ok((1, HashMap::new())), |m, arg| {
            let (i, mut map) = m?;
            let v = Rc::unwrap_or_clone(arg.clone()).whd(self, WhdFlags::default())?.dest_var().map_err(|_| Error { ctx: self.clone(), err: TypeError::HO(tv.clone()) })?;
            map.insert(v, if map.contains_key(&v) { None } else { Some(Term::Var(nargs - i)) });
            Ok((i + 1, map))
        })?;
        if t.free_vars().iter().all(|v| map.get(v).map(|v| v.clone()).flatten().is_some()) {
            //TODO: Am I sure that I get at least nargs binders?
            let mut tele = if nargs == 0 { VecDeque::new() } else { let (tele, _) = self.get_hole_type(&v)?.clone().dest_forall()?; tele };
            tele.truncate(nargs);
            let h = self.hole.get_mut(v).expect("Anomaly: hole should exist.");
            h.body.as_ref().map(|tv| self.commits.push(Commit::ReinstantiateHole(v, tv.clone())));
            h.body = Some(t.subst(|v| map.get(&v).map(|v| v.clone()).flatten().unwrap()).fun(tele));
            Ok(self)
        } else {
            Err(Error { ctx: self.clone(), err: TypeError::HO(tv.clone()) })
        }
    }

    pub fn register_constraint(&mut self, tv: Term, t: Term) -> Result<&mut Self, Error> {
        let (v, args) = tv.whd(self, WhdFlags::default())?.behead();
        self.hole.get_mut(v.dest_hole()?).unwrap().cstr.push((args.clone(), t));
        Ok(self)
    }

    pub fn set_option(&mut self, o: String, v: String) -> &mut Self {
        match self.options.get_mut(&o) {
            None => { self.options.insert(o, vec![v]); }
            Some(args) => args.push(v)
        };
        self
    }

    pub fn unset_option(&mut self, o: &String) -> &mut Self {
        match self.options.get_mut(o) {
            None => eprintln!("Cannot unset option {} that was never set.", o),
            Some(args) => {
                args.pop();
                if args.len() == 0 { self.options.remove(o); }
            }
        };
        self
    }

    pub fn pop_var(&mut self) -> &mut Self {
        self.var.pop_back();
        self
    }

    /* TOTHINK: We hide errors */
    pub fn pop_const(&mut self, c: &Name) -> &mut Self {
        self.cst.remove(c);
        self
    }

    pub fn depth(&self) -> usize {
        self.var.len()
    }

    pub fn with_var<F, T>(&mut self, v: (Name, Term, Option<Term>), f: F) -> T
        where F: FnOnce(&mut Context) -> T {
        self.push_var(v);
        let t = f(self);
        self.pop_var();
        t
    }

    pub fn fold_telescope<'a, T, U, I, F, G>(&mut self, f: F, tele: &mut I, init: T, g: G) -> U
        where I: Iterator<Item = &'a Binder>,
              F: Fn(&mut Context, &'a Binder, T) -> T,
              G: FnOnce(&mut Context, T) -> U {
        let x = tele.next();
        match x {
            None => g(self, init),
            Some(b) => {
                let t = f(self, b, init);
                let (v, ty, b) = b.clone();
                self.with_var((v, ty, b), |ctx| ctx.fold_telescope(f, tele, t, g))
            }
        }
    }

    //FIXME: Find a better name.
    pub fn save<T, E, F>(&mut self, f: F) -> Result<T, E>
        where F: FnOnce(&mut Context) -> Result<T, E> {
        let n = self.commits.len();
        f(self).map_err(|e| {
            loop {
                if self.commits.len() == n { return e };
                match self.commits.pop().unwrap() {
                    Commit::PushHole() => { self.hole.pop(); },
                    Commit::ReinstantiateHole(v, t) => { self.hole.get_mut(v).unwrap().body = Some(t); }
                    Commit::PushHoleConstraint(v) => { self.hole.get_mut(v).unwrap().cstr.pop(); }
                };
            }
        })
    }

    pub fn reset_holes(&mut self) -> &Self {
        self.hole = Vec::new();
        self
    }
}

