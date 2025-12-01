use super::term::*;
use super::error::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    // local variables
    pub var: Vec<Binder>,

    // global variables
    pub cst: HashMap<Name, (Term, Term)>,

    // Graph with an arc from v to w if v *-reduces to w when applied to enough arguments. Its
    // label tells the minimum number of beta-reductions needed to go from v to w.
    //pub reds: Graph<(Name, usize), usize>,

    // Graph with an arc from u to v if u <= v. The label of the arc tells if the inequality is
    // strict
    //pub universes: Graph<(), bool>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            var: Vec::new(),
            cst: HashMap::new(),
            //reds: Graph::new(),
            //universes: Graph::new(),
        }
    }

    pub fn find_var(&self, v: &VarType) -> Result<&(Name, Term, Option<Term>), Error> {
        self.var.get(self.var.len() - *v - 1).map_or(Err(Error::UnboundVar(v.clone())), |x| Ok(x))
    }

    pub fn find_const(&self, v: &Name) -> Result<&(Term, Term), Error> {
        self.cst.get(v).ok_or(Error::UnboundConst(v.clone()))
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

    pub fn get_const_type(&self, v: &Name) -> Result<&Term, Error> {
        let (t, _) = self.find_const(v)?;
        Ok(t)
    }

    pub fn get_const_body(&self, v: &Name) -> Result<&Term, Error> {
        let (_, t) = self.find_const(v)?;
        Ok(t)
    }

    pub fn push_var(&mut self, t: (Name, Term, Option<Term>)) -> &mut Self {
        self.var.push(t);
        self
    }

    pub fn push_const(&mut self, c: Name, t: (Term, Term)) -> &mut Self {
        self.cst.insert(c, t);
        self
    }

    pub fn pop_var(&mut self) -> &mut Self {
        self.var.pop();
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
}

