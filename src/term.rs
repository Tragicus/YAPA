use std::rc::Rc;

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Var(String),
    App(Vec<Term>),
    Lambda(String, Rc<Term>, Box<Term>),
    Pi(String, Rc<Term>, Box<Term>),
    Type(usize),
}

impl Term {
    pub fn mk_app(&self, arg: Term) -> Term {
        match self {
            Term::App(args) => {
                let mut args = args.clone();
                args.push(arg);
                Term::App(args)
            }
            _ => Term::App(vec![self.clone(), arg.clone()]),
        }
    }

    pub fn subst(&self, var: &String, value: &Term) -> Term {
        match self {
            Term::Var(v) if v == var => value.clone(),
            Term::App(args) => Term::App(args.iter().map(|x| x.subst(var, value)).collect()),
            Term::Lambda(v, ty, body) if v != var => Term::Lambda(
                v.clone(),
                ty.clone(),
                Box::new(body.subst(var, value)),
                ),
            Term::Pi(v, ty1, ty2) if v != var => Term::Pi(
                v.clone(),
                ty1.clone(),
                Box::new(ty2.subst(var, value)),
                ),
            _ => self.clone(),
        }
    }
}

