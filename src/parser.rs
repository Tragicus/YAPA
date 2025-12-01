use crate::kernel::univ::*;
use crate::engine::context::*;
use crate::command::*;
use crate::engine::context::Context;
use crate::tactic::*;
use std::rc::Rc;
use std::collections::VecDeque;
use std::collections::HashMap;
use crate::utils::ShadowHashMap;
use std::vec::Vec;
use pest::Parser;
use pest_derive::Parser;
use pest::error::Error;
use pest::iterators::Pair;

#[derive(Parser)]
#[grammar = "parser.pest"]
struct YapaParser;

pub type Binder = (String, Term, Option<Term>);
pub type Telescope = VecDeque<Binder>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Const(String),
    App(VecDeque<Term>),
    /* The Fun constructor packages the \lambda, \Pi and let constructs. Lets
     * are represented using defined binders. The boolean is true whenever the
     * constructor represents a \Pi, false when it represents a \lambda. */
    Fun(bool, Telescope, Box<Term>),
    Type(Univ),
}

impl Term {
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

    pub fn capture_vars(self, ctx: &mut Context) -> crate::engine::term::Term {
        fn fold_map_tele<'a, I>(ctx: &mut Context, vars: &mut ShadowHashMap<String, usize>, i: usize, mut tele: I, body: Term) -> (crate::engine::term::Telescope, crate::engine::term::Term)
            where I: Iterator<Item = Binder> {
            let x = tele.next();
            match x {
                None => (crate::engine::term::Telescope::new(), aux(ctx, vars, i, body)),
                Some((v, ty, b)) => {
                    let ty = aux(ctx, vars, i, ty);
                    let b = b.map(|b| aux(ctx, vars, i, b));
                    vars.insert(v.clone(), i);
                    let (mut tele, body) = ctx.with_var((v.clone(), ty.clone(), b.clone()), |ctx| fold_map_tele(ctx, vars, i+1, tele, body));
                    vars.remove(&v);
                    tele.push_front((v, ty, b));
                    (tele, body)
                }
            }
        }

        fn aux(ctx: &mut Context, vars: &mut ShadowHashMap<String, usize>, i: usize, t: Term) -> crate::engine::term::Term {
            match t {
                Term::Type(u) => crate::engine::term::Term::Type(u),
                Term::Const(c) =>
                    if c == "_".to_string() { ctx.new_hole(c, None, true) } else {
                        vars.get(&c).map_or(crate::engine::term::Term::Const(c.clone()), |v| crate::engine::term::Term::Var(i - v - 1))
                    },
                Term::App(args) => crate::engine::term::Term::App(args.into_iter().map(|t| aux(ctx, vars, i, t).into()).collect()),
                Term::Fun(forall, tele, body) => {
                    let (tele, body) = fold_map_tele(ctx, vars, i, tele.into_iter(), *body);
                    crate::engine::term::Term::Fun(forall, tele, body.into())
                }
            }
        }

        let (_, mut vars) = ctx.var.iter().fold((0, ShadowHashMap::new()), |(i, mut vars), (v, _, _)| {
            vars.insert(v.clone(), i);
            (i+1, vars)
        });

        aux(ctx, &mut vars, ctx.var.len(), self)
    }
}

fn parse_command(pair:Pair<Rule>) -> Command {
    match pair.as_rule() {
        Rule::print => Command::Print(parse_term(pair.into_inner().next().unwrap())),
        Rule::check => Command::Check(parse_term(pair.into_inner().next().unwrap())),
        Rule::define => {
            let mut inner_rules = pair.into_inner();
            let name = inner_rules.next().unwrap().as_str().to_string();
            let tele = parse_tele(inner_rules.next().unwrap());
            let ty = parse_type_annot(inner_rules.next().unwrap());
            let t = parse_def_body(inner_rules.next().unwrap());
            Command::Define(name, ty.forall(tele.clone()), t.fun(tele))
        }
        Rule::proof => Command::Skip(),
        Rule::tac => Command::Tac(parse_tactic(pair.into_inner().next().unwrap())),
        Rule::end_proof => {
            Command::Qed(match pair.into_inner().next().unwrap().as_rule() {
                Rule::qed => false,
                Rule::defined => true,
                _ => unreachable!()
            })
        }
        Rule::whd => Command::Whd(parse_term(pair.into_inner().next().unwrap())),
        Rule::debug => Command::Set("debug ".to_string() + pair.into_inner().next().unwrap().as_str(), None),
        Rule::stop => Command::Stop(),
        _ => unreachable!(),
    }
}

fn parse_tactic(pair: Pair<Rule>) -> Tactic {
    match pair.as_rule() {
        Rule::exact => Tactic::Exact(parse_term(pair.into_inner().next().unwrap())),
        Rule::refine => Tactic::Refine(parse_term(pair.into_inner().next().unwrap())),
        Rule::apply => Tactic::Apply(parse_term(pair.into_inner().next().unwrap())),
        Rule::intro => Tactic::Intro(pair.into_inner().next().unwrap().into_inner().map(|name| name.as_str().to_string()).collect()),
        _ => unreachable!(),
    }
}

fn parse_tele(pair: Pair<Rule>) -> Telescope {
    pair.into_inner().map(|pair| {
        match pair.as_rule() {
            Rule::name => vec![(pair.as_str().to_string(), Term::Const("_".to_string()), None)].into_iter(),
            Rule::tele_item => {
                let mut inner_rules = pair.into_inner();
                let names = inner_rules.next().unwrap();
                let ty = parse_term(inner_rules.next().unwrap());
                names.into_inner().map(move |name| (name.as_str().to_string(), ty.clone(), None)).collect::<Vec<_>>().into_iter()
            }
            _ => unreachable!()
        }
    }).flatten().collect()
}

fn parse_sterm_atom(pair: Pair<Rule>) -> Term {
    //println!("sterm_atom: {:?}", pair.as_rule());
    match pair.as_rule() {
        Rule::paren_term => parse_term(pair.into_inner().next().unwrap()),
        Rule::name => Term::Const(pair.as_str().to_string()),
        Rule::fun => {
            let mut inner_rules = pair.into_inner();
            let tele = parse_tele(inner_rules.next().unwrap());
            let body = parse_term(inner_rules.next().unwrap());
            Term::Fun(false, tele, Box::new(body))
        }
        Rule::forall => {
            let mut inner_rules = pair.into_inner();
            let tele = parse_tele(inner_rules.next().unwrap());
            let body = parse_term(inner_rules.next().unwrap());
            Term::Fun(true, tele, Box::new(body))
        }
        Rule::ttype => Term::Type(Univ::exact(0)),
        Rule::tlet => {
            let mut inner_rules = pair.into_inner();
            let name = inner_rules.next().unwrap().as_str().to_string();
            let ty = parse_term(inner_rules.next().unwrap());
            let body = parse_term(inner_rules.next().unwrap());
            let cont = parse_term(inner_rules.next().unwrap());
            Term::Fun(false, VecDeque::from([(name, ty, Some(body))]), Box::new(cont))
        }
        _ => unreachable!()
    }
}

fn parse_sterm(pair: Pair<Rule>) -> Term {
    //println!("sterm: {:?}", pair.as_rule());
    let mut args : VecDeque<Term> = pair.into_inner().map(parse_sterm_atom).collect();
    if args.len() == 1 { let t = args.pop_front().unwrap(); t } else { Term::App(args.into_iter().map(|x| x.into()).collect()) }
}

fn parse_def_body(pair: Pair<Rule>) -> Term {
    //println!("def_body: {:?}", pair.as_rule());
    pair.into_inner().map(parse_term).next().unwrap_or(Term::Const("_".to_string()))
} 

fn parse_type_annot(pair: Pair<Rule>) -> Term {
    //println!("type_annot: {:?}", pair.as_rule());
    pair.into_inner().map(parse_term).next().unwrap_or(Term::Const("_".to_string()))
} 

fn parse_term(pair: Pair<Rule>) -> Term {
    let mut tele : VecDeque<Term> = pair.into_inner().map(parse_sterm).collect();
    let body = tele.pop_back().unwrap();
    if tele.len() == 0 { body } else {
        Term::Fun(true, tele.into_iter().map(|ty| ("_".to_string(), ty, None)).collect(), Box::new(body))
    }
}

pub fn parse(file: &str) -> Result<Vec<Command>, Error<Rule>> {
    let mut ast : Vec<_> = YapaParser::parse(Rule::toplevel, file)?.collect();
    ast.pop();
    Ok(ast.into_iter().map(parse_command).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use Term::*;
    use std::collections::VecDeque;
    use std::rc::Rc;

    #[test]
    fn test_parser() {
        assert_eq!(parse(&"x".to_string()), Ok(Const("x".to_string())));
        assert_eq!(parse(&"(x)".to_string()), Ok(Const("x".to_string())));
        assert_eq!(parse(&"x -> y".to_string()), Ok(Forall(VecDeque::from([("_".to_string(), Const("x".to_string()))]), Rc::new(Const("y".to_string())))));
        assert_ne!(parse(&"x -> y".to_string()), Ok(Forall(VecDeque::from([("_".to_string(), Const("x".to_string()))]), Rc::new(Const("x".to_string())))));
        assert_eq!(parse(&"x y z".to_string()), Ok(App(VecDeque::from([Rc::new(Const("x".to_string())), Rc::new(Const("y".to_string())), Rc::new(Const("z".to_string()))]))));
        assert_eq!(parse(&"x y -> z".to_string()), Ok(Forall(VecDeque::from([("_".to_string(), App(VecDeque::from([Rc::new(Const("x".to_string())), Rc::new(Const("y".to_string()))])))]), Rc::new(Const("z".to_string())))));
    }

    #[test]
    fn test_app() -> Result<(), Box<dyn std::error::Error>> {
        assert_eq!(parse(&"x y".to_string())?.app(parse(&"z t".to_string())?), parse(&"x y (z t)".to_string())?);
        Ok(())
    }

    #[test]
    fn test_subst() {
        assert_eq!(Var(0).subst(|i| if i == 0 { Some(Type(Univ::exact(0))) } else { None }), Type(Univ::exact(0)));
        assert_eq!(
            App(VecDeque::from([Var(0).into(), Const("y".to_string()).into()])).subst(|i| if i == 0 { Some(Type(Univ::exact(0))) } else { None }),
            App(VecDeque::from([Type(Univ::exact(0)).into(), Const("y".to_string()).into()])));
        assert_eq!(
            App(VecDeque::from([Const("y".to_string()).into(), Var(0).into()])).subst(|i| if i == 0 { Some(Type(Univ::exact(0))) } else { None }),
            App(VecDeque::from([Const("y".to_string()).into(), Type(Univ::exact(0)).into()])));
                       
    }
}
