use crate::engine::context::*;
use crate::command::*;
use crate::engine::context::Context;
use crate::tactic::*;
use std::rc::Rc;
use std::collections::VecDeque;
use std::collections::HashMap;
use std::collections::BTreeMap;
use crate::utils::{VarType, ShadowHashMap};
use std::vec::Vec;
use pest::Parser;
use pest_derive::Parser;
use pest::error::Error;
use pest::iterators::Pair;

#[derive(Parser)]
#[grammar = "parser.pest"]
struct YapaParser;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    SProp(),
    Prop(),
    Type(),
    Var(String)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Level {
    pub vars: BTreeMap<String, usize>
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Univ {
    sort: Sort,
    level: Level
}

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

    pub fn capture_vars(self, ctx: &mut Context) -> Result<crate::engine::term::Term, crate::engine::error::Error> {
        fn fold_map_tele<'a, I>(ctx: &mut Context, vars: &mut ShadowHashMap<String, usize>, sorts: &HashMap<String, VarType>, levels: &HashMap<String, VarType>, i: usize, mut tele: I, body: Term) -> Result<(crate::engine::term::Telescope, crate::engine::term::Term), crate::engine::error::Error>
            where I: Iterator<Item = Binder> {
            let x = tele.next();
            Ok(match x {
                None => (crate::engine::term::Telescope::new(), aux(ctx, vars, sorts, levels, i, body)?),
                Some((v, ty, b)) => {
                    let ty = aux(ctx, vars, sorts, levels, i, ty)?;
                    let b = b.map(|b| aux(ctx, vars, sorts, levels, i, b)).transpose()?;
                    vars.insert(v.clone(), i);
                    let (mut tele, body) = ctx.with_var((v.clone(), ty.clone(), b.clone()), |ctx| fold_map_tele(ctx, vars, sorts, levels, i+1, tele, body))?;
                    vars.remove(&v);
                    tele.push_front((v, ty, b));
                    (tele, body)
                }
            })
        }

        fn aux(ctx: &mut Context, vars: &mut ShadowHashMap<String, usize>, sorts: &HashMap<String, VarType>, levels: &HashMap<String, VarType>, i: usize, t: Term) -> Result<crate::engine::term::Term, crate::engine::error::Error> {
            Ok(match t {
                Term::Type(Univ { sort: s, level: u }) => crate::engine::term::Term::Type(crate::kernel::univ::Univ {
                    sort: match s {
                        Sort::SProp() => crate::kernel::univ::Sort::SProp(),
                        Sort::Prop() => crate::kernel::univ::Sort::Prop(),
                        Sort::Type() => crate::kernel::univ::Sort::Type(),
                        Sort::Var(s) => crate::kernel::univ::Sort::Var(if s == "_" { ctx.univ.new_sort(None) } else { *sorts.get(&s).ok_or(crate::engine::error::Error::UnboundConst(s))? }),
                    },
                    level: crate::kernel::univ::Level { vars:
                        if u.vars.len() == 0 {
                            let u = ctx.univ.new_level(None);
                            BTreeMap::from([(u, 0)])
                        } else {
                            u.vars.into_iter().map(|(v, i)| Ok::<_, crate::engine::error::Error>((levels.get(&v).ok_or(crate::engine::error::Error::UnboundConst(v))?.clone(), i as isize))).collect::<Result<_, _>>()?
                        }
                    }}),
                Term::Const(c) =>
                    if c == "_".to_string() { ctx.new_hole(c, None, true) } else {
                        match vars.get(&c) {
                            None => ctx.fresh_const(c)?,
                            Some(v) => crate::engine::term::Term::Var(i - v - 1)
                        }
                    },
                Term::App(args) => crate::engine::term::Term::App(args.into_iter().map(|t| Ok::<_, crate::engine::error::Error>(aux(ctx, vars, sorts, levels, i, t)?.into())).collect::<Result<_, _>>()?),
                Term::Fun(forall, tele, body) => {
                    let (tele, body) = fold_map_tele(ctx, vars, sorts, levels, i, tele.into_iter(), *body)?;
                    crate::engine::term::Term::Fun(forall, tele, body.into())
                }
            })
        }

        let mut vars = ctx.var.iter().enumerate().fold(ShadowHashMap::new(), |mut vars, (i, (v, _, _))| {
            vars.insert(v.clone(), i);
            vars
        });

        let sorts = ctx.univ.sorts.iter().fold(HashMap::new(), |mut sorts, (n, _, _, _, _)| {
            n.as_ref().map(|n| sorts.insert(n.clone(), sorts.len()));
            sorts
        });

        let levels = ctx.univ.levels.iter().fold(HashMap::new(), |mut levels, (n, _)| {
            n.as_ref().map(|n| levels.insert(n.clone(), levels.len()));
            levels
        });

        aux(ctx, &mut vars, &sorts, &levels, ctx.var.len(), self)
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
        Rule::tac => Command::Tac(parse_tactic(pair)),
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
    let tacs: VecDeque<_> = pair.into_inner().map(|stac| parse_simple_tactic(stac.into_inner().next().unwrap())).collect();
    //TOTHINK: Why do I have to clone here?
    if tacs.len() == 1 { tacs[0].clone() } else { Tactic::Seq(tacs) }
}

fn parse_simple_tactic(pair: Pair<Rule>) -> Tactic {
    match pair.as_rule() {
        Rule::exact => Tactic::Exact(parse_term(pair.into_inner().next().unwrap())),
        Rule::refine => Tactic::Refine(parse_term(pair.into_inner().next().unwrap())),
        Rule::apply => Tactic::Apply(pair.into_inner().map(|t| parse_term(t)).collect()),
        Rule::intro => Tactic::Intro(pair.into_inner().next().unwrap().into_inner().map(|name| name.as_str().to_string()).collect()),
        Rule::assumption => Tactic::Assumption(),
        Rule::clear => Tactic::Clear(pair.into_inner().next().unwrap().into_inner().map(|name| name.as_str().to_string()).collect()),
        Rule::tac => parse_tactic(pair.into_inner().next().unwrap()),
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
        Rule::ttype => {
            let mut inner_rules = pair.into_inner().rev();
            let level = inner_rules.next();
            let sort = inner_rules.next();

            let sort = sort.map_or(Sort::Type(), |pair|
                match pair.as_str() {
                    "SProp" => Sort::SProp(),
                    "Prop" => Sort::Prop(),
                    "Type" => Sort::Type(),
                    s => Sort::Var(s.to_string())
                });

            let level = level.map_or(Level { vars: BTreeMap::new() }, parse_level);

            Term::Type(Univ { sort, level })
        }
        Rule::tprop => Term::Type(Univ { sort: Sort::Prop(), level: Level { vars: BTreeMap::from([(String::new(), 0)]) } }),
        Rule::tsprop => Term::Type(Univ { sort: Sort::SProp(), level: Level { vars: BTreeMap::from([(String::new(), 0)]) } }),
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

fn parse_level(pair: Pair<Rule>) -> Level {
    match pair.as_rule() {
        Rule::name => {
            let u = pair.as_str().to_string();
            Level { vars: BTreeMap::from([(u, 0)]) }
        }
        Rule::ladd => {
            let mut inner_rules = pair.into_inner();
            let u = inner_rules.next().unwrap().as_str().to_string();
            let i = inner_rules.next().unwrap().as_str().parse::<usize>().unwrap();
            Level { vars: BTreeMap::from([(u, i)]) }
        }
        Rule::lmax => {
            let mut lvs = pair.into_inner().map(parse_level);
            let mut u = lvs.next().unwrap().vars;
            for v in lvs {
                for (x, i) in v.vars.into_iter() {
                    let j = u.get(&x).unwrap_or(&0);
                    u.insert(x, std::cmp::max(i, *j));
                }
            }
            Level { vars: u }
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
        assert_eq!(Var(0).subst(|i| if i == 0 { Some(Type(Univ::set())) } else { None }), Type(Univ::set()));
        assert_eq!(
            App(VecDeque::from([Var(0).into(), Const("y".to_string()).into()])).subst(|i| if i == 0 { Some(Type(Univ::set())) } else { None }),
            App(VecDeque::from([Type(Univ::set()).into(), Const("y".to_string()).into()])));
        assert_eq!(
            App(VecDeque::from([Const("y".to_string()).into(), Var(0).into()])).subst(|i| if i == 0 { Some(Type(Univ::set())) } else { None }),
            App(VecDeque::from([Const("y".to_string()).into(), Type(Univ::set()).into()])));
                       
    }
}
