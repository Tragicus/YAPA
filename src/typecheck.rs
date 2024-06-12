use crate::context::*;
use crate::term::*;

impl Term {
    pub fn type_check<'a>(&'a self, ctx: &'a mut Context) -> Result<Term, String> {
        match self {
            Term::Var(v) => {
                match ctx.types.get(v) {
                    Some(ty) => Ok(ty.clone()),
                    _ => Err(format!("Unbound variable: {}", v)),
                }
            }
            Term::App(args) => {
                let mut args = args.iter().peekable();
                let f = match args.next() {
                    Some(x) => x,
                    _ => return Err(format!("Empty application")),
                };
                if args.peek() == None {
                    Err(format!("Application with no arguments"))
                } else {
                    let mut ty_f = f.type_check(ctx)?;
                    for arg in args {
                        let ty_arg = arg.type_check(ctx)?;
                        match ty_f {
                            Term::Pi(_, tyf_arg, tyf_next) if ty_arg == *tyf_arg => {
                                ty_f = *tyf_next;
                            },
                            _ => return Err(format!("Type mismatch in application: {:?} applied to {:?}", ty_f, ty_arg)),
                        }
                    };
                    Ok(ty_f)
                }
            }
            Term::Lambda(v, ty, body) => {
                let ctx_types = ctx.types.clone();
                ctx.types.insert(v.clone(), <Term>::clone(&*ty ));
                let res = body.type_check(ctx)?;
                ctx.types = ctx_types;
                Ok(Term::Pi(v.clone(), ty.clone(), Box::new(res)))
            }
            Term::Pi(v, ty, body) => {
                match ty.type_check(ctx) {
                    Ok(Term::Type(n)) => {
                        let ctx_types = ctx.types.clone();
                        ctx.types.insert(v.clone(), <Term>::clone(&*ty));
                        let t = body.type_check(ctx)?;
                        ctx.types = ctx_types;
                        match t {
                            Term::Type(m) => {
                                if m == 0 {
                                    Ok(Term::Type(0))
                                } else {
                                    let k = ctx.fresh_universe();
                                    ctx.add_univ_constraint(n, k, true);
                                    ctx.add_univ_constraint(m, k, true);
                                    Ok(Term::Type(k))
                                }
                            }
                            _ => Err(format!("Return type {:?} is not a type", body)),
                        }
                    }
                    Err(e) => Err(e),
                    _ => Err(format!("Type of argument {:?} is not a type: {:?}", v, ty)),
                }
            }
            Term::Type(n) => {
                let m = ctx.fresh_universe();
                ctx.add_univ_constraint(n.clone(), m.clone(), true);
                Ok(Term::Type(m))
            }
        }
    }
}

