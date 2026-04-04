mod utils;
mod kernel;
mod engine;
mod command;
mod parser;
mod tactic;
mod error;
mod goal;

use std::env;
use std::io::Read;
use crate::parser::parse;

fn main() {
    //let args: Vec<String> = env::args().collect();
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    let cmds = parse(&input).unwrap();
    println!("Successful parse! Got {} commands.", cmds.len());

    let mut ctx = crate::command::Context::new();
    for c in cmds {
        match c.exec(&mut ctx) {
            Ok(_) => (),
            Err(err) => {
                println!("{:?}\n\n in ctx {:?}", err, ctx);
                return;
            }
        }
    }

    if let crate::command::Status::Proofmode(_, _, _, goals) = ctx.status {
        if goals.len() == 0 {} else {
            println!("{}", goals[0].pp(&mut ctx.engine).expect("Unable to print first goal"))
        };
    }
}

