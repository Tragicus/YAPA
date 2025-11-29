mod utils;
mod kernel;
mod engine;
mod command;
mod parser;
mod tactic;

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
    for c in cmds { c.exec(&mut ctx); }
}

