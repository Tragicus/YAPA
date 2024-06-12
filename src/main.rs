mod term;
mod parser;
mod context;
mod typecheck;

use crate::parser::parse;
use crate::context::Context;

fn main() {
    let input = "forall x : Type, x";

    match parse(input) {
        Ok(term) => {
            println!("Parsed term: {:?}", term);
            match term.type_check(&mut Context::new()) {
                Ok(ty) => println!(" of type {:?}", ty),
                Err(msg) => println!("{}", msg),
            }
        }
        Err(e) => println!("Parse error: {}", e),
    }
}

/*
fn main() {
    let mut context = Context::new();

    loop {
        print!("> ");
        io::stdout().flush().unwrap();

        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();

        let term = parse_term(&input); // Implement a parser for terms
        match term {
            Ok(term) => {
                match type_check(&term, &context) {
                    Ok(ty) => println!("Type: {:?}", ty),
                    Err(e) => println!("Error: {}", e),
                }
            }
            Err(e) => println!("Parse error: {}", e),
        }
    }
}
*/
