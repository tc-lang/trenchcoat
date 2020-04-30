#![warn(clippy::perf)]

mod ast;
mod tokens;
mod verify;

use tokens::auto_sep::auto_insert_sep;
use tokens::tokenize;
use verify::verify;

fn main() {
    // Currently just a simple test of the tokenizer
    //let s = "a bc def 123hi  var2; let a = (b+c.x) / 2";
    let s = "fn f() {1 + 2};  fn hi (x, y){x * !y; 1 + 5\nf(x)+3}";
    //let s = "fn f() {2}";
    //let mut s = String::new();
    //std::fs::File::open("input")?.read_to_string(&mut s)?;
    let mut tokens = tokenize(s);
    auto_insert_sep(&mut tokens);

    let invalid_tokens = tokens::collect_invalid(&tokens);
    if !invalid_tokens.is_empty() {
        for t in invalid_tokens {
            eprintln!("Invalid token {:?}", t);
        }
        return;
    }

    let tree = match ast::try_parse(&tokens) {
        Ok(tree) => tree,
        Err(errs) => {
            println!("AST Parsing Errors: {:?}", errs);
            return;
        }
    };

    println!("{:?}", tokens);
    println!("{:?}", tree);

    println!("Verify: {:?}", verify(&tree));
}
