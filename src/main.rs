#![warn(clippy::perf)]

mod ast;
mod tokens;

use tokens::tokenize;

fn main() {
    // Currently just a simple test of the tokenizer
    let s = "a bc def 123hi  var2; let a = (b+c.x) / 2";
    //let mut s = String::new();
    //std::fs::File::open("input")?.read_to_string(&mut s)?;
    let tokens = tokenize(s);

    let invalid_tokens = tokens::collect_invalid(&tokens);
    if !invalid_tokens.is_empty() {
        for t in invalid_tokens {
            eprintln!("Invalid token {:?}", t);
        }
        return;
    }

    println!("{:?}", ast::try_parse(&tokens));
}
