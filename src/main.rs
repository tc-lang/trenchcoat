#![warn(clippy::perf)]

mod tokens;

use tokens::tokenize;

fn main() -> std::io::Result<()> {
    // Currently just a simple test of the tokenizer
    let s = "a bc def 123hi  var2; let a = (b+c.x) / 2";
    //let mut s = String::new();
    //std::fs::File::open("input")?.read_to_string(&mut s)?;
    println!("{:?}", tokenize(s));
    Ok(())
}
