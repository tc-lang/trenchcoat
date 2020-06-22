mod tokens;

use tokens::tokenize;

fn main() {
    let input_str = include_str!("test_input.tc");
    println!("{:?}", tokenize(input_str));
}
