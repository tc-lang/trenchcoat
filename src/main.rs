mod error;
mod files;
mod token_tree;
mod tokens;

use files::Files;
use token_tree::file_tree;
use tokens::tokenize;

fn main() {
    let mut files = Files::new();

    let input_str = include_str!("test_input.tc");
    files.add("test_input.tc", input_str);

    let token_results = tokenize(input_str);
    let n_tokens = token_results.len();

    let res =
        token_results
            .into_iter()
            .fold(Ok(Vec::with_capacity(n_tokens)), |tokens, res| {
                match (tokens, res) {
                    (Ok(mut ts), Ok(t)) => {
                        ts.push(t);
                        Ok(ts)
                    }
                    (Ok(_), Err(i)) => Err(vec![i]),
                    (Err(inv), Ok(_)) => Err(inv),
                    (Err(mut inv), Err(i)) => {
                        inv.push(i);
                        Err(inv)
                    }
                }
            });

    let offset = |line: &str| {
        let start = (line as *const str as *const u8 as usize)
            - (input_str as *const str as *const u8 as usize);

        start..start + line.len()
    };

    let tokens = match res {
        Ok(ts) => ts,
        Err(es) => {
            error::display_errors(es.into_iter(), (offset, "test_input.tc"), &files);
            return;
        }
    };

    let tokens = file_tree(&tokens);
    let token_tree_errors = tokens.collect_errors();
    if !token_tree_errors.is_empty() {
        error::display_errors(
            token_tree_errors.into_iter(),
            (offset, "test_input.tc"),
            &files,
        );
        return;
    }

    println!("{:?}", tokens);
}
