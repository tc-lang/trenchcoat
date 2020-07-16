mod ast;
mod error;
mod files;
mod token_tree;
mod tokens;

use ast::readable::Readable;
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

    println!("TOKENS: {:?}", tokens);

    use std::io::prelude::*;
    match crate::ast::try_parse(&tokens.tokens).map(|ast| ast.readable()) {
        Ok(readable) => {
            std::io::stdout().write(&readable.as_ref()).unwrap();
        }
        Err(errors) => println!(
            "\n\nAST Errors:\n\n{:?}",
            errors
                .iter()
                .map(|error| format!(
                    "{:?}\n\n{}\n\n",
                    error,
                    error
                        .src
                        .first()
                        .and_then(|token| token.src.first())
                        .map(|st| quick_context(input_str, st.src))
                        .unwrap_or("None")
                ))
                .collect::<Vec<_>>()
        ),
    }
}

fn quick_context<'a>(file: &'a str, src: &'a str) -> &'a str {
    let offset = src.as_ptr() as usize - file.as_ptr() as usize;
    let start = offset.saturating_sub(10);
    let end = offset.saturating_add(10).min(file.len());
    &file[start..end]
}
