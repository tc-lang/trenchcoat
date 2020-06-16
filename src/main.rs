#![warn(clippy::perf)]

mod ast;
mod exec;
mod proof;
mod tokens;
mod types;
mod verify;

use ansi_term::Color::Red;
use ast::try_parse;
use tokens::auto_sep::auto_insert_sep;
use tokens::tokenize;
use verify::verify;

fn main() {
    // This function displays the high-level pipeline of the interpreter. Each step is labeled,
    // with a little bit of description as to what it does. For a more complete overview, please
    // refer to the accompanying writeup of the system as a whole.

    // 1. Get the input file as a string
    //
    // The `include_str!` macro produces a static string given by the contents of the file it is
    // given, at compile-time. Instead of interfacing with command-line arugments (and other IO),
    // which could proudce runtime errors that we'd need to handle, we just do all of the necessary
    // IO at compile-time.
    let input_str = include_str!("test_input.tc");
    const FULL_INPUT_FILE: &'static str = "src/test_input.tc";

    // 2. Tokenize
    //
    // We produce token trees from the input string, and then auto-insert statement separators
    // where applicable (allowing the language's syntax to remain relatively clean of punctuation).
    //
    // What should be noted is that invalid tokens are included in the set of tokens produecd by
    // `tokenize`, so we need to determine if tokenizing has encountered errors as a separate
    // operation (hence `collect_invalid`).
    let mut tokens = tokenize(input_str);
    auto_insert_sep(&mut tokens);

    let invalid_tokens = tokens::collect_invalid(&tokens);
    if !invalid_tokens.is_empty() {
        for t in invalid_tokens {
            eprintln!("Invalid token {:?}", t);
        }
        return;
    }

    // 3. Parse into the AST
    //
    // Parsing is largely covered elsewhere. The key piece to note here is that `try_parse`
    // produces a value of type `Result<Vec<ast::Item>, Vec<Error>>`, which means that subsequent
    // operations cannot proceed without the success of this step.
    //
    // If we encounter errors here, we'll display them in a pleasant fashion and then exit, as
    // there's nothing left to do.
    let parse_tree = match try_parse(&tokens) {
        Ok(tree) => tree,
        Err(errs) => {
            display_errors(input_str, FULL_INPUT_FILE, &errs, "Failed to parse");
            return;
        }
    };

    // 4. Verify
    //
    // Verification - like parsing - is covered extensively elsewhere. Because both verification
    // and execution rely on the AST, it is *possible* to skip this step, leaving any errors to
    // cause runtime failure. We don't do that, however, because that would be contrary to the
    // point of this project.
    //
    // Like parsing, if we encountered any errors here, we'll display them and exit.
    match &verify(&parse_tree)[..] {
        [] => (),
        errs => {
            display_errors(input_str, FULL_INPUT_FILE, &errs, "Could not verify");
            return;
        }
    }

    // 5. Execute
    //
    // This is perhaps the most simple step. Execution takes the entire input to build a "global
    // scope" (primarily a registry of functions), and we then execute 'main', provided it exists.
    //
    // Checking that 'main' exists and has the correct number of arguments is the only check
    // perfomed at this stage.
    //
    // We also output any value returned from 'main', just to provide extra information.
    let global = exec::generate_global_scope(parse_tree);
    match global.num_args("main") {
        None => eprintln!("no fn 'main' found"),
        Some(n) if n != 0 => eprintln!(
            "wrong number of args for fn 'main'; expected 0, found {}",
            n
        ),
        Some(_) => {
            println!("main: {:?}", global.exec("main", Vec::new()));
        }
    }
}

/// A helper function to provide pretty printing of error messages
fn display_errors<E: PrettyError>(file_str: &str, file_name: &str, errs: &[E], pre_msg: &str) {
    if errs.is_empty() {
        panic!("Internal error: no errors to display");
    }

    for err in errs {
        eprintln!("{}", err.pretty_print(file_str, file_name));
    }

    let err_no = match errs.len() {
        1 => "a previous error".into(),
        n => format!("{} previous errors", n),
    };

    eprintln!("{}: {} due to {}", Red.paint("error"), pre_msg, err_no);
}

trait PrettyError {
    fn pretty_print(&self, file_str: &str, file_name: &str) -> String;
}
