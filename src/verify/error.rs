//! Error definitions for verification

use super::Func;
use crate::ast::{Item, ItemKind::FnDecl, Node};
use crate::proof::{ProofResult, Requirement};
use crate::types::Type;
use crate::PrettyError;
use ansi_term::Color::{Blue, Red};
use std::fmt::Write;
use std::ops::{Deref, Range};

/// Errors each have a kind and a context in which it occured. These can be combined with the
/// source AST node to create an error message.
#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub kind: Kind<'a>,
    pub context: Context,
    /// In the future, we should make a source stack rather than just have 1 source.
    pub source: Node<'a>,
}

#[derive(Debug, Clone)]
pub enum Kind<'a> {
    ItemConflict(&'a Item<'a>, &'a Item<'a>),
    FunctionNotFound {
        name: &'a str,
    },
    FunctionMustBeName,
    IncorrectNumberOfArgs {
        given: usize,
        func: &'a Func<'a>,
    },
    VariableNotFound,
    AccessFieldOnNotStruct,
    TypeMismatch {
        expected: Vec<Type<'a>>,
        found: Type<'a>,
    },
    /// Indicates that the return identifier "_" appeared somewhere it isn't allowed
    MisplacedReturnIdent,
    /// Indicates that a certain feature is currently not allowed (even though it may be
    /// syntactically or otherwise valid)
    FeatureNotAllowed {
        description: &'static str,
    },
    /// A collection of proof requirements that didn't pass, along with their proof results.
    /// Note: The requirements are in terms of the variables in the calling scope.
    FailedProofs {
        fn_name: &'a str,
        func_info: &'a Func<'a>,
        failed: Vec<(ProofResult, Requirement<'a>)>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum Context {
    NoContext,
    TopLevel,
    ProofStmt,
    Expr,
    Assign,
    FnTail,
    FnArg,
    FieldAccess,
    BinOpTypeCheck,
    PrefixOpTypeCheck,
}

impl<'a> Error<'a> {
    pub fn with_context(self, ctx: Context) -> Self {
        Self {
            context: ctx,
            ..self
        }
    }
}

///////////////////////////////////////////////////////////////////////////////
//                               Pretty Errors                               //
///////////////////////////////////////////////////////////////////////////////

impl PrettyError for Error<'_> {
    fn pretty_print(&self, file_str: &str, file_name: &str) -> String {
        use Kind::{
            FailedProofs, FunctionMustBeName, FunctionNotFound, ItemConflict, TypeMismatch,
        };

        match &self.kind {
            ItemConflict(fst, snd) => Error::format_item_conflict(fst, snd, file_str, file_name),
            FunctionNotFound { name } => {
                Error::format_function_not_found(name, &self.source, file_str, file_name)
            }
            FunctionMustBeName => {
                Error::format_function_must_be_name(&self.source, file_str, file_name)
            }
            TypeMismatch { expected, found } => {
                Error::format_type_mismatch(expected, found, &self.source, file_str, file_name)
            }
            FailedProofs {
                fn_name,
                func_info,
                failed,
            } => Error::format_failed_proofs(
                failed,
                fn_name,
                func_info,
                &self.source,
                file_str,
                file_name,
            ),
            _ => format!("{:?}\n", self),
        }
    }
}

impl Error<'_> {
    /// Returns information about the position of the given byte index within the file
    ///
    /// The return values are - in order - the line number, column number, the byte index of the
    /// line in the text, and the byte index on the line. All values start at zero.
    ///
    /// The final return value is the string containing the entire line.
    fn line_info<'a>(file_str: &'a str, byte_idx: usize) -> (usize, usize, usize, usize, &'a str) {
        let start_offset = |line: &str| {
            let line_ptr = line as *const str as *const u8 as usize;
            let base_ptr = file_str as *const str as *const u8 as usize;
            line_ptr - base_ptr
        };

        let lines = file_str
            .lines()
            .take_while(|line| start_offset(line) <= byte_idx)
            .collect::<Vec<_>>();

        let last = lines.last().unwrap();
        let offset = start_offset(last);

        // Subtract 1 from both of these so that they start at zero
        let line_no = lines.len() - 1;
        let col_no = last[..byte_idx - offset].chars().count() - 1;

        (line_no, col_no, offset, byte_idx - offset, last)
    }

    /// Produces a row of caret characters to underline the given byte range of the line. The upper
    /// value on the byte range may be longer than the end of the line - this is quietly ignored.
    fn underline(line: &str, mut range: Range<usize>) -> String {
        range.end = range.end.min(line.len());

        // In the future, this function could account for non-ascii strings. Right now, we're just
        // going with the super simple solution of not dealing with that, and simply returning the
        // values.

        // For consistency, we'll double-check that the range is within the bounds of the line
        assert!(range.start < line.len());

        let mut pre = " ".repeat(range.start);
        let mid = "^".repeat(range.end - range.start);
        let post = " ".repeat(line.len() - range.end);

        write!(pre, "{}{}", mid, post).unwrap();
        pre
    }

    /// Produces the standard portion of many error messages. This contains the "context line" and
    /// selection + highlighting of the source. The returned string has a trailing - but no leading
    /// - newline.
    ///
    /// For more information, see the comments inside the function.
    fn context_lines(source: &Node, file_str: &str, file_name: &str) -> String {
        Error::context_lines_and_spacing(source, file_str, file_name).0
    }

    /// The same function `context_lines`, except there is the added (second) return value of the
    /// spacing used to prefix certain lines
    ///
    /// This function is useful in cases where additional information must be displayed after the
    /// context lines - that additional info needs to be aligned in the same manner.
    fn context_lines_and_spacing(
        source: &Node,
        file_str: &str,
        file_name: &str,
    ) -> (String, String) {
        // The standard portion of the error message primarily consists of contextual information
        // for the user, without regard to what the error message actually is.
        //
        // Here's an example of what it might look like:
        // ```
        //   --> src/test_input.tc:18:10
        //    |
        // 18 |     print bar();
        //    |           ^^^
        // ```
        //
        // We'll use this particular example to demonstrate what each component supplies to the
        // total set of lines.

        let byte_range = source.byte_range();
        let (line_no, col_no, line_offset, _, line) = Error::line_info(file_str, byte_range.start);

        let line_no_str = (line_no + 1).to_string();
        let spacing = " ".repeat(line_no_str.len());

        // The range of bytes that the source takes up on its initial line.
        //
        // In a future version, we might allow displaying regions that span multiple lines, but
        // this will do for now - realistically, it should be fine.
        let line_range = {
            let start = byte_range.start - line_offset;
            let end = (byte_range.end - line_offset).min(line.len());
            start..end
        };

        // First, we'll put in the context line. This will tend to look something like:
        // ```
        //   --> src/test_input.tc:18:10
        // ```
        // It provides a little bit of color and the location that the error occured. The newline
        // is at the end so we can start the next line without one.
        let mut msg = format!(
            "{}{} {}:{}:{}\n",
            spacing,
            Blue.paint("-->"),
            file_name,
            line_no + 1,
            col_no + 1
        );

        // The next line is the "filler" line - this simply adds a little bit of space, and sets us
        // up for the selected text and highlight. We mostly just want this to align properly.
        //
        // We save it so that we can use it later in constructing the highlight line.
        // The filler line from above is simply:
        // ```
        //    |
        // ```
        // The only important piece here is that it lines up wit the middle character of the arrow
        // above it and evenly with the pipes below it.
        let filler_line = format!("{} {}", spacing, Blue.paint("|"));
        writeln!(msg, "{}", filler_line).unwrap();

        // And now we have some fun stuff. The selection line has two things on it: (1) The full
        // line that the node started on and (2) the line number once more, which is off to the
        // left.
        //
        // The selection line from the example is:
        // ```
        // 18 |     print bar();
        // ```
        writeln!(msg, "{} {}", Blue.paint(line_no_str + " |"), line).unwrap();

        // The final line here is the "highlight" line - though this is really more like an
        // underline. It serves to draw extra focus by giving a bright red set of "^^^^" underneath
        // the actual selected region.
        //
        // The highlight line from the example above is:
        // ```
        //    |           ^^^
        // ```
        writeln!(
            msg,
            "{} {}",
            filler_line,
            Red.paint(Error::underline(line, line_range))
        )
        .unwrap();

        (msg, spacing)
    }
}

impl Error<'_> {
    fn format_item_conflict(fst: &Item, snd: &Item, file_str: &str, file_name: &str) -> String {
        // This error message looks something like:
        // ```
        // error: duplicate definitions of function `bar`
        //   --> src/test_input.tc:17:3
        //    |
        // 17 | fn bar() {
        //    |    ^^^
        //    = note: First defined here, at src/test_input.tc:13:3:
        //    |
        // 13 | fn bar(x: int, y: int, z: int) -> int {
        //    |    ^^^
        // ```

        // We extract the names from the items so that we can specifically point to those as part
        // of the error message.
        let FnDecl { name: fst_name, .. } = &fst.kind;
        let FnDecl { name: snd_name, .. } = &snd.kind;

        // The first line of error message. We'll use this point to build the rest of it with
        // repeated `writeln!` macro usages.
        let mut msg = format!(
            "{}: duplicate definitions of function `{}`\n",
            Red.paint("error"),
            fst_name.name
        );

        let (fst_line_no, fst_col_no, fst_line, fst_line_range) = {
            let byte_range = fst_name.node().byte_range();
            let (line_no, col_no, line_offset, _, line) =
                Error::line_info(file_str, byte_range.start);

            let line_range = {
                let start = byte_range.start - line_offset;
                let end = byte_range.end - line_offset;
                start..end
            };

            (line_no, col_no, line, line_range)
        };

        let (snd_line_no, snd_col_no, snd_line, snd_line_range) = {
            let byte_range = snd_name.node().byte_range();
            let (line_no, col_no, line_offset, _, line) =
                Error::line_info(file_str, byte_range.start);

            let line_range = {
                let start = byte_range.start - line_offset;
                let end = byte_range.end - line_offset;
                start..end
            };

            (line_no, col_no, line, line_range)
        };

        let (fst_line_no_str, snd_line_no_str, spacing) = {
            let fst = (fst_line_no + 1).to_string();
            let snd = (snd_line_no + 1).to_string();

            let n_space = fst.len().max(snd.len());
            let spacing = " ".repeat(n_space);
            let fst = format!("{:>width$}", fst, width = n_space);
            let snd = format!("{:>width$}", snd, width = n_space);

            (fst, snd, spacing)
        };

        let context_line = format!(
            "{}{} {}:{}:{}",
            spacing,
            Blue.paint("-->"),
            file_name,
            snd_line_no + 1,
            snd_col_no + 1
        );
        let filler_line = format!("{} {}", spacing, Blue.paint("|"));
        let selection = format!("{} {}", Blue.paint(snd_line_no_str + " |"), snd_line);
        let highlight = format!(
            "{} {}",
            filler_line,
            Red.paint(Error::underline(snd_line, snd_line_range))
        );
        let note = format!(
            "{} {} note: First defined here, at {}:{}:{}:",
            spacing,
            Blue.paint("="),
            file_name,
            fst_line_no + 1,
            fst_col_no + 1,
        );
        let snd_selection = format!("{} {}", Blue.paint(fst_line_no_str + " |"), fst_line);
        let snd_highlight = format!(
            "{} {}",
            filler_line,
            Blue.paint(Error::underline(fst_line, fst_line_range))
        );

        writeln!(msg, "{}", context_line).unwrap();
        writeln!(msg, "{}", filler_line).unwrap();
        writeln!(msg, "{}", selection).unwrap();
        writeln!(msg, "{}", highlight).unwrap();
        writeln!(msg, "{}", note).unwrap();
        writeln!(msg, "{}", filler_line).unwrap();
        writeln!(msg, "{}", snd_selection).unwrap();
        writeln!(msg, "{}", snd_highlight).unwrap();

        msg
    }

    fn format_function_not_found(
        name: &str,
        source: &Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        // This error message looks something like:
        // ```
        // error: cannot find function `bar`
        //   --> src/test_input.tc:18:10
        //    |
        // 18 |     print bar();
        //    |           ^^^
        // ```

        format!(
            "{}: cannot find function `{}`\n{}",
            Red.paint("error"),
            name,
            Error::context_lines(source, file_str, file_name)
        )
    }

    fn format_function_must_be_name(source: &Node, file_str: &str, file_name: &str) -> String {
        // This error looks something like:
        // ```
        // error: function calls must be direct by name
        //   --> src/test_input.tc:18:10
        //    |
        // 18 |     print (foo)(1, 2);
        //    |           ^^^^^
        // ```

        format!(
            "{}: function calls must be direct by name\n{}",
            Red.paint("error"),
            Error::context_lines(source, file_str, file_name)
        )
    }

    fn format_type_mismatch(
        expected: &[Type],
        found: &Type,
        source: &Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        // This error message looks something like:
        // ```
        // error: type mismatch: expected `int`, found `bool`
        //   --> src/test_input.tc:18:14
        //    |
        // 18 |     print 1 + (2 == 3);
        //    |               ^^^^^^^^
        // ```
        //
        // or:
        //
        // ```
        // error: type mismatch: expected `int` or `uint`, found `bool`
        //  --> src/test_input.tc:5:10
        //   |
        // 5 |     print (2 == 3) + 1;
        //   |           ^^^^^^^^
        // ```

        // A helper string:
        //   "`bool`"
        //   "`int` or `uint`"
        let expected_types = match expected.deref() {
            [] => panic!("TypeMismatch has no expected types"),
            [ref typ] => format!("`{}`", typ),
            [init @ .., last] => {
                let head_str = format!("`{}`", init[0]);
                let mut s = init[1..].iter().fold(head_str, |mut s, ty| {
                    write!(s, ", `{}`", ty).unwrap();
                    s
                });
                match init.len() {
                    1 => write!(s, " or `{}`", last).unwrap(),
                    _ => write!(s, ", or `{}`", last).unwrap(),
                }
                s
            }
        };

        format!(
            "{}: type mismatch: expected {}, found `{}`\n{}",
            Red.paint("error"),
            expected_types,
            found,
            Error::context_lines(source, file_str, file_name),
        )
    }

    fn format_failed_proofs(
        proofs: &[(ProofResult, Requirement)],
        fn_name: &str,
        func: &Func,
        source: &Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        // This error message will look something like:
        //
        // ```
        // error: failed to prove that the argument to `foo` is within bounds
        //   --> src/main.tc:35:19
        //    |
        // 35 |         print x + foo(3);
        //    |                   ^^^^^^
        //    |
        //    = help: `foo(x)` requires `x >= 5`
        //    = note:
        // ```
        //
        // or:
        //
        // ```
        // error: failed to prove that the arguments to `foo` are within bounds
        //  --> src/main.tc:9:19
        //   |
        // 9 |         print x + foo(3, z);
        //   |                   ^^^^^^^^^
        //   |
        //   = help: `foo(x, y)` requires `x >= 5`, `y <= 3` and `x + y <= 10`
        //   = note: `3 >= 5` is false
        //   = note: `z <= 3` cannot be determined
        //   = note: `3 + z <= 10` cannot be determined
        // ```

        assert!(func.params.len() >= 1);
        assert!(func.reqs.is_some());
        assert!(func.reqs.as_ref().unwrap().len() >= 1);

        // The first line of error message. We'll use this point to build the rest of it with
        // repeated `writeln!` macro usages.
        let mut msg = {
            let (arg, is) = match func.params.len() {
                0 => panic!("failed requirement on function with no arguments"),
                1 => ("argument", "is"),
                _ => ("arguments", "are"),
            };

            format!(
                "{}: failed to prove that {} to `{}` {} within bounds\n",
                Red.paint("error"),
                arg,
                fn_name,
                is
            )
        };

        // Generic contextual information - this is the main body of the error message
        //
        // There's already a trailing newline from `context_lines`, so we only use write!, not
        // writeln!
        let (context_lines, spacing) =
            Error::context_lines_and_spacing(source, file_str, file_name);
        write!(msg, "{}", context_lines).unwrap();

        // The line that says:
        // ```
        //   = help: `foo(x, y)` requires `x >= 5`, `y <= 3` and `x + y <= 10`
        // ```
        let help_line = {
            // 'foo(x, y)'
            let fancy_fn = {
                let mut f = format!("{}({}", fn_name, func.params[0].0.name);
                func.params[1..].iter().for_each(|(p, _)| {
                    write!(f, ", {}", p.name).unwrap();
                });
                f.push(')');
                f
            };

            // '`x >= 5`, `y <= 3`, and `x + y <= 10`
            let req_list = {
                let reqs = func.reqs.as_ref().unwrap();

                match reqs.deref() {
                    [] => unreachable!(),
                    [ref req] => format!("`{}`", req),
                    [init @ .., last] => {
                        let mut rs = format!("`{}`", &init[0]);

                        init[1..].iter().for_each(|r| {
                            write!(rs, ", `{}`", r).unwrap();
                        });

                        match init.len() {
                            1 => write!(rs, " and `{}`", last).unwrap(),
                            _ => write!(rs, ", and `{}`", last).unwrap(),
                        }

                        rs
                    }
                }
            };

            format!(
                "{} {} help: `{}` requires {}",
                spacing,
                Blue.paint("="),
                fancy_fn,
                req_list
            )
        };

        writeln!(msg, "{}", help_line).unwrap();

        // All of the lines that look like:
        // ```
        //   = note: `3 >= 5` is false
        // ```
        // or
        // ```
        //   = note: whether `z <= 3` cannot be determined
        // ```
        let notes = {
            // "  = note:"
            let pre = format!("{} {} note:", spacing, Blue.paint("="));

            proofs.iter().fold(String::new(), |mut s, (res, req)| {
                assert!(res != &ProofResult::True);

                let (before, after) = match res {
                    ProofResult::False => ("", "is false"),
                    // Undetermined
                    _ => ("whether ", "cannot be determined"),
                };

                writeln!(s, "{} {}`{}` {}", pre, before, req.pretty(file_str), after).unwrap();
                s
            })
        };

        // We don't use `writeln!` because `notes` ends in a newline
        write!(msg, "{}", notes).unwrap();

        msg
    }
}
