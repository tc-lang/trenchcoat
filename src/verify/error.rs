//! Error definitions for verification

use super::Func;
use crate::ast::{Ident, Item, ItemKind::FnDecl, Node};
use crate::errors::{context_lines, context_lines_and_spacing, line_info, underline, PrettyError};
use crate::proof::{ProofResult, Requirement};
use crate::types::Type;
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
    /// A collection of proof requirements that didn't pass while attempting to uphold a contract
    /// The source should be the node representing the function definition
    FailedContract {
        fn_name: &'a str,
        failed: Vec<(ProofResult, Requirement<'a>)>,
        pre_source: Option<Node<'a>>,
        post_source: Node<'a>,
        /// The temporary variable corresponding to the final return value of the function
        ret_ident: Ident<'a>,
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
    fn pretty_format(&self, file_str: &str, file_name: &str) -> String {
        use Kind::{
            FailedContract, FailedProofs, FunctionMustBeName, FunctionNotFound, ItemConflict,
            TypeMismatch,
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
            FailedContract {
                fn_name,
                failed,
                pre_source,
                post_source,
                ret_ident,
            } => Error::format_failed_contract(
                failed,
                fn_name,
                ret_ident,
                *pre_source,
                *post_source,
                self.source,
                file_str,
                file_name,
            ),
            _ => format!("{:?}\n", self),
        }
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
            let (line_no, col_no, line_offset, _, line) = line_info(file_str, byte_range.start);

            let line_range = {
                let start = byte_range.start - line_offset;
                let end = byte_range.end - line_offset;
                start..end
            };

            (line_no, col_no, line, line_range)
        };

        let (snd_line_no, snd_col_no, snd_line, snd_line_range) = {
            let byte_range = snd_name.node().byte_range();
            let (line_no, col_no, line_offset, _, line) = line_info(file_str, byte_range.start);

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
            Red.paint(underline(snd_line, snd_line_range))
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
            Blue.paint(underline(fst_line, fst_line_range))
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
            context_lines(source, file_str, file_name)
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
            context_lines(source, file_str, file_name)
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
            context_lines(source, file_str, file_name),
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
        //    = note: `3 >= 5` is false
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
        //   = note: whether `z <= 3` cannot be determined
        //   = note: whether `3 + z <= 10` cannot be determined
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
        let (context_lines, spacing) = context_lines_and_spacing(source, file_str, file_name);
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

    fn format_failed_contract(
        proofs: &[(ProofResult, Requirement)],
        fn_name: &str,
        ret_ident: &Ident,
        pre_source: Option<Node>,
        post_source: Node,
        fn_source: Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        // This error message looks something like:
        // ```
        // error: proof contract is not upheld for function `foo`
        //   --> src/main.tc:10:13
        //   --> src/main.tc:35:19
        //    |
        // 10 | # x <= 4 => _ <= 5
        //    |             ^^^^^^
        // ...
        // 13 | fn foo(x: int) -> int {
        // ...
        // 34 |     let y = bar(x);
        // 35 |     x + y
        //    |     ^^^^^
        // 36 | }
        //    |
        //    = note: the contract assumes that `x <= 4`
        //    = note: whether `(x + y) <= 5` cannot be determined
        // ```

        // This error message is one of the more complicated ones.
        //
        // Because there's so much to do here, we'll sort out this message by breaking it apart into
        // pieces.

        let fn_name_source = match fn_source {
            Node::Item(item) => {
                let FnDecl { name, .. } = &item.kind;
                name.node()
            }
            _ => panic!(
                "non-item node as function source for failed contract error: {:?}",
                fn_source
            ),
        };

        let mut msg = format!(
            "{}: proof contract is not upheld for function `{}`\n",
            Red.paint("error"),
            fn_name
        );

        struct Info<'b> {
            line_no: usize,
            col_no: usize,
            line: &'b str,
            line_range: Range<usize>,
        }

        // A helper function for generating bits of information about the ranges around a given node.
        let info = |node: Node| -> Info {
            let byte_range = node.byte_range();
            let (line_no, col_no, line_offset, _, line) = line_info(file_str, byte_range.start);

            let line_range = {
                let start = byte_range.start - line_offset;
                let end = byte_range.end - line_offset;
                start..end
            };

            Info {
                line_no,
                col_no,
                line,
                line_range,
            }
        };

        let lines = file_str.lines().collect::<Vec<_>>();

        let req = info(post_source);
        let func = info(fn_name_source);
        let ret = info(ret_ident.node());

        let pre_ret_line = match ret.line_no - 1 <= func.line_no {
            true => None,
            false => Some(lines[ret.line_no - 1]),
        };

        let (end_fn_line_no, _, _, _, end_fn_line) =
            line_info(file_str, fn_source.byte_range().end);

        let pad_size = (end_fn_line_no + 1).to_string().len();
        let padding = " ".repeat(pad_size);

        // Write the first two context lines. In the example at the top of this function, these are
        // the following two lines:
        // ```
        //   --> src/main.tc:10:13
        //   --> src/main.tc:35:19
        // ```
        // They serve to indicate the relevant locations for the error
        writeln!(
            msg,
            "{}{} {}:{}:{}",
            padding,
            Blue.paint("-->"),
            file_name,
            req.line_no,
            req.col_no
        )
        .unwrap();
        writeln!(
            msg,
            "{}{} {}:{}:{}",
            padding,
            Blue.paint("-->"),
            file_name,
            ret.line_no,
            ret.col_no
        )
        .unwrap();

        let filler_line = format!("{} {}", padding, Blue.paint("|"));
        let dots_line = format!("{}", Blue.paint("..."));

        // There's a single filler line after the context
        writeln!(msg, "{}", filler_line).unwrap();

        // The next component is the highlighted selection of the requirement. This consists of two
        // lines - the first gives the line itself, and the second underlines the selection.
        writeln!(
            msg,
            "{:>width$} {} {}",
            req.line_no,
            Blue.paint("|"),
            req.line,
            width = pad_size
        )
        .unwrap();
        writeln!(
            msg,
            "{} {}",
            filler_line,
            Blue.paint(underline(req.line, req.line_range))
        )
        .unwrap();

        // Before we print the function definition, we might want to add a `...` before it. We'll
        // do that if the function definition doesn't immediately follow the proof line.
        if req.line_no + 1 != func.line_no {
            writeln!(msg, "{}", dots_line).unwrap();
        }

        // And now for the function definition. This condition should never be true, but it's good
        // to check anyways.
        if func.line_no != ret.line_no {
            writeln!(
                msg,
                "{:>width$} {} {}",
                func.line_no,
                Blue.paint("|"),
                func.line,
                width = pad_size
            )
            .unwrap();
        }

        // Again with maybe dots between the function definition and return
        if func.line_no + 2 < ret.line_no {
            writeln!(msg, "{}", dots_line).unwrap();
        }

        // And now the line before the return
        if let Some(line) = pre_ret_line {
            writeln!(
                msg,
                "{:>width$} {} {}",
                ret.line_no - 1,
                Blue.paint("|"),
                line,
                width = pad_size
            )
            .unwrap();
        }

        // And the return line, followed by a highlight
        writeln!(
            msg,
            "{:>width$} {} {}",
            ret.line_no,
            Blue.paint("|"),
            ret.line,
            width = pad_size
        )
        .unwrap();
        writeln!(
            msg,
            "{} {}",
            filler_line,
            Red.paint(underline(ret.line, ret.line_range))
        )
        .unwrap();

        // And our final bit of source: The last line of the function. This - once again - might
        // need some dots to connect it
        if ret.line_no + 1 < end_fn_line_no {
            writeln!(msg, "{}", dots_line).unwrap();
        }

        if ret.line_no != end_fn_line_no {
            // No need to account for width here since this line has the longest number
            writeln!(
                msg,
                "{} {} {}",
                end_fn_line_no,
                Blue.paint("|"),
                end_fn_line,
            )
            .unwrap();
        }

        // Now, all that we have left is for notes to the user. We'll add a filler line first, then
        // format the requirements as necessary.
        writeln!(msg, "{}", filler_line).unwrap();

        // First note:
        // ```
        //    = note: the contract assumes that `x <= 4`
        // ```
        // This  will not be present if the contract has no assumptions
        if let Some(pre_source) = pre_source {
            writeln!(
                msg,
                "{} {} note: the contract assumes that `{}`",
                padding,
                Blue.paint("="),
                &file_str[pre_source.byte_range()]
            )
            .unwrap();
        }

        // Trailing notes:
        for (res, req) in proofs {
            assert!(res != &ProofResult::True);

            let (before, after) = match res {
                ProofResult::False => ("", "is false"),
                // Undetermined
                _ => ("whether ", "cannot be determined"),
            };

            writeln!(
                msg,
                "{} {} note: {}`{}` {}",
                padding,
                Blue.paint("="),
                before,
                req.pretty(file_str),
                after
            )
            .unwrap();
        }

        // And then we're done!

        msg
    }
}
