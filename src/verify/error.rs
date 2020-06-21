//! Error definitions for verification

use super::Func;
use crate::ast::{proof::Condition, Ident, Item, ItemKind::FnDecl, Node};
use crate::errors::{
    context_lines, context_lines_and_spacing, info_lines, line_info, replace_tabs, underline,
    PosInfo, PrettyError,
};
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
        fn_name: &'a str,
    },
    VariableNotFound,
    /// A field access was attempted on an expression that was not a struct. The source should be
    /// the *only* the expression that produced the struct
    AccessFieldOnNotStruct {
        /// The type that was expected to be a struct
        typ: Type<'a>,
        /// The field that was being accessed
        field_name: Ident<'a>,
    },
    /// A struct did not have a field with the name that was being accessed. The source should be
    /// the entirety of the expression
    NoStructFieldWithName {
        /// The name that wasn't found
        missing: Ident<'a>,
        /// The struct type that was expected to have the field
        typ: Type<'a>,
    },
    TypeMismatch {
        expected: Vec<Type<'a>>,
        found: Type<'a>,
    },
    /// Indicates that the return identifier "_" appeared somewhere in a proof statement it wasn't
    /// allowed
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
    /// This indicates that the *result* of a lemma could not be proven with whatever was given (or
    /// not).
    ///
    /// The source should give the entirety of the lemma statement.
    FailedLemma {
        /// The assumed requirements under which the lemma failed. This will be None if the lemma
        /// failed under the base prover. The Node should give the source for the requirements.
        assumption: Option<Node<'a>>,

        /// The "proof" conditions for the lemma, if they were available
        proof: &'a [Condition<'a>],

        /// For use when `assumption` and `proof` are None/empty - i.e. when the base prover failed
        /// on a proof with no preconditions. This indicates that there were other provers available
        /// that *might* have been able to prove this, had the proof been given explicitly
        /// (i.e. with `proof` non-empty).
        ///
        /// This might be changed in the future to explicitly record if other provers *were* able to
        /// prove it.
        other_assumptions: bool,

        /// The results of the lemma that we failed to prove, along with their results
        failed: Vec<(ProofResult, Requirement<'a>)>,
    },
    /// This indicates that the "proof" portion of a lemma could not be satisfied by any prover
    InvalidLemmaProof {
        failed: Vec<(ProofResult, Requirement<'a>)>,

        /// This carries the same meaning as above, for `FailedLemma`
        other_assumptions: bool,
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
    LemmaStmt,
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
        use Kind::*;

        match &self.kind {
            ItemConflict(fst, snd) => Error::format_item_conflict(fst, snd, file_str, file_name),
            FunctionNotFound { name } => {
                Error::format_function_not_found(name, &self.source, file_str, file_name)
            }
            FunctionMustBeName => {
                Error::format_function_must_be_name(&self.source, file_str, file_name)
            }
            IncorrectNumberOfArgs {
                fn_name,
                func,
                given,
            } => Error::format_incorrect_number_of_args(
                *given,
                fn_name,
                func,
                &self.source,
                file_str,
                file_name,
            ),
            VariableNotFound => Error::format_variable_not_found(&self.source, file_str, file_name),
            AccessFieldOnNotStruct { typ, field_name } => Error::format_access_field_on_not_struct(
                typ,
                field_name,
                &self.source,
                file_str,
                file_name,
            ),
            NoStructFieldWithName { missing, typ } => Error::format_no_struct_field_with_name(
                missing,
                typ,
                &self.source,
                file_str,
                file_name,
            ),
            TypeMismatch { expected, found } => {
                Error::format_type_mismatch(expected, found, &self.source, file_str, file_name)
            }
            MisplacedReturnIdent => {
                Error::format_misplaced_return_ident(&self.source, file_str, file_name)
            }
            FeatureNotAllowed { description } => {
                Error::format_feature_not_allowed(description, &self.source, file_str, file_name)
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
            FailedLemma {
                assumption,
                proof,
                other_assumptions,
                failed,
            } => Error::format_failed_lemma(
                failed,
                *assumption,
                proof,
                *other_assumptions,
                self.source,
                file_str,
                file_name,
            ),
            InvalidLemmaProof {
                failed,
                other_assumptions,
            } => Error::format_invalid_lemma_proof(
                failed,
                *other_assumptions,
                self.source,
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
                pre_source.clone(),
                post_source.clone(),
                self.source.clone(),
                file_str,
                file_name,
            ),
            InvalidLemmaProof { .. } => {
                format!("Error message currently unimplemented:\n{:?}\n", self)
            }
        }
    }
}

fn write_proof_notes(
    msg: &mut String,
    spacing: &str,
    failed: &[(ProofResult, Requirement)],
    file_str: &str,
) {
    for (res, req) in failed {
        assert!(res != &ProofResult::True);

        let (before, after) = match res {
            ProofResult::False => ("", "is false"),
            // Undetermined
            _ => ("whether ", "cannot be determined"),
        };

        writeln!(
            msg,
            "{} {} note: {}`{}` {}",
            spacing,
            Blue.paint("="),
            before,
            req.pretty(file_str),
            after
        )
        .unwrap();
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

        let ctx = |node: Node| {
            let byte_range = node.byte_range();
            let (line_no, col_no, line_offset, _, line) = line_info(file_str, byte_range.start);

            let mut line_range = {
                let start = byte_range.start - line_offset;
                let end = byte_range.end - line_offset;
                start..end
            };

            // handle tabs
            let line = replace_tabs(line, Some(&mut line_range));

            (line_no, col_no, line, line_range)
        };

        let (fst_line_no, fst_col_no, fst_line, fst_line_range) = ctx(fst_name.node());
        let (snd_line_no, snd_col_no, snd_line, snd_line_range) = ctx(snd_name.node());

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
            Red.paint(underline(&snd_line, snd_line_range))
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
            Blue.paint(underline(&fst_line, fst_line_range))
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
            context_lines(source.byte_range(), file_str, file_name)
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
            context_lines(source.byte_range(), file_str, file_name)
        )
    }

    fn format_incorrect_number_of_args(
        given: usize,
        fn_name: &str,
        func: &Func,
        source: &Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        // This error message looks something like:
        // ```
        // error: incorrect number of arguments to function 'foo'
        //   --> src/test_input.tc:24:10
        //    |
        // 24 |     print foo(x);
        //    |              ^^^
        //    = help: expected two arguments, found one
        // ```

        let mut msg = format!(
            "{}: incorrect number of arguments to function '{}'\n",
            Red.paint("error"),
            fn_name
        );

        let (context, spacing) =
            context_lines_and_spacing(source.byte_range(), file_str, file_name);

        // We'll provide words for the first few cases, but not in general.
        let expected_args = match func.params.len() {
            0 => "no arguments".into(),
            1 => "one argument".into(),
            2 => "two arguments".into(),
            3 => "three arguments".into(),
            4 => "four arguments".into(),
            n => format!("{} arguments", n),
        };

        let found_args = match given {
            0 => "none".into(),
            1 => "one".into(),
            2 => "two".into(),
            3 => "three".into(),
            4 => "four".into(),
            n => n.to_string(),
        };

        writeln!(
            msg,
            "{}{} {} help: expected {}, found {}",
            context,
            spacing,
            Blue.paint("="),
            expected_args,
            found_args,
        )
        .unwrap();

        msg
    }

    fn format_variable_not_found(source: &Node, file_str: &str, file_name: &str) -> String {
        // This error message looks like:
        // ```
        // error: variable 'w' not found
        //   --> src/test_input.tc:24:11
        //    |
        // 24 |     print foo(w, 2);
        //    |               ^
        // ```

        format!(
            "{}: variable '{}' not found\n{}",
            Red.paint("error"),
            &file_str[source.byte_range()],
            context_lines(source.byte_range(), file_str, file_name)
        )
    }

    fn format_access_field_on_not_struct(
        typ: &Type,
        field: &Ident,
        struct_expr: &Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        // FIXME: Actual message
        //
        // This error is *really* a type mismatch... most of the time. So we treat it as such.
        // It looks something like this:
        // ```
        // error: type mismatch: expected struct `{ foo: _, .. }`, found `int`
        //   --> src/test_input.tc:11:1
        //    |
        // 11 |     bar(x, y, 3).foo
        //    |     ^^^^^^^^^^^^
        // ```

        format!(
            "{}: type mismatch: expected struct `{{ {}: _, .. }}`, found `{}`\n{}",
            Red.paint("error"),
            field.name,
            typ,
            context_lines(struct_expr.byte_range(), file_str, file_name),
        )
    }

    fn format_no_struct_field_with_name(
        missing: &Ident,
        typ: &Type,
        expr: &Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        // This error looks like:
        // ```
        // error: no field 'hello' on struct `{ x: int, y: int, z: bool }`
        //   --> src/test_input.tc:30:4
        //    |
        // 30 |         b: my_struct.world.hello,
        //    |            ^^^^^^^^^^^^^^^^^^^^^
        // ```

        format!(
            "{}: no field '{}' on struct `{}`\n{}",
            Red.paint("error"),
            missing.name,
            typ,
            context_lines(expr.byte_range(), file_str, file_name),
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

        // A helper string to represent the type(s) that was/were expected:
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
            context_lines(source.byte_range(), file_str, file_name),
        )
    }

    fn format_misplaced_return_ident(source: &Node, file_str: &str, file_name: &str) -> String {
        // This error message looks like:
        // ```
        // error: misplaced return identifier
        //   --> src/test_input.tc:14:20
        //    |
        // 14 | # require y >= 0 + _
        //    |                    ^
        //    = note: the identifier '_' is used to signify the return value in proof contracts
        // ```

        let (context, spacing) =
            context_lines_and_spacing(source.byte_range(), file_str, file_name);
        let note =
            "note: the identifier '_' is used to signify the return value in proof contracts";
        format!(
            "{}: misplaced return identifier\n{}{} {} {}\n",
            Red.paint("error"),
            context,
            spacing,
            Blue.paint("="),
            note,
        )
    }

    fn format_feature_not_allowed(
        description: &str,
        source: &Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        // This error will look something like:
        // ```
        // error: feature not currently available
        //  --> src/test_input.tc:7:11
        //   |
        // 7 | # require x >= 1 || x <= 1
        //   |           ^^^^^^^^^^^^^^^^
        //   = note: logical OR is currently not allowed in proof statements
        // ```
        // where `description` is the portion after 'note: '

        let (context, spacing) =
            context_lines_and_spacing(source.byte_range(), file_str, file_name);
        format!(
            "{}: feature not yet available\n{}{} {} note: {}\n",
            Red.paint("error"),
            context,
            spacing,
            Blue.paint("="),
            description,
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
        let (context_lines, spacing) =
            context_lines_and_spacing(source.byte_range(), file_str, file_name);
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

    fn format_failed_lemma(
        failed: &[(ProofResult, Requirement)],
        assumption: Option<Node>,
        proof: &[Condition],
        other_assumptions: bool,
        stmt_source: Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        // This error message has a few different versions, depending on how exactly the lemma
        // failed.
        //
        // `proof` indicates the proof that was used, and - if present - `assumption` gives the
        // source of the assumption satisfying the proof, if the base prover was unable to.

        let lines = file_str.lines().collect::<Vec<_>>();

        let assumption = assumption.map(|a| info_lines(a.byte_range(), &lines));
        let stmt = info_lines(stmt_source.byte_range(), &lines);

        let width = (stmt.line_idx + 1).to_string().len();
        let spacing = " ".repeat(width);

        let mut msg = format!("{}: failed to prove lemma\n", Red.paint("error"));

        // write the context line:
        writeln!(
            msg,
            "{}{} {}:{}:{}",
            spacing,
            Blue.paint("-->"),
            file_name,
            stmt.line_idx + 1,
            stmt.col_idx + 1
        )
        .unwrap();

        // Just a blank line for looks
        writeln!(msg, "{} {}", spacing, Blue.paint("|")).unwrap();

        // If there was an assumption, we'll display that bit first
        if let Some(ass) = assumption.as_ref() {
            writeln!(
                msg,
                "{:>width$} {} {}",
                ass.line_idx + 1,
                Blue.paint("|"),
                ass.line,
                width = width
            )
            .unwrap();
            writeln!(
                msg,
                "{} {} {}",
                spacing,
                Blue.paint("|"),
                Blue.paint(underline(&ass.line, ass.line_range.clone()))
            )
            .unwrap();
        }

        // Now we display the actual lemma that failed
        writeln!(
            msg,
            "{:>width$} {} {}",
            stmt.line_idx + 1,
            Blue.paint("|"),
            stmt.line,
            width = width
        )
        .unwrap();
        writeln!(
            msg,
            "{} {} {}",
            spacing,
            Blue.paint("|"),
            Red.paint(underline(&stmt.line, stmt.line_range.clone()))
        )
        .unwrap();

        // And now for the help messages
        if proof.is_empty() {
            // If there wasn't a proof supplied, but some assumptions might have been able to prove it,
            // the user should know that.
            if other_assumptions {
                writeln!(
                    msg,
                    "{} {} note: lemmas without proof must have valid preconditions in all cases",
                    spacing,
                    Blue.paint("="),
                )
                .unwrap();
                writeln!(
                    msg,
                    "{} {} help: to restrict this only to certain contract assumptions,\n{}   {}",
                    spacing,
                    Blue.paint("="),
                    spacing,
                    "      add proof elements with `==>`"
                )
                .unwrap();
            } else {
                // We know that there wasn't an assumption, so there isn't much else we can provide
                // to the user here.
                //
                // It's mostly plain and simple; we just couldn't do the proof. This is a possible
                // area of improvement for the future.
            }
        } else {
            // There were proof conditions provided, but we still weren't able to prove the lemma
            if assumption.is_some() {
                writeln!(
                    msg,
                    "{} {} note: the conditions require the assumption given above",
                    spacing,
                    Blue.paint("="),
                )
                .unwrap();
            } else {
                // No assumptions, so we failed to prove the lemma with the main prover
                writeln!(
                    msg,
                    "{} {} note: the conditions were proven without any assumptions,\n{}   {}",
                    spacing,
                    Blue.paint("="),
                    spacing,
                    "      but the result could not be proven",
                )
                .unwrap();
                if other_assumptions {
                    // TODO: This could specifically mention the provers that *are* able to solve
                    // it, if those were added to the information here
                    writeln!(
                        msg,
                        "{} {} help: try making the conditions more restrictive so that it is\n{}   {}",
                        spacing,
                        Blue.paint("="),
                        spacing,
                        "      only attempted in fully valid contexts",
                    )
                    .unwrap();
                }
            }
        }

        // Final help messages - these will give the specific results for each requirement
        write_proof_notes(&mut msg, &spacing, failed, file_str);

        msg
    }

    fn format_invalid_lemma_proof(
        failed: &[(ProofResult, Requirement)],
        other_assumptions: bool,
        stmt_source: Node,
        file_str: &str,
        file_name: &str,
    ) -> String {
        let mut msg = if other_assumptions {
            format!(
                "{}: lemma conditions cannot be verified under any assumptions\n",
                Red.paint("error")
            )
        } else {
            format!(
                "{}: lemma conditions cannot be verified\n",
                Red.paint("error")
            )
        };

        let (context, spacing) =
            context_lines_and_spacing(stmt_source.byte_range(), file_str, file_name);

        // We only write! not writeln! because `context` is guaranteed to have a trailing newline
        write!(msg, "{}", context).unwrap();

        writeln!(
            msg,
            "{} {} note: lemma conditions must be valid under at least one assumption if present",
            spacing,
            Blue.paint("="),
        )
        .unwrap();

        write_proof_notes(&mut msg, &spacing, failed, file_str);

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

        let lines = file_str.lines().collect::<Vec<_>>();
        let info = |node: Node| info_lines(node.byte_range(), &lines);

        let req = info(post_source);
        let func = info(fn_name_source);
        let ret = info(ret_ident.node());

        let pre_ret_line = match ret.line_idx - 1 <= func.line_idx {
            true => None,
            false => Some(lines[ret.line_idx - 1]),
        };

        let end_fn = {
            let (line_idx, _, _, _, line) = line_info(file_str, fn_source.byte_range().end);
            let line = replace_tabs(line, None);

            // `col_idx` and `line_range` are just filler values because we don't actually need
            // them.
            PosInfo {
                line_idx,
                col_idx: 0,
                line,
                line_range: 0..1,
            }
        };

        let pad_size = (end_fn.line_idx + 1).to_string().len();
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
            req.line_idx + 1,
            req.col_idx + 1
        )
        .unwrap();
        writeln!(
            msg,
            "{}{} {}:{}:{}",
            padding,
            Blue.paint("-->"),
            file_name,
            ret.line_idx + 1,
            ret.col_idx + 1
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
            req.line_idx + 1,
            Blue.paint("|"),
            req.line,
            width = pad_size
        )
        .unwrap();
        writeln!(
            msg,
            "{} {}",
            filler_line,
            Blue.paint(underline(&req.line, req.line_range))
        )
        .unwrap();

        // Before we print the function definition, we might want to add a `...` before it. We'll
        // do that if the function definition doesn't immediately follow the proof line.
        if req.line_idx + 1 != func.line_idx {
            writeln!(msg, "{}", dots_line).unwrap();
        }

        // And now for the function definition. This condition should never be true, but it's good
        // to check anyways.
        if func.line_idx != ret.line_idx {
            writeln!(
                msg,
                "{:>width$} {} {}",
                func.line_idx + 1,
                Blue.paint("|"),
                func.line,
                width = pad_size
            )
            .unwrap();
        }

        // Again with maybe dots between the function definition and return
        if func.line_idx + 2 < ret.line_idx {
            writeln!(msg, "{}", dots_line).unwrap();
        }

        // And now the line before the return
        if let Some(line) = pre_ret_line {
            writeln!(
                msg,
                "{:>width$} {} {}",
                // Exactly `line_idx` because we're one line before and `line_idx` starts at zero.
                ret.line_idx,
                Blue.paint("|"),
                replace_tabs(line, None),
                width = pad_size
            )
            .unwrap();
        }

        // And the return line, followed by a highlight
        writeln!(
            msg,
            "{:>width$} {} {}",
            ret.line_idx + 1,
            Blue.paint("|"),
            ret.line,
            width = pad_size
        )
        .unwrap();
        writeln!(
            msg,
            "{} {}",
            filler_line,
            Red.paint(underline(&ret.line, ret.line_range))
        )
        .unwrap();

        // And our final bit of source: The last line of the function. This - once again - might
        // need some dots to connect it
        if ret.line_idx + 1 < end_fn.line_idx {
            writeln!(msg, "{}", dots_line).unwrap();
        }

        if ret.line_idx != end_fn.line_idx {
            // No need to account for width here since this line has the longest number
            writeln!(
                msg,
                "{} {} {}",
                end_fn.line_idx + 1,
                Blue.paint("|"),
                end_fn.line,
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
        // This will not be present if the contract has no assumptions
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

        // Trailing notes about the proofs:
        write_proof_notes(&mut msg, &padding, proofs, file_str);

        // And then we're done!

        msg
    }
}
