//! Error definitions for ast parsing

use crate::errors;
use crate::errors::PrettyError;
use crate::tokens::{Token, TokenKind};
use ansi_term::Color::{Blue, Red};
use std::fmt::Write;
use std::ops::Range;

/// Errors each have a kind and a context in which it occured. These can be combined with the
/// source token to create a hopefully ok error message.
#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub kind: Kind,
    pub context: Context,
    pub source: Source<'a>,
}

/// The source for a parsing error; either a single token or a range
#[derive(Debug, Copy, Clone)]
pub enum Source<'a> {
    Single(&'a Token<'a>),
    Range(&'a [Token<'a>]),
    /// EOF gives the index of the token if the function producing the error was called with a
    /// slice of tokens. Whenever this may be the case, this should be accounted for and replaced
    /// with one of the other two
    EOF,
    /// Indicates that the source occured at the end of a block token - any of `Parens`, `Curlys`,
    /// or `ProofLine`.
    End(&'a Token<'a>),
}

#[derive(Debug, Clone, Copy)]
pub enum Kind {
    /// This error is generated when a type ident is given where a name ident should have been.
    /// This didd contain a string, maybe useful for suggesting a valid name later on however now
    /// the Error type contains the token so it can be retrieved from that.
    TypeIdent,
    /// This error is generated when a NameIdent token was expected but another kind was given.
    ExpectingName,
    /// This error is generated when a Parens token was expected but another kind was given.
    ExpectingParens,
    /// This error is generated when a Curlys token was expected but another kind was given.
    ExpectingCurlys,
    ExpectingKeyword,
    ExpectingEquals,
    ExpectingExpr,
    ExpectingStmt,
    /// When a type is expected, the first token should be any of `TypeIdent`, `Parens`, or
    /// `Curlys`
    ExpectingType,
    ExpectingIdent,
    ExpectingColon,
    MalformedStructField,
    UnexpectedToken,

    /// An integer literal represents a value larger than `isize::MAX`, and so we cannot construct
    /// it
    IntegerValueTooLarge,

    /// An error resulting from proof statments. This occurs when two conditions were expected as
    /// part of a contract, but only one was given. It is possible that the user is missing the
    /// `require` keyword.
    SingleContractCondition,

    /// An error resulting from proof statments. This occurs when parsing a contract, which has
    /// conditions separated by `=>` tokens. There should only be two of these (so the value here
    /// will be ≥ 3)
    TooManyContractConditions(usize),

    /// A place where a proof condition expected to have a comparison operator but there was none
    /// found.
    CondWithoutCompareOp,

    /// A place where a proof condition has multiple comparison operators; e.g. `x < y < 5`
    ChainedComparison,

    /// A proof line was being parsed in a context where only lemmas are allowed
    ExpectingLemma,
}

#[derive(Debug, Clone, Copy)]
pub enum Context {
    NoContext,
    UnknownName,
    TopLevel,
    FnName,
    FnParam,
    FnParams,
    FnReturnType,
    FnBody,
    LetName,
    LetEquals,
    LetExpr,
    PrintExpr,
    AssignName,
    AssignExpr,
    BinOperLeft,
    BinOperRight,
    PrefixOp,
    ParseStmt,
    ParseAll,
    Struct,
    StructExpr,
    ProofStmt,
    ProofCond,
    ProofExpr,
}

impl<'a> Error<'a> {
    pub fn with_context(self, ctx: Context) -> Self {
        Self {
            context: ctx,
            ..self
        }
    }

    pub fn set_eof(mut errs: Vec<Self>, source: Source<'a>) -> Vec<Self> {
        errs.iter_mut().for_each(|e| {
            if let Source::EOF = e.source {
                e.source = source;
            }
        });
        errs
    }
}

impl PrettyError for Error<'_> {
    fn pretty_format(&self, file_str: &str, file_name: &str) -> String {
        use Kind::*;
        use Source::{End, Single, EOF};

        // Produces the description for a single token
        fn token_desc(this: &Error, token: &Token) -> String {
            use TokenKind::{
                Curlys, Fake, InvalidChar, Keyword, NameIdent, Num, Oper, Parens, ProofLine, Punc,
                Squares, TypeIdent,
            };

            match token.kind {
                Keyword(kwd) => format!("keyword '{}'", kwd),
                TypeIdent(s) => format!("type identifier '{}'", s),
                NameIdent(s) => format!("identifier '{}'", s),
                Num(s) => format!("numeric literal '{}'", s),

                Parens(_) => "open parenthesis '('".into(),
                Curlys(_) => "open curly-braces '{'".into(),
                Squares(_) => "open square-brackets '['".into(),
                ProofLine(_) => "proof line".into(),

                // These two are deliberately left as not *quite* as descriptive - there's some
                // mixing between these two categories, so they're just left here as generic
                // "tokens". It should be fine.
                Oper(o) => format!("token {}", o),
                Punc(p) => format!("token {}", p),

                // These two shouldn't occur at this point - parsing shouldn't have been given
                // these sorts of tokens
                InvalidChar(_) | Fake => panic!(
                    "unexpected token {:?} in source for error {:?}",
                    token, this
                ),
            }
        }

        // We'll build the error message in two parts. The first part is the main error message,
        // which is determined by the error kind and context; the second is the main body, which is
        // given only by the source.

        // Pull yourself up by the bootstraps!
        let mut help = None;

        let (main_msg, needs_found): (&str, bool) = match (&self.kind, &self.context) {
            (TypeIdent, _) => ("expected type identifier", true),
            (ExpectingName, _) => ("expected idendentifier", true),
            (ExpectingParens, _) => ("expected parenthetical", true),
            (ExpectingCurlys, _) => ("expected curly braces", true),
            (ExpectingKeyword, _) => ("expected keyword", true),
            (ExpectingEquals, _) => ("expected '='", true),
            (ExpectingExpr, _) => ("expected expression", true),
            (ExpectingStmt, _) => ("expected statement", true),
            (ExpectingType, _) => ("expected type", true),
            (ExpectingIdent, _) => ("expected identifier", true),
            (ExpectingColon, _) => ("expected ':'", true),
            (MalformedStructField, _) => ("malformed struct field", false),
            (UnexpectedToken, _) => ("unexpected token", true),
            (IntegerValueTooLarge, _) => ("integer literal too large", false),
            (SingleContractCondition, _) => {
                // TODO: It would be great if this actually demonstrated to the user how to change
                // their code to make it work
                help = Some("help: to make a requirement, use the `require` keyword");
                ("only single contract condition found", false)
            }
            (TooManyContractConditions(_), _) => ("cannot chain contract implication", false),
            (CondWithoutCompareOp, _) => ("expected comparison operator", false),
            // TODO: It would be great if this actually demonstrated to the user how to change
            // their code to make it work
            (ChainedComparison, _) => ("cannot chain comparison operators", false),
            (ExpectingLemma, _) => {
                help = Some("note: only lemmas are allowed within function bodies");
                ("expected lemma", false)
            }
        };

        // `byte_range` will be `Some` if the error was not at EOF, otherwise None
        let (byte_range, found): (Option<Range<usize>>, String) = match &self.source {
            Single(t) => (Some(t.byte_range().unwrap()), token_desc(self, t)),
            Source::Range([t]) => (Some(t.byte_range().unwrap()), token_desc(self, t)),
            Source::Range([t, .., end]) => (
                Some(t.byte_range().unwrap().start..end.byte_range().unwrap().end),
                token_desc(self, t),
            ),
            Source::Range([]) => panic!("AST error source with empty range: {:?}", self),
            End(t) => {
                let ch = match t.kind {
                    TokenKind::Parens(_) => "')'",
                    TokenKind::Curlys(_) => "'}'",
                    TokenKind::Squares(_) => "']'",
                    TokenKind::ProofLine(_) => "newline",
                    _ => panic!(
                        "end source specified for non-block token for error {:?}",
                        self
                    ),
                };

                let idx = t.byte_range().unwrap().end - 1;
                (Some(idx..idx + 1), ch.into())
            }
            EOF => (None, "end of file".into()),
        };

        let (mut msg, spacing) = if let Some(range) = byte_range {
            // ^ The error wasn't at EOF

            let (context, spacing) = errors::context_lines_and_spacing(range, file_str, file_name);
            let msg = if needs_found {
                format!(
                    "{}: {}, found {}\n{}\n",
                    Red.paint("error"),
                    main_msg,
                    found,
                    context,
                )
            } else {
                format!("{}: {}\n{}\n", Red.paint("error"), main_msg, context,)
            };

            (msg, spacing)
        } else {
            // The error was at EOF. We'll display one extra line for context
            let lines = file_str.lines().collect::<Vec<_>>();
            let last_line_no = lines.len() - 1;

            let mut msg = if needs_found {
                format!("{}: {}, found {}\n", Red.paint("error"), main_msg, found)
            } else {
                format!("{}: {}\n", Red.paint("error"), main_msg)
            };

            // Add a little context line
            let width = last_line_no.to_string().len();
            let spacing = " ".repeat(width);
            writeln!(msg, "{}{} {}:EOF", spacing, Blue.paint("-->"), file_name).unwrap();

            let snd_last = lines.len().checked_sub(2).map(|i| lines[i]);

            if let Some(line) = snd_last {
                writeln!(
                    msg,
                    "{:>width$} {} {}",
                    last_line_no - 1,
                    Blue.paint("|"),
                    line,
                    width = width
                )
                .unwrap();
            }

            let last_line = lines.last().unwrap();
            writeln!(msg, "{} {} {}", last_line_no, Blue.paint("|"), last_line).unwrap();
            writeln!(
                msg,
                "{} {} {}",
                spacing,
                Blue.paint("|"),
                errors::underline(&last_line, last_line.len()..last_line.len() + 1)
            )
            .unwrap();

            (msg, spacing)
        };

        // And finally, we add the help messages
        if let Some(help) = help {
            writeln!(msg, "{} {} {}", spacing, Blue.paint("="), help).unwrap();
        }

        msg
    }
}
