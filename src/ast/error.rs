//! Error definitions for ast parsing

use crate::errors;
use crate::errors::PrettyError;
use crate::tokens::{Token, TokenKind};
use ansi_term::Color::{Blue, Red};
use std::fmt::Write;
use std::ops::Range;
use unicode_width::UnicodeWidthStr;

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
    /// The reserved return identifier '_' was used as a normal identifier, outside of a proof
    /// statment.
    ReturnIdent,
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

        let (main_msg, display_found): (&str, bool) = match (&self.kind, &self.context) {
            (TypeIdent, _) => ("expected type identifier", true),
            (ExpectingName, _) => ("expected idendentifier", true),
            (ReturnIdent, _) => {
                help = Some("note: the identifier '_' is only allowed in proof contracts, to represent the return value");
                ("invalid usage of reserved identifier '_'", false)
            }
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
        let (mut byte_range, found): (Option<Range<usize>>, String) = match &self.source {
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

        // We'll generate the first line of the message, which depends on whether we want to
        // display the token that was found at the error point
        let mut msg = if display_found {
            format!("{}: {}, found {}\n", Red.paint("error"), main_msg, found)
        } else {
            format!("{}: {}\n", Red.paint("error"), main_msg)
        };

        // Collect the lines of the file, so we can grab some additional context for the message
        let lines = file_str.lines().collect::<Vec<_>>();

        let (line_no, col_no) = match &mut byte_range {
            None => (lines.len() - 1, None),
            Some(range) => {
                let offset = |line: &&str| {
                    (*line as *const str as *const u8 as usize)
                        - (file_str as *const str as *const u8 as usize)
                };

                let line_no = lines
                    .binary_search_by_key(&range.start, offset)
                    .unwrap_or_else(|x| x - 1);

                let line_offset = offset(&lines[line_no]);

                let col_no = UnicodeWidthStr::width(
                    &lines[line_no][..range.start - offset(&lines[line_no])],
                );

                range.start -= line_offset;
                range.end -= line_offset;

                (line_no, Some(col_no))
            }
        };

        let width = match lines.get(line_no + 1) {
            None => (line_no + 1).to_string().len(),
            Some(_) => (line_no + 2).to_string().len(),
        };

        let spacing = " ".repeat(width);
        match col_no {
            Some(c) => writeln!(
                msg,
                "{}{} {}:{}:{}",
                spacing,
                Blue.paint("-->"),
                file_name,
                line_no + 1,
                c + 1
            )
            .unwrap(),
            None => writeln!(msg, "{}{} {}:EOF", spacing, Blue.paint("-->"), file_name).unwrap(),
        }

        let filler_line = format!("{} {}", spacing, Blue.paint("|"));

        writeln!(msg, "{}", filler_line).unwrap();

        if let Some(pre) = line_no.checked_sub(1) {
            writeln!(
                msg,
                "{:>width$} {} {}",
                pre + 1,
                Blue.paint("|"),
                lines[pre].replace('\t', "    "),
                width = width,
            )
            .unwrap();
        }

        let line = lines[line_no];
        let mut line_range = match byte_range {
            Some(range) => range,
            // The selected area will be the end of the file, and this line is the last in the
            // file. So all we need to do is to give the end of the line as the range
            None => (line.len()..line.len() + 1),
        };

        let line = errors::replace_tabs(line, Some(&mut line_range));

        writeln!(
            msg,
            "{:>width$} {} {}",
            line_no + 1,
            Blue.paint("|"),
            line,
            width = width
        )
        .unwrap();
        writeln!(
            msg,
            "{} {} {}",
            spacing,
            Blue.paint("|"),
            Red.paint(errors::underline(&line, line_range))
        )
        .unwrap();

        if let Some(post_line) = lines.get(line_no + 1) {
            writeln!(
                msg,
                "{:>width$} {} {}",
                line_no + 2,
                Blue.paint("|"),
                post_line.replace('\t', "    "),
                width = width
            )
            .unwrap();
        }

        if let Some(help) = help {
            // A little bit more padding if we have something else to say
            writeln!(msg, "{}", filler_line).unwrap();
            writeln!(msg, "{} {} {}", spacing, Blue.paint("="), help).unwrap();
        }

        msg
    }
}
