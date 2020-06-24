use crate::error::{self, Builder as ErrorBuilder, SourceRange, ToError};
use std::ops::Range;

// Note: tokens might not be strictly non-overlapping. This can occur in certain error cases, where
// we might have string literals / block comments inside others
pub fn tokenize<'a>(file_str: &'a str) -> Vec<Result<Token<'a>, Invalid<'a>>> {
    use TokenKind::*;

    let mut tokens = Vec::new();

    // idx gives the start of the current character
    let mut ch = match char_at(file_str, 0) {
        Some(c) => c,
        None => return Vec::new(),
    };
    let mut byte_idx = 0;

    // TODO: Because we aren't really allowing non-ascii characters in the source - outside of
    // string/char literals - we can actually optimize this to only use individual bytes.
    // Realistically, this isn't going to be the slow part of the compiler, so it's probably fine.

    let mut next_idx: usize = byte_idx + ch.len_utf8();
    let mut next_ch: Option<_> = char_at(file_str, next_idx);

    let mut last_invalid: Option<usize> = None;

    macro_rules! valid_char {
        () => {{
            if let Some(idx) = last_invalid {
                tokens.push(Err(Invalid {
                    src: &file_str[idx..byte_idx],
                    incomplete: None,
                }));
            }
        }};
    }

    macro_rules! end {
        ($kind:expr, $end_idx:expr) => {{
            valid_char!();

            let end = $end_idx;
            tokens.push(Ok(Token {
                src: &file_str[byte_idx..end],
                kind: $kind,
            }));

            match char_at(file_str, end) {
                Some(c) => ch = c,
                None => break,
            }
            byte_idx = end;
            next_idx = byte_idx + ch.len_utf8();
            next_ch = char_at(file_str, next_idx);
            continue;
        }};
    }

    macro_rules! single {
        ($kind:expr) => {{
            valid_char!();
            tokens.push(Ok(Token {
                src: &file_str[byte_idx..next_idx],
                kind: $kind,
            }));
        }};
    }

    loop {
        match ch {
            '/' if next_ch == Some('/') => {
                end!(LineComment, find_newline_or_eof(file_str, next_idx + 1));
            }
            '/' if next_ch == Some('*') => {
                valid_char!();

                // The reason we might have intermediate failures here is because the user might
                // not have closed a nested block comment or string literal.
                //
                // Any nested block comments/string literals that are properly terminated won't
                // have been added, so all of these are *actually* errors that we'll add to the
                // list of returns for collection later.
                match consume_block_comment(file_str, byte_idx) {
                    Ok(end) => end!(BlockComment, end),
                    Err(mid_fails) => {
                        // If there was no end index, we've already gone through the rest of the
                        // file, so we'll just add the error(s) to the list and break (which will
                        // return)
                        //
                        // We don't need to add any errors *here* because it's accounted for
                        tokens.extend(mid_fails.into_iter().map(Err));
                        break;
                    }
                }
            }
            '"' => {
                valid_char!();

                match consume_string_lit(file_str, next_idx) {
                    Some(end) => end!(Literal(LiteralKind::String), end),
                    None => {
                        // There wasn't a closing quote, so we'll construct an error and exit by
                        // breaking out of the loop
                        tokens.push(Err(Invalid {
                            src: &file_str[byte_idx..],
                            incomplete: Some(IncompleteKind::StringLiteral),
                        }));
                        break;
                    }
                }
            }
            '\'' => {
                valid_char!();

                match consume_single_quote(file_str, byte_idx) {
                    Some(end) => end!(Literal(LiteralKind::Char), end),
                    // TODO: This isn't perfect - the user might get severely mediocre error
                    // messages when writings something like:
                    //   'foo'
                    // or
                    //   bar('x)
                    // These are both cases that are equally reasonable mistakes (the first being
                    // quotation style, the second being a typo) and so we should ideally provide
                    // reasonable/helpful errors.
                    //
                    // As of writing, I'm not sure what the best way to do this is - further
                    // research might be required.
                    None => {
                        if last_invalid.is_none() {
                            last_invalid = Some(byte_idx);
                        }
                    }
                }
            }
            _ if is_whitespace(ch) => {
                end!(Whitespace, find_end_whitespace(file_str, next_idx));
            }
            '_' | 'a'..='z' | 'A'..='Z' => {
                end!(Ident, find_end_ident(file_str, next_idx));
            }

            '0'..='9' => {
                end!(
                    Literal(LiteralKind::Int),
                    find_end_digits(file_str, next_idx)
                );
            }

            '(' => single!(OpenParen),
            ')' => single!(CloseParen),
            '{' => single!(OpenCurly),
            '}' => single!(CloseCurly),
            '[' => single!(OpenSquare),
            ']' => single!(CloseSquare),
            ';' => single!(Semi),
            ':' => single!(Colon),
            ',' => single!(Comma),
            '.' => single!(Dot),
            '=' => single!(Eq),
            '<' => single!(Lt),
            '>' => single!(Gt),
            '&' => single!(And),
            '|' => single!(Pipe),
            '!' => single!(Not),
            '+' => single!(Plus),
            '-' => single!(Minus),
            '*' => single!(Star),
            '/' => single!(Slash),

            // Final case - if we couldn't match any of the characters we wanted, we'll mark this
            // as an invalid character
            _ => {
                if last_invalid.is_none() {
                    last_invalid = Some(byte_idx);
                }
            }
        }

        ch = match next_ch {
            Some(c) => c,
            None => break,
        };
        byte_idx = next_idx;

        next_idx = byte_idx + ch.len_utf8();
        next_ch = char_at(file_str, next_idx);
    }

    // Close out any trailing invalid tokens
    valid_char!();

    tokens
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    src: &'a str,
    kind: TokenKind,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    // Multi-character tokens:
    LineComment,  // Two slashes, followed by anything until a newline
    BlockComment, // Block comments allow nesting, and include string literals
    /// Any continued amount of whitespace
    Whitespace,
    Ident,
    Literal(LiteralKind),

    // Single-character tokens
    OpenParen,   // "("
    CloseParen,  // ")"
    OpenCurly,   // "{"
    CloseCurly,  // "}"
    OpenSquare,  // "["
    CloseSquare, // "]"
    Semi,        // ";"
    Colon,       // ":"
    Comma,       // ","
    Dot,         // "."
    Eq,          // "="
    Lt,          // "<"
    Gt,          // ">"
    And,         // "&"
    Pipe,        // "|"
    Not,         // "!"
    Plus,        // "+"
    Minus,       // "-"
    Star,        // "*"
    Slash,       // "/"
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LiteralKind {
    Char,
    Int,
    String,
}

/// An invalid character sequence in the source file
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Invalid<'a> {
    src: &'a str,
    incomplete: Option<IncompleteKind>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum IncompleteKind {
    BlockComment,
    StringLiteral,
}

/// Returns the character at a given index in the string, if it's within the range of the string.
fn char_at(s: &str, idx: usize) -> Option<char> {
    let ch = s.get(idx..)?.chars().next()?;
    Some(ch)
}

/// Returns whether the given character is qualified as whitespace. This is intentionally made more
/// restrictive than the ASCII whitespace definition, as certain characters (e.g. vertical tab)
/// should never appear in source files.
///
/// Currently the only characters allowed as whitespace are: spaces, tabs, newlines, and carriage
/// returns.
fn is_whitespace(c: char) -> bool {
    match c {
        ' ' | '\r' | '\n' | '\t' => true,
        _ => false,
    }
}

/// A companion function to [`is_whitespace`] that returns whether a given byte represents a
/// whitespace character.
///
/// [`is_whitespace`]: fn.is_whitespace.html
fn is_whitespace_byte(b: u8) -> bool {
    match b {
        b' ' | b'\r' | b'\n' | b'\t' => true,
        _ => false,
    }
}

/// Returns the byte index of the next newline character, startring from `idx`, if there is one.
/// Otherwise returns the length of the string.
fn find_newline_or_eof(s: &str, idx: usize) -> usize {
    s.as_bytes()[idx..]
        .iter()
        .position(|&b| b == b'\n')
        .map(|i| idx + i)
        .unwrap_or(s.len())
}

/// Returns the starting byte index of the first non-whitespace character, including and after
/// `idx`. If all of the remaining characters are whitespace, the length of the string will be
/// returned.
fn find_end_whitespace(s: &str, idx: usize) -> usize {
    s.as_bytes()[idx..]
        .iter()
        .position(|&b| !is_whitespace_byte(b))
        .map(|i| idx + i)
        .unwrap_or(s.len())
}

/// Returns the starting byte index of the first non-digit (0-9) character, including and after
/// `idx`. If all of the remaining characters are digits, the end of the string will be returned.
fn find_end_digits(s: &str, idx: usize) -> usize {
    s.as_bytes()[idx..]
        .iter()
        .position(|b| !b.is_ascii_digit())
        .map(|i| idx + i)
        .unwrap_or(s.len())
}

fn find_end_ident(s: &str, idx: usize) -> usize {
    fn is_trailing_ident_char(b: u8) -> bool {
        match b {
            b'_' | b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' => true,
            _ => false,
        }
    }

    s.as_bytes()[idx..]
        .iter()
        .position(|&b| !is_trailing_ident_char(b))
        .map(|i| idx + i)
        .unwrap_or(s.len())
}

/// Parses an entire block comment, including the starting `/*` and ending `*/`, returning the byte
/// index of the first character outside of the comment. Failure indicates that the comment wasn't
/// closed, and - because block comments may be nested - failure allows all unclosed nested block
/// comments to be returned.
fn consume_block_comment<'a>(s: &'a str, start_idx: usize) -> Result<usize, Vec<Invalid<'a>>> {
    // Block comments are complicated, because we'll allow them to be nested, and we'll explicitly
    // account for string literals as well. We'll call this function recursively for every nested
    // block comment that we get, and we'll call `consume_string_lit` for any string literals.
    //
    // If any of these don't complete, we also won't have completed, so we'll fail as well, adding
    // the context that *we* have to the list.

    // We'll just double-check that we received the correct starting values.
    assert_eq!(&s[start_idx..start_idx + 2], "/*");

    // add two so that we start *after* the '/*'
    let mut idx = start_idx + 2;

    // If there isn't room after the '/*' for another index, we'll return that it failed. We need
    // to do this bounds check here because otherwise this would panic if the input file ends with
    // an opening block comment.
    if s.len() <= idx {
        return Err(vec![Invalid {
            src: &s[start_idx..],
            incomplete: Some(IncompleteKind::BlockComment),
        }]);
    }

    let bytes = s.as_bytes();

    let mut b = bytes[idx];
    while let Some(&next) = bytes.get(idx + 1) {
        match (b, next) {
            // Close the current block - we're done! We add 2 because +1 is the index of '/', so +2
            // will be just after the end
            (b'*', b'/') => return Ok(idx + 2),

            // Recurse so that we get a nested block comment
            (b'/', b'*') => match consume_block_comment(s, idx) {
                // Within bounds
                Ok(i) if i < bytes.len() => {
                    idx = i;
                    b = bytes[idx];
                }
                // Out of bounds - the inner comment was fine, but the outer wasn't (the inner was
                // closed at ~ the end of the file), so we'll let the cleanup at the end of this
                // function handle that
                Ok(_) => break,
                // The inner block didn't complete, so neither can this - we'll add the error
                // *before* the others, because this block comment occurs earlier in the file
                Err(mut errs) => {
                    errs.insert(
                        0,
                        Invalid {
                            src: &s[start_idx..],
                            incomplete: Some(IncompleteKind::BlockComment),
                        },
                    );

                    return Err(errs);
                }
            },

            // Start parsing (escaping) a string literal
            //
            // We give it idx+1 because it expects the first character *inside* the string.
            (b'"', _) => match consume_string_lit(s, idx + 1) {
                // Within bounds
                Some(i) if i < bytes.len() => {
                    idx = i;
                    b = bytes[idx];
                }
                // Out of bounds - The string was fine, but the block comment wasn't, so we'll let
                // the cleanup handle it
                Some(_) => break,
                // Didn't finish - we'll return a list of errors containing both token attempts
                None => {
                    return Err(vec![
                        // The block comment occurs first, so we put it first in the list
                        Invalid {
                            src: &s[start_idx..],
                            incomplete: Some(IncompleteKind::BlockComment),
                        },
                        // And then we follow it with the inner string literal
                        Invalid {
                            src: &s[idx..],
                            incomplete: Some(IncompleteKind::StringLiteral),
                        },
                    ]);
                }
            },

            // In the base case, we just keep going, consuming more bytes
            _ => {
                idx += 1;
                b = next;
            }
        }
    }

    // If we got here, it wasn't closed!
    Err(vec![Invalid {
        src: &s[start_idx..],
        incomplete: Some(IncompleteKind::BlockComment),
    }])
}

/// Given the byte index of the first character inside a string literal, this returns the byte
/// index of the first character following the closing double-quote.
///
/// It may be the case that a user has not closed this double-quote, in which case `None` will be
/// returned.
fn consume_string_lit(s: &str, idx: usize) -> Option<usize> {
    // Currently, we won't allow escaped characters here, so this is fairly simple. We'll replace
    // this once the semantics for escape characters are decided on.
    s.as_bytes()[idx..]
        .iter()
        .position(|&b| b == b'"')
        .map(|i| idx + i + 1) // Add one so we give the *next* character
}

/// Attempts to consume a single-quote escaped character literal, returning the starting byte index
/// of the first character after the quotes.
fn consume_single_quote(s: &str, idx: usize) -> Option<usize> {
    // Currently our rules will require exactly one character in-between quotes here.
    //
    // As such, this can use - at most - three characters, so we check these three in order. The
    // first one should be given by the caller, but we'll check it anyways. Escaped characters
    // (which will require more than one character in the source file) need to be decided on, so
    // they aren't implemented here yet.

    // This should have been given a section of the string starting with a single-quote.
    assert_eq!(s.as_bytes()[idx], b'\'');

    // If there's no next character, we haven't matched, so we'll return.
    let c = char_at(s, idx + 1)?;

    // With our middle character out of the way, we only need to check that it's followed by a
    // second single-quote.
    let post = idx + 1 + c.len_utf8();

    match s.as_bytes().get(post) {
        Some(b'\'') => Some(post + 1),
        _ => None,
    }
}

impl<F: Fn(&str) -> Range<usize>> ToError<(F, &str)> for Invalid<'_> {
    fn to_error(self, aux: &(F, &str)) -> ErrorBuilder {
        use IncompleteKind::{BlockComment, StringLiteral};

        let (ref byte_range, ref file_name) = aux;

        let range = byte_range(self.src);
        let region = SourceRange {
            file_name: (*file_name).into(),
            byte_range: range.clone(),
        };

        match self.incomplete {
            None => ErrorBuilder::new(format!("unrecognized character sequence: {:?}", self.src))
                .context(*file_name, range.start)
                .highlight(vec![region], error::ERR_COLOR),
            Some(BlockComment) => ErrorBuilder::new("unclosed block comment")
                .context(*file_name, range.start)
                .highlight(vec![region], error::ERR_COLOR),
            Some(StringLiteral) => ErrorBuilder::new("unclosed string literal")
                .context(*file_name, range.start)
                .highlight(vec![region], error::ERR_COLOR),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // A helper macro for cleanly constructing tokens
    macro_rules! token {
        ($kind:expr, $src:expr) => {{
            Token {
                src: $src,
                kind: $kind,
            }
        }};
    }

    #[test]
    fn valid_no_nested() {
        use TokenKind::*;

        let input = concat!(
            "foo 34 // comment\n",
            "bars! (){}[]\n",
            "    <- indent\n",
            "\tops +-*/= \n",
            "punc. ,:;",
        );

        let expected = vec![
            // First line:
            token!(Ident, "foo"),
            token!(Whitespace, " "),
            token!(Literal(LiteralKind::Int), "34"),
            token!(Whitespace, " "),
            token!(LineComment, "// comment"),
            token!(Whitespace, "\n"),
            // Second line:
            token!(Ident, "bars"),
            token!(Not, "!"),
            token!(Whitespace, " "),
            token!(OpenParen, "("),
            token!(CloseParen, ")"),
            token!(OpenCurly, "{"),
            token!(CloseCurly, "}"),
            token!(OpenSquare, "["),
            token!(CloseSquare, "]"),
            token!(Whitespace, "\n    "),
            // Third line:
            token!(Lt, "<"),
            token!(Minus, "-"),
            token!(Whitespace, " "),
            token!(Ident, "indent"),
            token!(Whitespace, "\n\t"),
            // Fourth line:
            token!(Ident, "ops"),
            token!(Whitespace, " "),
            token!(Plus, "+"),
            token!(Minus, "-"),
            token!(Star, "*"),
            token!(Slash, "/"),
            token!(Eq, "="),
            token!(Whitespace, " \n"),
            // Fifth line:
            token!(Ident, "punc"),
            token!(Dot, "."),
            token!(Whitespace, " "),
            token!(Comma, ","),
            token!(Colon, ":"),
            token!(Semi, ";"),
        ];

        let tokens = tokenize(input)
            .into_iter()
            .map(Result::unwrap)
            .collect::<Vec<_>>();

        assert_eq!(tokens, expected);
    }

    #[test]
    fn valid_nested() {
        use TokenKind::*;

        let input = concat!(
            "foo /* block!\n",
            "    /* inner! */\n",
            "    \" string! */ \" continue\n",
            " and end */\n",
            "tail!",
        );

        let expected = vec![
            token!(Ident, "foo"),
            token!(Whitespace, " "),
            token!(
                BlockComment,
                concat!(
                    "/* block!\n",
                    "    /* inner! */\n",
                    "    \" string! */ \" continue\n",
                    " and end */",
                )
            ),
            // NOTE: The inner values are parsed, but not given, because they were done
            // successfully
            //
            // token!(BlockComment, "/* inner! */"),
            // token!(Literal(LiteralKind::String), "\" string! */ \""),
            token!(Whitespace, "\n"),
            token!(Ident, "tail"),
            token!(Not, "!"),
        ];

        let tokens = tokenize(input)
            .into_iter()
            .map(Result::unwrap)
            .collect::<Vec<_>>();

        assert_eq!(tokens, expected);
    }
}
