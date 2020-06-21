//! A collection of helper functions and traits for helping to construct and display error messages

use ansi_term::Color::{Blue, Red};
use std::fmt::Write;
use std::ops::Range;
use unicode_width::UnicodeWidthStr;

/// An interface for creating "pretty" error messages, given the total file string and the name of
/// the file in which it occured.
pub trait PrettyError {
    /// Formats the error, given the contents of the file (`file_str`) and the path (`file_name`).
    ///
    /// The string returned should have a single trailing newline.
    fn pretty_format(&self, file_str: &str, file_name: &str) -> String;
}

/// A helper function to provide pretty printing of error messages
pub fn display_errors<E: PrettyError>(file_str: &str, file_name: &str, errs: &[E], pre_msg: &str) {
    if errs.is_empty() {
        panic!("Internal error: no errors to display");
    }

    for err in errs {
        eprintln!("{}", err.pretty_format(file_str, file_name));
    }

    let err_no = match errs.len() {
        1 => "a previous error".into(),
        n => format!("{} previous errors", n),
    };

    eprintln!("{}: {} due to {}", Red.paint("error"), pre_msg, err_no);
}

/// Returns information about the position of the given byte index within the file
///
/// The return values are - in order - the line number, column number, the byte index of the
/// line in the text, and the byte index on the line. All values start at zero.
///
/// The final return value is the string containing the entire line.
pub fn line_info<'a>(file_str: &'a str, byte_idx: usize) -> (usize, usize, usize, usize, &'a str) {
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
    let col_no = UnicodeWidthStr::width(&last[..byte_idx - offset]);

    (line_no, col_no, offset, byte_idx - offset, last)
}

/// Produces a row of caret characters to underline the given byte range of the line. The upper
/// value on the byte range may be longer than the end of the line, plus one - this is quietly ignored.
pub fn underline(line: &str, mut range: Range<usize>) -> String {
    range.end = range.end.min(line.len());

    // In the future, this function could account for non-ascii strings. Right now, we're just
    // going with the super simple solution of not dealing with that, and simply returning the
    // values.

    // For consistency, we'll double-check that the range is within the bounds of the line
    assert!(range.start <= line.len());

    let pre_len = UnicodeWidthStr::width(&line[..range.start]);
    let mut mid_len = UnicodeWidthStr::width(&line[range.start..range.end]);

    if range.end == range.start {
        mid_len += 1;
    }

    let pre = " ".repeat(pre_len);
    let mid = "^".repeat(mid_len);

    format!("{}{}", pre, mid)
}

/// Produces the standard portion of many error messages. This contains the "context line" and
/// selection + highlighting of the source. The returned string has a trailing - but no leading
/// - newline.
///
/// For more information, see the comments inside `context_lines_and_spacing`, where a detailed
/// explanation is given - both of the total message and each component.
pub fn context_lines(source: Range<usize>, file_str: &str, file_name: &str) -> String {
    context_lines_and_spacing(source, file_str, file_name).0
}

/// The same function `context_lines`, except there is the added (second) return value of the
/// spacing used to prefix certain lines
///
/// This function is useful in cases where additional information must be displayed after the
/// context lines - that additional info needs to be aligned in the same manner.
pub fn context_lines_and_spacing(
    byte_range: Range<usize>,
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

    let (line_no, col_no, line_offset, _, line) = line_info(file_str, byte_range.start);

    let line_no_str = (line_no + 1).to_string();
    let spacing = " ".repeat(line_no_str.len());

    // The range of bytes that the source takes up on its initial line.
    //
    // In a future version, we might allow displaying regions that span multiple lines, but
    // this will do for now - realistically, it should be fine.
    let mut line_range = {
        let start = byte_range.start - line_offset;
        let end = (byte_range.end - line_offset).min(line.len());
        start..end
    };

    let line = replace_tabs(line, Some(&mut line_range));

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
        Red.paint(underline(&line, line_range))
    )
    .unwrap();

    (msg, spacing)
}

pub fn replace_tabs(line: &str, byte_range: Option<&mut Range<usize>>) -> String {
    if let Some(range) = byte_range {
        let start_offset = line[..range.start].chars().filter(|&c| c == '\t').count();
        let mid_offset = line[range.clone()].chars().filter(|&c| c == '\t').count();
        // Because each replacement goes from one tab to four spaces, we actually only add 3
        // characters.
        range.start += 3 * start_offset;
        range.end += 3 * (start_offset + mid_offset);
    }

    line.replace('\t', "    ")
}

/// Information about a given position in the source file, generated by the `info` function.
pub struct PosInfo {
    pub line_idx: usize,
    pub col_idx: usize,
    pub line: String,
    pub line_range: Range<usize>,
}

/// Generates a `PosInfo` given a byte range and the raw string of the file
pub fn info(byte_range: Range<usize>, file_str: &str) -> PosInfo {
    let (line_idx, col_idx, line_offset, _, line) = line_info(file_str, byte_range.start);

    let mut line_range = {
        let start = byte_range.start - line_offset;
        let end = byte_range.end - line_offset;
        start..end
    };

    let line = replace_tabs(line, Some(&mut line_range));

    PosInfo {
        line_idx,
        col_idx,
        line,
        line_range,
    }
}

pub fn info_lines(mut byte_range: Range<usize>, lines: &[&str]) -> PosInfo {
    let base_ptr = lines[0] as *const str as *const u8 as usize;
    let offset = |line: &str| (line as *const str as *const u8 as usize) - base_ptr;

    // We'll find the line that we want
    let line_idx = lines
        .binary_search_by_key(&byte_range.start, |l| offset(*l))
        // We subtract one because - if the start of the range is just above the start of a certain
        // line - the correct index to insert at (which is given by Err(_) for binary search) will
        // be the index of that line + 1.
        .unwrap_or_else(|x| x - 1);

    let line = lines[line_idx];

    byte_range.start -= offset(line);
    byte_range.end -= offset(line);

    let line = replace_tabs(line, Some(&mut byte_range));
    let col_idx = UnicodeWidthStr::width(&line[..byte_range.start]);

    PosInfo {
        line_idx,
        col_idx,
        line,
        line_range: byte_range,
    }
}
