//! Utilities for building and displaying error messages
//!
//! The primary interface here is through the [`Builder`] type, which allows for dynamic construction
//! of complex error messages.

use crate::files::Files;
use ansi_term::Color;
use std::fmt::Write;
use std::mem;
use std::ops::{Range, RangeInclusive};
use unicode_width::UnicodeWidthStr;

pub struct Builder {
    /// The primary error message to go at the top of the error. This is is prefixed by 'error: ' to
    /// construct the final error message.
    msg: String,
    elements: Vec<Element>,
}

/// A range in a single source file
#[derive(Debug, Clone)]
pub struct SourceRange {
    /// The file which the range exists
    pub file_name: String,
    /// The range of bytes in the source file
    pub byte_range: Range<usize>,
}

pub const ERR_COLOR: Color = Color::Red;
pub const CTX_COLOR: Color = Color::Blue;
pub const INFO_COLOR: Color = Color::Yellow;
pub const ACCENT_COLOR: Color = Color::Blue;

/// Elements for use in constructing a complex error message
#[derive(Debug, Clone)]
pub enum Element {
    /// Contextual information for an error message. The byte index is used to generate the
    /// position (in lines and columns) that the error occured.
    ///
    /// Typically, only one context will be given, but this allows for multiple.
    Context { file_name: String, byte_idx: usize },

    /// A set of source ranges in a single file to be highlighted, in order. Multiple ranges are
    /// allowed here so that multiple highlights can be made on a single line, where applicable.
    Highlight {
        regions: Vec<SourceRange>,
        color: Color,
    },

    /// An individual line in the source file to display, usually for the effect o f
    Line { file_name: String, byte_idx: usize },

    /// A string to present following "note: "
    Note(String),

    /// A string to present following "help: "
    Help(String),

    /// (Typically more lengthy) Text to display for the purpose of additional information to
    /// present to the user, with minimal indentation and formatting.
    Text(String),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum ElementKind {
    Context,
    Highlight,
    Line,
    Note,
    Help,
    Text,
}

pub trait ToError<A> {
    fn to_error(self, aux: &A) -> Builder;
}

/// Displays the set of errors, printing them to the terminal via stderr
pub fn display_errors<A, E: ToError<A>>(errs: impl Iterator<Item = E>, aux: A, files: &Files) {
    let mut count = 0;

    for err in errs {
        eprintln!("{}", err.to_error(&aux).pretty_fmt(files));
        count += 1;
    }

    let num_errs = match count {
        1 => "a previous error".into(),
        n => format!("{} previous errors", n),
    };

    eprintln!("{}: Failed due to {}", ERR_COLOR.paint("error"), num_errs);
}

impl Builder {
    pub fn new(msg: impl Into<String>) -> Builder {
        Builder {
            msg: msg.into(),
            elements: Vec::new(),
        }
    }

    pub fn context(self, file_name: impl Into<String>, byte_idx: usize) -> Self {
        self.element(Element::Context {
            file_name: file_name.into(),
            byte_idx,
        })
    }

    // All of the regions must have the same source file
    pub fn highlight(self, regions: Vec<SourceRange>, color: Color) -> Self {
        assert!(!regions.is_empty());
        assert!(regions[1..]
            .iter()
            .all(|r| r.file_name == regions[0].file_name));

        self.element(Element::Highlight { regions, color })
    }

    pub fn line(self, file_name: impl Into<String>, byte_idx: usize) -> Self {
        self.element(Element::Line {
            file_name: file_name.into(),
            byte_idx,
        })
    }

    pub fn note(self, text: impl Into<String>) -> Self {
        self.element(Element::Note(text.into()))
    }

    pub fn help(self, text: impl Into<String>) -> Self {
        self.element(Element::Text(text.into()))
    }

    pub fn text(self, text: impl Into<String>) -> Self {
        self.element(Element::Text(text.into()))
    }

    pub fn element(mut self, elem: Element) -> Self {
        self.elements.push(elem);
        self
    }
}

impl Element {
    fn kind(&self) -> ElementKind {
        use ElementKind::*;

        match self {
            Element::Context { .. } => Context,
            Element::Highlight { .. } => Highlight,
            Element::Line { .. } => Line,
            Element::Note(_) => Note,
            Element::Help(_) => Help,
            Element::Text(_) => Text,
        }
    }
}

impl Builder {
    fn pretty_fmt(&self, files: &Files) -> String {
        // There's a few assertions we'll make that should be true of any error message:
        assert!(!self.elements.is_empty());
        assert_eq!(self.elements[0].kind(), ElementKind::Context);

        // There must some number of contexts at the start, and then none after
        self.elements[1..].iter().fold(true, |can_ctx, elem| {
            if !can_ctx {
                assert!(elem.kind() != ElementKind::Context);
                false
            } else {
                elem.kind() == ElementKind::Context
            }
        });

        // Write the first line of the error - this is the main message, and gives the user a brief
        // overview of what went wrong.
        let mut msg = format!("{}: {}\n", ERR_COLOR.paint("error"), self.msg);

        // From here out, we'll write everything out, adding whatever padding is necessary. The
        // first step is to determine the indentation width for line numbers
        //
        // We'll find the largest line index (line number - 1) represented by the ranges and
        // individual points here, and then use that to determine the width
        let max_line_idx = self
            .elements
            .iter()
            .filter_map(|elem| match elem {
                Element::Context {
                    file_name,
                    byte_idx,
                } => Some(files.line_idx(&file_name, *byte_idx)),
                Element::Highlight { regions, .. } => regions
                    .iter()
                    .map(|r| files.line_idx(&r.file_name, r.byte_range.end))
                    .max(),
                Element::Line {
                    file_name,
                    byte_idx,
                } => Some(files.line_idx(&file_name, *byte_idx)),
                _ => None,
            })
            .max();

        // The width we need to provide in order to ensure all line numbers are evenly aligned.
        let width = match max_line_idx {
            Some(idx) => (idx + 1).to_string().len(),
            None => 0,
        };

        let spacing = " ".repeat(width);
        let blank_line = format!("{} {}", spacing, ACCENT_COLOR.paint("|"));

        // We use `last_file` to determine whether we need to add some extra context to indicate
        // that a line or highlighted region is in a different file.
        let mut last_file: Option<&str> = None;

        // `prev_space` indicates whether the previous line added to the file is "spacious". This
        // is loosely defined, but is essentially used to determine whether we need to add extra
        // spacing so that the message doesn't look too crowded.
        let mut prev_space = false;

        // `prev_note` is simply a marker to indicate whether the previous line (or set of lines)
        // added to the message is a note at the bottom. This is mostly an override for
        // `prev_space` in the case of having multiple notes following each other, because those
        // *should* be packed, unlike all other cases.
        let mut prev_note = false;

        let mut i = 0;
        while i < self.elements.len() {
            // Marker variables to track whether the current element has certain properties. These
            // simply get bumped to `prev_space` and `prev_note` at the end of the loop iteration.
            // let mut has_space = false; // <- unused
            let mut is_note = false;

            match &self.elements[i] {
                // Highlights and lines are the most complicated section. To account for that,
                // they're extracted into a separate function, with more details there.
                Element::Highlight { .. } | Element::Line { .. } => {
                    let (next_idx, file, has_space) = self.write_fmt_lines_from_elem_idx(
                        &mut msg, i, last_file, prev_space, files, &spacing,
                    );
                    i = next_idx;
                    last_file = Some(file);
                    prev_space = has_space;
                    prev_note = false;
                    continue;
                }

                // Context lines are required above to be the first set of elements - we'll have at
                // least one, and any more must be immediately following it.
                //
                // They go directly below the main error message, and tend to look something like
                // this:
                // ```
                //   --> src/test_input.tc:26:9
                // ```
                // They exist to provide an immediate source for the error, so that the user can
                // determine where it is with a glance.
                Element::Context {
                    file_name,
                    byte_idx,
                } => {
                    let line_no = files.line_idx(&file_name, *byte_idx) + 1;
                    let col_no = files.col_idx(&file_name, *byte_idx) + 1;

                    writeln!(
                        msg,
                        "{}{} {}:{}:{}",
                        // The spacing means that the middle '-' in the arrow lines up with
                        // subsequent pipes ('|') going down the side of the message
                        spacing,
                        CTX_COLOR.paint("-->"),
                        // file_name:line:col is the standard format for displaying file locations
                        file_name,
                        line_no,
                        col_no
                    )
                    .unwrap();

                    // If we have multiple contexts for different files at the start, they're too
                    // far out of the way to consider the *last* one as properly setting that
                    // filename as the context.
                    //
                    // In practice, this won't ever really be the case, because most error messages
                    // should only give one context, and the ones that give two will both be in the
                    // same file.
                    match i {
                        0 => last_file = Some(&file_name),
                        _ if last_file == Some(&file_name) => (),
                        _ => last_file = None,
                    }
                }

                // These three cases are fairly simple - they're used for providing a little bit of
                // extra information to the user, which may come in a few different forms.
                //
                // `Note` and `Help` will respectively produce lines that look like:
                // ```
                //    = note: messages can have extra info!
                //    = help: Or instructions on what to change, too!
                // ```
                // Whereas `Text` will produce a line that looks like:
                // ```
                //   ::: Here's some longer-form text that might be used in combination with others
                // ```
                //
                // TODO: @Improvement: Make the text here wrap nicely so that we can split evenly
                // over multiple lines - even better would be doing that automatically based on the
                // terminal width
                Element::Note(text) => {
                    is_note = true;

                    // We want to ensure there's enough space between things, so we'll
                    if !prev_space && !prev_note {
                        writeln!(msg, "{}", blank_line).unwrap();
                    }

                    writeln!(
                        msg,
                        "{} {} note: {}",
                        spacing,
                        ACCENT_COLOR.paint("="),
                        text
                    )
                    .unwrap();
                }
                Element::Help(text) => {
                    is_note = true;

                    if !prev_space && !prev_note {
                        writeln!(msg, "{}", blank_line).unwrap();
                    }

                    writeln!(
                        msg,
                        "{} {} {}: {}",
                        spacing,
                        ACCENT_COLOR.paint("="),
                        INFO_COLOR.paint("help"),
                        text
                    )
                    .unwrap();
                }
                Element::Text(text) => {
                    if !prev_space {
                        writeln!(msg, "{}", blank_line).unwrap();
                    }

                    writeln!(msg, "{}{} {}", spacing, ACCENT_COLOR.paint(":::"), text).unwrap();
                }
            }

            i += 1;
            // prev_space = has_space;
            prev_note = is_note;
        }

        msg
    }

    fn write_fmt_lines_from_elem_idx<'a>(
        &'a self,
        msg: &mut String,
        idx: usize,
        last_file: Option<&str>,
        mut prev_space: bool,
        files: &Files,
        spacing: &str,
    ) -> (usize, &'a str, bool) {
        assert!(idx < self.elements.len());
        assert!(
            self.elements[idx].kind() == ElementKind::Highlight
                || self.elements[idx].kind() == ElementKind::Line
        );

        let file: &str = match &self.elements[idx] {
            Element::Highlight { regions, .. } => {
                // We're given that all highlight regions refer to the same file and that all
                // regions require, so we can just
                // take the first one
                &regions[0].file_name
            }
            Element::Line { file_name, .. } => &file_name,
            _ => unreachable!(),
        };

        let line_range = |elem: &Element| match elem {
            Element::Highlight { regions, .. } => {
                let start = regions
                    .iter()
                    .map(|r| files.line_idx(&r.file_name, r.byte_range.start))
                    .min()
                    .unwrap();
                let end = regions
                    .iter()
                    .map(|r| files.line_idx(&r.file_name, r.byte_range.end))
                    .max()
                    .unwrap();

                start..=end
            }
            Element::Line {
                file_name,
                byte_idx,
            } => {
                let line_idx = files.line_idx(&file_name, *byte_idx);
                line_idx..=line_idx
            }
            _ => unreachable!(),
        };

        let mut current_group = vec![(line_range(&self.elements[idx]), &self.elements[idx])];
        let mut groups = Vec::new();

        // The last line of the current group
        let mut last_line = *line_range(&self.elements[idx]).end();

        // A marker for whether the last value added to the current group is a highlight element.
        // We track this because we don't allow multiple highlight elements to be grouped together.
        let mut last_is_highlight = match self.elements[idx] {
            Element::Highlight { .. } => true,
            _ => false,
        };

        // This is the index that we'll return for the caller to continue formatting with
        let mut continue_idx = self.elements.len();

        for (i, elem) in (idx + 1..).zip(&self.elements[idx + 1..]) {
            match elem {
                Element::Highlight { regions, .. } => {
                    // Again: We only check the first region's file name because all of the regions
                    // for a highlight region must be in the same file
                    //
                    // If it's in a different file, we'll leave it out
                    if &regions[0].file_name != file {
                        continue_idx = i;
                        break;
                    }

                    let range = line_range(elem);

                    if *range.start() < last_line {
                        continue_idx = i;
                        break;
                    }

                    // TODO: This is all somewhat imprecise, and should probably be thoroughly
                    // tested + commented
                    if last_is_highlight || *range.start() != last_line {
                        last_line = *range.end();
                        groups.push(mem::replace(&mut current_group, vec![(range, elem)]));
                    } else {
                        last_line = *range.end();
                        current_group.push((range, elem));
                    }

                    last_is_highlight = true;
                }

                Element::Line { file_name, .. } => {
                    if file_name != &file {
                        continue_idx = i;
                        break;
                    }

                    let range = line_range(elem);

                    if *range.start() < last_line {
                        continue_idx = i;
                        break;
                    }

                    if last_line == *range.start() {
                        last_line = *range.end();
                        current_group.push((range, elem));
                    } else {
                        last_line = *range.end();
                        groups.push(mem::replace(&mut current_group, vec![(range, elem)]));
                    }

                    last_is_highlight = false;
                }

                _ => {
                    continue_idx = i;
                    break;
                }
            }
        }

        groups.push(current_group);

        let mut end_space = false;

        // And now we print each group, which we delegate to yet another function
        for (i, g) in groups.into_iter().enumerate() {
            if i == 0 && last_file != Some(file) {
                if !prev_space {
                    writeln!(msg, "{} {}", spacing, ACCENT_COLOR.paint("|")).unwrap();
                }

                // We'll write a little bit of context, just to indicate that we're describing a
                // new file. It'll look something like:
                // ```
                //    --> in 'src/main.tc':
                // ```
                writeln!(
                    msg,
                    "{}{} in '{}':",
                    spacing,
                    ACCENT_COLOR.paint("-->"),
                    file,
                )
                .unwrap();
            }

            if prev_space {
                writeln!(msg, "{} {}", spacing, ACCENT_COLOR.paint("|")).unwrap();
                prev_space = false;
            }

            end_space = Self::write_group(msg, g, files, file, spacing);
        }

        (continue_idx, file, end_space)
    }

    // Returns whether there should be space after this group
    fn write_group(
        msg: &mut String,
        group: Vec<(RangeInclusive<usize>, &Element)>,
        files: &Files,
        file_name: &str,
        spacing: &str,
    ) -> bool {
        let mut i = 0;
        let mut last_line: Option<usize> = None;

        let mut end_needs_space = false;

        while i < group.len() {
            let (ref range, ref elem) = &group[i];

            let mut next = i + 1;

            // If there's a gap between successive regions, we'll put some dots in between them
            if let Some(l) = last_line {
                if *range.start() > l + 1 {
                    writeln!(msg, "{}", ACCENT_COLOR.paint("...")).unwrap();
                }
            }

            let regions;
            let color;

            if let Element::Highlight {
                regions: rs,
                color: c,
            } = elem
            {
                regions = rs;
                color = *c;

                // If it's a highlight, we'll mark all following lines contained within this range
                // as being included as part of it
                next += group[i + 1..]
                    .iter()
                    .take_while(|(r, e)| {
                        // We only keep including *lines* that are exactly at the end of this range
                        e.kind() == ElementKind::Line
                            && r.start() == r.end()
                            && r.start() == range.start()
                    })
                    .count();
            } else {
                assert_eq!(elem.kind(), ElementKind::Line);

                // Otherwise, we'll skip forward to the next value that includes this line as a
                // starting point. If it isn't *this* one, we'll re-do the loop
                let skip_to = i + group[i + 1..]
                    .iter()
                    .take_while(|(r, _)| range.start() == range.end() && range.end() == r.start())
                    .count();

                if skip_to != i {
                    i = skip_to;
                    continue;
                }

                // Painting a single line is simple, so we'll do that and continue to the next
                // element
                for i in range.clone() {
                    writeln!(
                        msg,
                        "{:>width$} {} {}",
                        // We add one because the ranges are line *indexes*, which start from zero
                        i + 1,
                        ACCENT_COLOR.paint("|"),
                        width = spacing.len(),
                    )
                    .unwrap();
                }

                last_line = Some(*range.end());
                end_needs_space = true;

                i += 1;
                continue;
            }

            // If we're here, we know it's a highlighted region. This is probaby the most
            // complicated piece of this. The first thing we'll do is to collapse all of the regions
            // into a single set of sorted ranges that are all mutally exclusive.
            //
            // And because it's complicated, we're deferring it to yet another function!
            let byte_ranges = collapse_ranges(regions.into_iter().map(|r| r.byte_range.clone()));
            Self::highlight_byte_ranges(msg, byte_ranges, color, files, file_name, spacing);
            end_needs_space = false;
            i = next;
        }

        // There's nothing else to do! We've already written all of the pieces that we wanted to.
        end_needs_space
    }

    // *Actually* does the formatting for writing a set of highlighted ranges to a region. The
    // regions are guaranteed to not have any lines without highlighting between them.
    fn highlight_byte_ranges(
        msg: &mut String,
        ranges: Vec<Range<usize>>,
        color: Color,
        files: &Files,
        file_name: &str,
        spacing: &str,
    ) {
        assert!(!ranges.is_empty());

        // We'll produce the ranges of lines corresponding to each input range, along with the
        // ranges of columns *on* those lines
        //
        // Note that at this point, we're using line+column *indices*, which start at zero. It
        // should also be noted that the ending column might be less than the starting colum - if
        // they are on different lines.
        let line_ranges: Vec<(RangeInclusive<usize>, Range<usize>)>;
        line_ranges = ranges
            .into_iter()
            .map(|r| {
                let lines = RangeInclusive::new(
                    files.line_idx(file_name, r.start),
                    files.line_idx(file_name, r.end),
                );

                let cols = Range {
                    start: files.col_idx(file_name, r.start),
                    end: files.col_idx(file_name, r.end),
                };

                (lines, cols)
            })
            .collect();

        // Most formatting cases are going to be a single line, so we'll handle that quickly.
        let first_line = *line_ranges[0].0.start();
        if line_ranges.iter().all(|(r, _)| r.end() == &first_line) {
            // This is pretty simple. It'll look something like:
            // ```
            // 14 | fn foo(x: int, y: bo0l) {
            //    |    ^^^            ^^^^
            // ```

            // We'll write the first line first.
            writeln!(
                msg,
                "{:>width$} {} {}",
                // +1 becaues lines start at zero
                first_line + 1,
                ACCENT_COLOR.paint("|"),
                width = spacing.len(),
            )
            .unwrap();

            // And now the highlighted region
            write!(msg, "{} {} ", spacing, ACCENT_COLOR.paint("|")).unwrap();
            let mut last = 0;

            for (_, range) in &line_ranges {
                msg.push_str(&" ".repeat(range.start - last));
                write!(msg, "{}", color.paint("^".repeat(range.end - range.start))).unwrap();

                last = range.end;
            }

            // Add one extra newline for consistency
            msg.push('\n');
            return;
        }

        // If that wasn't the case, we have a more complex situtation on our hands. At a maximum
        // level of complexity, this can look something like:
        // ```
        // 14 |        let foo = bar({
        //    | /                ^^^^^
        // 15 | |          baz();    // <- this extra line is a courtesy
        // ...  |
        // 17 | |      }) + qux + FooBar {
        //    | |______^^   ^^^   ^^^^^^^^
        // 18 |            inner: x*y } // <- end the curly here 'cause we're weird
        //    |             ^^^^^^^^^^^^
        // ```
        // Note that there are only three separate regions: `bar(...)`, `qux`, and `FooBar {...}`.
        //
        // This is obviously a completely contrived example, but something that we need to account
        // for in order to not impose arbitrary restrictions on the construction of error messages.
        //
        // What should be noted here is that we indent an additional 4 spaces when displaying the
        // lines themselves. This is to allow for vertial lines behind them.

        // The last column that was highlighted and written to the message. `last_line` and
        // `last_col` are set after every loop iteration, so they are only `None` on the first.
        let mut last_col: Option<usize> = None;
        let mut last_line: Option<usize> = None;

        for (lines, cols) in &line_ranges {
            // The body of this loop works largely in two stages. The first takes into account the
            // first of the set of lines that the range is over, and the second produces all of the
            // following lines. There might not be following lines, in which case that is
            // explicitly handled.

            // Set up some things to use later - these will be useful in all of the cases below.
            let col = last_col.unwrap_or(0);
            let curr_line = files.get(file_name, *lines.start());

            // If we're on a new line (this shouldn't happen outside of the first loop iteration),
            // we'll do some setup to make sure that we have the
            if last_line != Some(*lines.start()) {
                if last_col.is_some() {
                    // This shouldn't be the case, but we'll still account for it anyways. The way
                    // this *might* happen, though, would be through range differences at newlines.
                    //
                    // `last_col` will be Some if we're currently in the process of writing the
                    // highlight line. We'll make that a newline because we're done with it.
                    msg.push('\n');

                    // Reset this to None because we're on a new line now.
                    last_col = None;
                }

                // And finally we'll write the actual line that we're highlighting. Note the 4
                // spaces between the pipe and the text of the line. This is for the reason
                // mentioned briefly above, with the overview picture of the complex case.
                writeln!(
                    msg,
                    "{:>width$} {}    {}",
                    // +1 because line indices start at zero
                    *lines.start() + 1,
                    ACCENT_COLOR.paint("|"),
                    curr_line,
                    width = spacing.len(),
                )
                .unwrap();
            }

            // After doing this, we'll write the first line of the area that we need. There's
            // two ways we can do this. If we two or fewer lines here, then we only need to
            // highlight directly under the text. Otherwise, we'll link up with the side and
            // only highlight through the end of the line.
            //
            // We'll actually handle the cases for n_lines = 1 and 2 separately, because the
            // differences are just enough to make that a little more clear.
            if lines.start() == lines.end() {
                if last_col.is_none() {
                    // If this is the first highlight on the line, we need some padding
                    write!(msg, "{} {}    ", spacing, ACCENT_COLOR.paint("|")).unwrap();
                    // Note: these    ^^^^  are the four spaces mentioned above.
                }

                // Because we only need to write one line, we can simply use the starting and
                // ending columns.
                write!(
                    msg,
                    "{}{}",
                    " ".repeat(cols.start),
                    color.paint("^".repeat(cols.end - cols.start)),
                )
                .unwrap();
            } else if lines.start() + 1 == *lines.end() {
                if last_col.is_none() {
                    // Just like the previous case, if this is the first highlight on the line, we
                    // need some padding.
                    write!(msg, "{} {}    ", spacing, ACCENT_COLOR.paint("|")).unwrap();
                    // Note: these    ^^^^  are the four spaces mentioned above.
                }

                // In the case where there's just two lines, we highlight both of them.
                //
                // The end of the highlight for the first line is the number of columns:
                let fst_end = UnicodeWidthStr::width(curr_line.as_ref() as &str);
                writeln!(
                    msg,
                    "{}{}",
                    " ".repeat(cols.start),
                    color.paint("^".repeat(fst_end - cols.start)),
                )
                .unwrap();

                // And now we write the second line. In the interest of making it look cleaner,
                // we'll actually start after any leading whitespace. If this conflicts with
                // the end of the range, we'll ignore it.
                //
                // Before we do that, however, we need to write another line of the source
                // text.
                let snd_line = files.get(file_name, *lines.end());

                writeln!(
                    msg,
                    "{:>width$} {}    {}",
                    // +1 because line indices start at zero
                    *lines.end() + 1,
                    ACCENT_COLOR.paint("|"),
                    snd_line,
                    width = spacing.len(),
                )
                .unwrap();

                let leading_spaces = snd_line
                    .as_bytes()
                    .iter()
                    .take_while(|&&b| b == b' ')
                    .count();
                let start = match leading_spaces >= cols.end {
                    true => 0,
                    false => leading_spaces,
                };

                // And now we write the actual start of the highlight. We'll let subsequent
                // iterations continue on from this line.
                write!(
                    msg,
                    "{} {}    {}{}",
                    spacing,
                    ACCENT_COLOR.paint("|"),
                    " ".repeat(start),
                    color.paint("^".repeat(cols.end - start)),
                )
                .unwrap();
            } else {
                // Otherwise, we need to make a larger range. As a courtesy, we'll include the
                // line immediately following the start, as well as a set of dots ("...") to
                // indicate if/when lines are being skipped over.
                //
                // As shown above, this structure looks something like:
                // ```
                // 14 |        let foo = bar({
                //    | /                ^^^^^
                // 15 | |          baz();    // <- this extra line is a courtesy
                // ...  |
                // 17 | |      }) + qux + FooBar {
                //    | |______^^
                // ```

                let col = last_col.unwrap_or(0);

                if last_col.is_none() {
                    // We're writing the entire highlight, so get to include the '/' at the
                    // beginning.
                    //
                    // Without any long regions like this, there's 4 spaces between the first
                    // pipe (see: "14 |") and the start of the text ("    let foo"). With this
                    // addition, we replace two of them with " /" for the start of the
                    // highlighting, and leave the rest of the message to be written in a
                    // moment
                    write!(
                        msg,
                        "{} {} {}  ",
                        spacing,
                        ACCENT_COLOR.paint("|"),
                        color.paint("/")
                    )
                    .unwrap();
                }

                let end = UnicodeWidthStr::width(curr_line.as_ref() as &str);

                // Now we'll write the rest of the *first* highlight line
                writeln!(
                    msg,
                    "{}{}",
                    " ".repeat(cols.start - col),
                    color.paint("^".repeat(end - cols.start))
                )
                .unwrap();

                // Because there's at least three lines, we can safely write the next one:
                writeln!(
                    msg,
                    "{:>width$} {} {}  {}",
                    // Note:         ^^ These two spaces are what's left of the four from
                    // before, after filling in the " |" as the continuation of the upper "/".
                    //
                    // +1 because indicies start at zero, +1 again because it's the next line
                    lines.start() + 2,
                    ACCENT_COLOR.paint("|"),
                    color.paint("|"),
                    files.get(file_name, lines.start() + 1),
                    width = spacing.len(),
                )
                .unwrap();

                // If there's more than three total lines, we'll include some dots. Note that
                // the line range is inclusive, so `end - start` is actually `len - 1`.
                if lines.end() - lines.start() > 3 - 1 {
                    // Note that the width here is different from other places - we might not
                    // have the spacing necessary, so we account for that by breaking the first
                    // line of pipes ('|') and adding two to the width to account for that.
                    //
                    // To see how this line fits in, please refer to the example above.

                    writeln!(
                        msg,
                        "{:<width$}  {}",
                        ACCENT_COLOR.paint("..."),
                        color.paint("|"),
                        // Explanation of adding 2 in comment above.
                        width = spacing.len() + 2,
                    )
                    .unwrap();
                }

                // And now we'll do the final line. In a similar manner to one of the other
                // cases above, we'll ignore any leading whitespace (which will only be spaces
                // at this point). As before, if ignoring the whitespace would cut off the
                // ending column, we will silently revert to highlighting all of the whitespace.
                let final_line = files.get(file_name, *lines.end());

                writeln!(
                    msg,
                    "{:>width$} {} {}  {}",
                    // Note:         ^^ These two spaces are what's left of the four from
                    // before, after filling in the " |" as the continuation of the upper "/".
                    lines.end(),
                    ACCENT_COLOR.paint("|"),
                    color.paint("|"),
                    final_line,
                    width = spacing.len(),
                )
                .unwrap();

                let leading_spaces = final_line
                    .as_bytes()
                    .iter()
                    .take_while(|&&b| b == b' ')
                    .count();
                let start = match leading_spaces >= cols.end {
                    true => 0,
                    false => leading_spaces,
                };

                // And now we write the start of the highlighting. This final line (as seen
                // above) looks like:
                // ```
                // 17 | |      }) + qux + FooBar {
                //    | |______^^
                // ```
                // with the context of the line it's highlighting.
                let highlight = format!("|__{}{}", "_".repeat(start), "^".repeat(cols.end - start));

                // We `write!` so that the next ranges can pick up where we left off.
                write!(
                    msg,
                    "{} {} {}",
                    spacing,
                    ACCENT_COLOR.paint("|"),
                    color.paint(highlight),
                )
                .unwrap()
            }

            last_line = Some(*lines.end());
            last_col = Some(cols.end);
        }

        if last_col.is_some() {
            // For a similar reason as given within the loop, we'll push a newline here because a
            // value of `Some` for `last_col` indicates that there was a highlight line in the
            // process of being written, which is now (clearly) done.
            msg.push('\n');
        }
    }
}

// Collapses a set of unsorted ranges into a new set of ranges
fn collapse_ranges(iter: impl Iterator<Item = Range<usize>>) -> Vec<Range<usize>> {
    let mut ranges = <Vec<Range<_>>>::new();

    for region in iter {
        let start_idx = match ranges.binary_search_by_key(&region.start, |r| r.start) {
            Ok(i) => i,
            Err(0) => {
                ranges.insert(0, region.clone());
                0
            }
            Err(i) => {
                if ranges[i - 1].end < region.start {
                    ranges.insert(i, region.clone());
                    i
                } else {
                    // Otherwise, the start value is inside of the previous range
                    i - 1
                }
            }
        };

        // We need to figure out how many ranges we're going to collect into one.
        let n_collapse = ranges[start_idx + 1..]
            .iter()
            .take_while(|r| r.start <= region.end)
            .count();

        ranges[start_idx].end = ranges[start_idx + n_collapse].end.max(region.end);

        // We'll remove all of the ranges that we're collapsing
        ranges.drain(start_idx + 1..=start_idx + n_collapse);
    }

    ranges
}
