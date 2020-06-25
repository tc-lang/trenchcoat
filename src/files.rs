//! Utilites for managing files and their lines
//!
//! This is primarily for use in mapping byte indices to line/column numbers in error messages, but
//! is extracted here because it's not *directly* related to that.
//!
//! The only type exported is the [`Files`] struct, which is what is used to store information
//! about sets of files.

use std::borrow::Cow;
use std::collections::HashMap;
use unicode_width::UnicodeWidthStr;

/// A container for tracking line information about a set of files
pub struct Files<'a> {
    files: HashMap<String, Vec<LineInfo<'a>>>,
}

/// The information about a single line of text in a source file
///
/// This contains all of the cached content that might be later used.
struct LineInfo<'a> {
    /// The string given directly by the file
    raw: &'a str,

    /// The starting byte index of the line
    start_idx: usize,
}

impl<'a> Files<'a> {
    /// Creats a new, empty set of files
    pub fn new() -> Self {
        Files {
            files: HashMap::new(),
        }
    }

    /// Adds the the file with the given name and content to the tracker
    ///
    /// If an entry with the same file name already exists, this will panic.
    pub fn add(&mut self, file_name: &str, file_content: &'a str) {
        let base = file_content as *const str as *const u8 as usize;

        let lines = file_content
            .lines()
            .map(|line| {
                let start_idx = (line as *const str as *const u8 as usize) - base;

                LineInfo {
                    raw: line,
                    start_idx,
                }
            })
            .collect();

        let old = self.files.insert(String::from(file_name), lines);

        if old.is_some() {
            panic!("file {:?} added twice", file_name);
        }
    }

    /// Returns the line index of the byte index in a certain file
    ///
    /// If the character at the given byte index is a newline, it the line on which the newline
    /// character starts will be returned.
    ///
    /// Note that line indices (as returned by this function) start at zero.
    pub fn line_idx(&self, file_name: &str, byte_idx: usize) -> usize {
        let lines = self.files.get(file_name).unwrap();

        lines
            .binary_search_by_key(&byte_idx, |l| l.start_idx)
            .unwrap_or_else(|idx| idx - 1)
    }

    /// Returns the column of the byte index corresponding to the byte index in the given file
    pub fn col_idx(&self, file_name: &str, mut byte_idx: usize) -> usize {
        // TODO: This function isn't as efficient as it could be, but that's okay for now - this is
        // only really used in printing errors, so we can get away with it being a little slower.
        //
        // A future improvement might make this faster, but that's not something that urgently
        // needs doing.

        let lines = self.files.get(file_name).unwrap();
        let idx = self.line_idx(file_name, byte_idx);

        // And now we'll set the byte index to be within the *line*
        byte_idx -= lines[idx].start_idx;

        // We're nearly there. If the line contains any tab characters (it shouldn't!), we'll
        // replace them and then get the line.
        let n_tabs = lines[idx]
            .raw
            .as_bytes()
            .iter()
            .filter(|&&b| b == b'\t')
            .count();

        if n_tabs != 0 {
            // Because we're replacing one character with 4, we're increasing the number of bytes
            // by 3 for each tab.
            byte_idx += 3 * n_tabs;

            // Substitute each tab with four spaces - if there's tabs somewhere weird (i.e. not at
            // the start of a line), that's the user's fault, and so they can deal with it not
            // looking perfect
            let line = lines[idx].raw.replace('\t', "    ");
            UnicodeWidthStr::width(&line[..byte_idx])
        } else {
            byte_idx = byte_idx.min(lines[idx].raw.len());
            UnicodeWidthStr::width(&lines[idx].raw[..byte_idx])
        }
    }

    /// Returns the line with the given index from the file
    ///
    /// The returned string will have all tab characters replaced by four spaces.
    pub fn get<'b>(&'b self, file_name: &str, line_idx: usize) -> Cow<'b, str> {
        let line = &self.files.get(file_name).unwrap()[line_idx].raw;

        if line.contains('\t') {
            Cow::Owned(line.replace('\t', "    "))
        } else {
            Cow::Borrowed(line)
        }
    }
}
