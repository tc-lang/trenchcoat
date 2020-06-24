//! Utilites for managing files and their lines
//!
//! This is primarily for use in mapping byte indices to line/column numbers in error messages, but
//! is extracted here because it's not *directly* related to that.
//!
//! The only type exported is the `Files` struct, which is what is used to manage storing sets of
//! files.

use std::collections::HashMap;
use unicode_width::UnicodeWidthStr;

pub struct Files<'a> {
    files: HashMap<String, Vec<&'a str>>,
}

impl<'a> Files<'a> {
    pub fn new() -> Self {
        Files {
            files: HashMap::new(),
        }
    }

    pub fn add(&mut self, file_name: &str, file_content: &'a str) {
        let lines = file_content.lines().collect::<Vec<_>>();
        let old = self.files.insert(String::from(file_name), lines);

        if old.is_some() {
            panic!("file {:?} added twice", file_name);
        }
    }

    pub fn line_idx(&self, file_name: &str, byte_idx: usize) -> usize {
        let lines = self.files.get(file_name).unwrap();

        // We use these to calculate the byte index within the file that each individual line
        // starts at
        let base_ptr = lines[0] as *const str as *const u8 as usize;
        let offset = |line: &str| (line as *const str as *const u8 as usize) - base_ptr;

        lines
            .binary_search_by_key(&byte_idx, |l| offset(*l))
            .unwrap_or_else(|idx| idx - 1)
    }

    pub fn col_idx(&self, file_name: &str, mut byte_idx: usize) -> usize {
        // TODO: This function isn't as efficient as it could be, but that's okay for now - this is
        // only really used in printing errors, so we can get away with it being a little slower.
        //
        // A future improvement might make this faster, but that's not something that urgently
        // needs doing.

        let lines = self.files.get(file_name).unwrap();
        let idx = self.line_idx(file_name, byte_idx);

        // The byte index of the line within the file
        let offset = (lines[idx] as *const str as *const u8 as usize)
            - (lines[0] as *const str as *const u8 as usize);

        // And now we'll set the byte index to be within the *line*
        byte_idx -= offset;

        // We're nearly there. If the line contains any tab characters (it shouldn't!), we'll
        // replace them and then get the line.
        let n_tabs = lines[idx]
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
            let line = lines[idx].replace('\t', "    ");
            UnicodeWidthStr::width(&line[..byte_idx])
        } else {
            byte_idx = byte_idx.min(lines[idx].len());
            UnicodeWidthStr::width(&lines[idx][..byte_idx])
        }
    }

    // Returns the requested line in the given file, with all tabs replaced by four spaces.
    // TODO: Make this return Cow<'_, _>
    pub fn get(&self, file_name: &str, line_idx: usize) -> String {
        self.files.get(file_name).unwrap()[line_idx].replace('\t', "    ")
    }
}
