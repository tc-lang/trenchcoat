#![warn(clippy::pedantic)]

use std::char;

#[derive(Debug, Clone, Copy)]
///Represents a position in a source file.
pub struct Position {
    ///i is the byte index within the file (starting at 0)
    pub i: usize,
    ///line is the line number within the file (starting at 1)
    pub line: usize,
    ///char is the character number within the current line (starting at 1)
    pub char: usize,
}

impl Position {
    ///char_read should be called when a character is read from a file being tracked by this
    ///`Position`. It advnaces the fields according to the character.
    pub fn char_read(&mut self, ch: char) {
        self.i += 1;
        if ch == '\n' {
            self.line += 1;
            self.char = 1;
        } else {
            self.char += 1;
        }
    }
}

