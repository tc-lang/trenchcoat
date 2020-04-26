#![warn(clippy::pedantic)]
#![warn(clippy::perf)]

use std::char;
use std::iter::Peekable;

use super::position::Position;

///Containts a `std::iter::Peekable<T>` which the iterator and peek methods pass through to. It
///also keeps track of the `Position` in the source file.
pub(super) struct Reader<'a, T: Iterator<Item=char>> {
    pos: Position,
    peekable: &'a mut Peekable<T>,
}

impl<T: Iterator<Item=char>> Reader<'_, T> {
    ///Creates a new reader reading from peekable.
    pub fn new<'a>(peekable: &'a mut Peekable<T>) -> Reader<'a, T> {
        Reader::<'a, T> {
            pos: Position{
                i: 0,
                line: 1,
                char: 1,
            },
            peekable,
        }
    }
    ///Returns the next character that would be returned by next without advancing the iterator. If
    ///no char exists, None is returned.
    pub(super) fn peek(&mut self) -> Option<&char> { self.peekable.peek() }
    ///Returns the `Position` of the next char to be read.
    pub(super) fn position(&mut self) -> Position { self.pos }
}

impl<T: Iterator<Item=char>> Iterator for Reader<'_, T> {
    type Item = char;
    fn next(&mut self) -> Option<Self::Item> {
        let ch = self.peekable.next()?;
        self.pos.char_read(ch);
        Some(ch)
    }
}

