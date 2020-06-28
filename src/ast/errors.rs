//! Error types and messages for parsing into the AST

use super::Node;

pub struct Error<'a> {
    pub kind: Kind<'a>,
    pub src: Node<'a>,
}

// A placeholder error kind until we need more
pub type Kind<'a> = &'a str;
