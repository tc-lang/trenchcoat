//! The main parser

pub mod errors;

use crate::token_tree::{Token, TokenKind};
use errors::Error;

pub fn try_parse<'a>(tokens: &'a [Token<'a>]) -> Vec<Result<Item<'a>, Error<'a>>> {
    todo!()
}

#[derive(Debug, Clone)]
pub struct Item<'a> {
    src: &'a [Token<'a>],
    kind: ItemKind<'a>,
}

#[derive(Debug, Clone)]
enum ItemKind<'a> {
    Fn(FnDecl<'a>),
    Type(TypeDef<'a>),
    Import(ImportStmt<'a>),
}

// These are all placeholders until they're properly written
type FnDecl<'a> = &'a str;
type TypeDef<'a> = &'a str;
type ImportStmt<'a> = &'a str;

pub enum Node<'a> {
    Item(&'a Item<'a>),
}

impl<'a> Item<'a> {
    fn parse_from(tokens: &'a [Token<'a>]) -> Result<Item<'a>, bool> {
        todo!()
    }
}
