use super::prelude::*;
use std::ops::Deref;

#[derive(Debug, Clone)]
pub struct Item<'a> {
    pub kind: ItemKind<'a>,
    pub src: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
pub enum ItemKind<'a> {
    Fn(FnDecl<'a>),
    Type(TypeDecl<'a>),
    Import(ImportStmt<'a>),
    Const(ConstDecl<'a>),
}

#[derive(Debug, Clone)]
pub struct FnDecl<'a> {
    pub name: &'a str,
    pub params: Vec<NamedField<'a>>,
    pub ret_typ: Type<'a>,
    pub body: Expr<'a>,
}
#[derive(Debug, Clone)]
pub struct TypeDecl<'a> {
    pub name: &'a str,
    pub alias: bool,
    pub typ: Type<'a>,
}
type ImportStmt<'a> = &'a str;
type ConstDecl<'a> = &'a str;

impl<'a, 'b> Item<'a> {
    parser!(
        pub(crate) fn consume_items(inp: ParseInp<'a, 'b>) -> ParseRet<Vec<Item<'a>>> {
            let mut tok_idx = 0;
            let mut items = Vec::new();

            while tok_idx < inp.tokens.len() {
                items.push(call!(Item::consume));
            }

            ret!(items)
        }
    );

    parser!(
        pub(crate) fn consume(inp: ParseInp<'a, 'b>) -> ParseRet<Item<'a>> {
            let mut idx = 0;

            ret!(mtch_kwd!(
                Fn => call!(Item::consume_fn),
                Type => call!(Item::consume_type),
                Import => todo!(),
                Const => todo!();

                context: TopLevelKwd,

                // TODO
                // This will generate a really bad error in cases such as:
                //  while something() { ... }
                // On the top level since this will only consume the `while` keyword, leaving the
                // rest to generate more errors.
                //
                // We could parse these statements and only generate 1 error.
            ))
        }
    );

    parser!(
        pub(crate) fn consume_fn(inp: ParseInp<'a, 'b>) -> ParseRet<Item<'a>> {
            let mut tok_idx = 0;

            let name = expect_ident!(FnName);

            let params = call!(Type::parse_struct_fields, expect_delim!(Parens, FnParams); false).0;

            let ret_typ = match maybe_punc!(ThinRightArrow) {
                false => Type::PAREN_UNIT,
                true => call!(Type::consume),
            };

            use Punc::RightArrow;
            use TokenKind::{Punctuation, Tree};
            let body = match token!().kind() {
                Some(Punctuation(RightArrow)) => call!(Expr::consume; true),

                Some(Tree {
                    delim: Delim::Curlies,
                    inner,
                    leading_whitespace: _,
                }) => call!(Expr::parse_curlies_inner, inner.deref(); last_token_slice!()).0,

                Some(_) => todo!(),
                None => todo!(),
            };

            ret!(Item {
                kind: ItemKind::Fn(FnDecl {
                    name,
                    params,
                    ret_typ,
                    body,
                }),
                src: src!(),
            })
        }
    );

    parser!(
        pub(crate) fn consume_type(inp: ParseInp<'a, 'b>) -> ParseRet<Item<'a>> {
            let mut tok_idx = 0;

            let name = expect_ident!(TypeDeclName);

            let alias = match peek!().kind() {
                Some(TokenKind::Keyword(Kwd::Alias)) => {
                    skip!();
                    true
                }
                _ => false,
            };

            let typ = call!(Type::consume);

            ret!(Item {
                kind: ItemKind::Type(TypeDecl { name, alias, typ }),
                src: src!(),
            })
        }
    );
}
