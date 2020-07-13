use super::prelude::*;

#[derive(Debug, Clone)]
pub struct Pat<'a> {
    pub kind: PatKind<'a>,
    pub src: &'a [Token<'a>],
}
#[derive(Debug, Clone)]
pub enum PatKind<'a> {
    Ident(&'a str),
}

impl<'a, 'b> Pat<'a> {
    parser!(
        pub(crate) fn consume(inp: ParseInp<'a, 'b>) -> ParseRet<Pat<'a>> {
            let mut tok_idx = 0;

            ret!(Pat {
                kind: PatKind::Ident(expect_ident!(PatIdent)),
                src: src!(),
            })
        }
    );
}
