use crate::token_tree::{Token, TokenKind};

pub(crate) trait KindOption<'a> {
    fn kind(self) -> Option<&'a TokenKind<'a>>;
}

impl<'a> KindOption<'a> for Option<&'a Token<'a>> {
    fn kind(self) -> Option<&'a TokenKind<'a>> {
        self.map(|t| &t.kind)
    }
}
