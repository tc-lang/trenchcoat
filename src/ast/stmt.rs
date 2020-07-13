use super::expr::{Expr, ExprKind};
use super::prelude::*;

#[derive(Debug, Clone)]
pub struct Stmt<'a> {
    pub kind: StmtKind<'a>,
    pub src: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
pub enum StmtKind<'a> {
    /// An expression.
    /// We need not a source for the expression, hence this is just a ExprKind.
    Expr(ExprKind<'a>),
    /// Assignment
    /// `<target> = <expr>` (pointer: false)
    /// `*<target> = <expr>` (pointer: true)
    Assign {
        /// TODO this needs to be more than just a string
        target: &'a str,
        expr: Expr<'a>,
        pointer: bool,
    },
}

impl<'a, 'b> Stmt<'a> {
    pub const EMPTY: Stmt<'a> = Stmt {
        kind: StmtKind::Expr(ExprKind::Empty),
        src: &[],
    };

    parser!(
        pub(crate) fn consume(inp: ParseInp<'a, 'b>) -> ParseRet<Stmt<'a>> {
            let mut tok_idx = 0;

            use TokenKind::{Ident, Punctuation};

            match [
                inp.tokens.get(0).kind(),
                inp.tokens.get(1).kind(),
                inp.tokens.get(2).kind(),
            ] {
                [Some(Ident(name)), Some(Punctuation(Punc::Eq)), _] => {
                    tok_idx += 2;
                    ret!(Stmt {
                        kind: StmtKind::Assign {
                            target: name,
                            expr: call!(Expr::consume),
                            pointer: false,
                        },
                        src: src!(),
                    })
                }

                [Some(Punctuation(Punc::Star)), Some(Ident(name)), Some(Punctuation(Punc::Eq))] => {
                    tok_idx += 3;
                    ret!(Stmt {
                        kind: StmtKind::Assign {
                            target: name,
                            expr: call!(Expr::consume),
                            pointer: true,
                        },
                        src: src!(),
                    })
                }

                _ => ret!(Stmt {
                    kind: StmtKind::Expr(call!(Expr::consume).kind),
                    src: src!(),
                }),
            }
        }
    );
}
