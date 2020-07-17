use super::{prelude::*, types::GenericArgs};
use crate::tokens::{contains_newline, LiteralKind};

#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
    pub src: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
pub enum ExprKind<'a> {
    /// A name, just a string for now.
    Name(&'a str),

    Type {
        name: &'a str,
        generic_args: GenericArgs<'a>,
    },

    RawLiteral(&'a str, LiteralKind),

    /// `<op><expr>`
    PrefixOp {
        op: PrefixOp,
        expr: Box<Expr<'a>>,
    },
    /// `<expr><op>`
    PostfixOp {
        expr: Box<Expr<'a>>,
        op: PostfixOp,
    },
    /// `<lhs><op><rhs>`
    BinaryOp {
        lhs: Box<Expr<'a>>,
        op: BinaryOp,
        rhs: Box<Expr<'a>>,
    },

    TypeHint {
        expr: Box<Expr<'a>>,
        typ: Type<'a>,
    },

    /// `let <pat> = <expr>`
    Let {
        pat: Pat<'a>,
        expr: Box<Expr<'a>>,
    },

    Match {
        expr: Box<Expr<'a>>,
        arms: Vec<(Pat<'a>, Expr<'a>)>,
    },

    /// A list of statements.
    /// The evaluated value is the evaluated value of the last statement.
    /// If the block is terminated by a semi-colon, then the last statement is an empty expression.
    Block {
        stmts: Vec<Stmt<'a>>,
        delim: Delim,
    },

    /// `{ ident }` - ambiguous between Block and Struct
    BlockOrStruct {
        ident: &'a str,
        delim: Delim,
    },

    /// A struct, enclosed in `delim` when parsed.
    Struct {
        fields: Struct<'a>,
        delim: Delim,
    },

    /// `<func><arguments>` - call `func` with `arguments`
    /// Note that the struct may have `delim: Curlies` or `delim: Parens`.
    /// Curlies can be used to call type functions.
    /// Checking this should occur in verification, when the kinds of `func` are known.
    FnCall {
        func: Box<Expr<'a>>,
        arguments: Struct<'a>,
    },

    CurlyFnCall {
        func: Box<Expr<'a>>,
        arguments: Struct<'a>,
    },

    Index {
        expr: Box<Expr<'a>>,
        index: Box<Expr<'a>>,
    },

    /// `if <condition> <block> [else <else_block>]`
    /// `block` will always be a `Struct` with `delim: Curlies`
    /// `else_block` could also be `If`
    If {
        condition: Box<Expr<'a>>,
        block: Box<Expr<'a>>,
        else_block: Option<Box<Expr<'a>>>,
    },
    /// `loop <block>`
    /// Currently, the block is always a curlies tree.
    Loop {
        block: Box<Expr<'a>>,
    },
    /// `while <condition> <block> [else <else_block>]`
    /// Currently, the block is always a curlies tree.
    While {
        condition: Box<Expr<'a>>,
        block: Box<Expr<'a>>,
        else_block: Option<Box<Expr<'a>>>,
    },
    /// `do <block> while <condition> [else <else_block>]`
    /// Currently, the block is always a curlies tree.
    DoWhile {
        condition: Box<Expr<'a>>,
        block: Box<Expr<'a>>,
        else_block: Option<Box<Expr<'a>>>,
    },
    /// `for <variable> in <expr> <block> [else <else_block>]`
    /// Currently, the block is always a curlies tree.
    For {
        variable: &'a str,
        expr: Box<Expr<'a>>,
        block: Box<Expr<'a>>,
        else_block: Option<Box<Expr<'a>>>,
    },

    Closure {
        params: Vec<NamedField<'a>>,
        ret_typ: Type<'a>,
        body: Box<Expr<'a>>,
    },

    /// An empty expression, this evaluates to `{}`.
    Empty,
}

#[derive(Debug, Clone)]
pub struct Struct<'a> {
    pub unnamed_fields: Vec<Expr<'a>>,
    pub named_fields: Vec<(&'a str, Expr<'a>)>,
}

impl<'a> Struct<'a> {
    const UNIT: Struct<'a> = Struct {
        named_fields: Vec::new(),
        unnamed_fields: Vec::new(),
    };
}

macro_rules! opers {
    ($vis:vis enum $name:ident (bp $bp_type:ty) {
        $($punc:ident => $oper:ident $bp:expr,)*
    }) => {
        #[derive(Debug, Clone, Copy)]
        $vis enum $name {
            $($oper,)*
        }
        impl $name {
            fn try_from(punc: &Punc) -> Option<Self> {
                match punc {
                    $(Punc::$punc => Some(Self::$oper),)*
                    _ => None,
                }
            }
            fn binding_power(&self) -> $bp_type {
                match self {
                    $(Self::$oper => $bp,)*
                }
            }
        }
    }
}

opers!(
    pub enum PrefixOp (bp u8) {
        And => Ref (2),
        AndAnd => RefRef (2),
        Minus => Neg (2),
        Not => Not (2),
    }
);

opers!(
    pub enum PostfixOp (bp u8) {
        Question => Try (6),
    }
);

/// The binding power of let
const LET_BP: u8 = 3;
/// The binding power of function application
const APPLY_BP: u8 = 8;
opers!(
    pub enum BinaryOp (bp (u8, u8)) {
        AndAnd => LogicAnd (1, 1),
        OrOr => LogicOr (2, 2),
        // LET: 3
        Plus => Plus (4, 5),
        Minus => Sub (4, 5),
        Star => Mul (6, 7),
        Slash => Div (6, 7),
        // Function application: 8
        Dot => Dot (9, 10),
    }
);

macro_rules! else_block {
    ($context:ident) => {
        match maybe_kwd!(Else) {
            true => Some(Box::new(curlies!($context))),
            false => None,
        };
    };
}

impl<'a, 'b> Expr<'a> {
    pub const EMPTY: Expr<'a> = Expr {
        kind: ExprKind::Empty,
        src: &[],
    };

    pub(crate) fn consume(inp: ParseInp<'a, 'b>, allow_curly_call: bool) -> ParseRet<Expr<'a>> {
        Expr::consume_with_min_bp(inp, 0, allow_curly_call)
    }

    parser!(
        pub(crate) fn consume_with_min_bp(
            inp: ParseInp<'a, 'b>;
            min_bp: u8, allow_curly_call: bool
        ) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            use TokenKind::Punctuation;

            let mut lhs = match peek!(1).kind() {
                Some(Punctuation(Punc::RightArrow)) | Some(Punctuation(Punc::ThinRightArrow)) => {
                    if min_bp <= 3 {
                        call!(Expr::consume_closure; allow_curly_call)
                    } else {
                        todo!()
                    }
                }
                _ => match token!().kind() {
                    Some(TokenKind::Punctuation(punc)) => {
                        let prefix_op = match PrefixOp::try_from(punc) {
                            Some(op) => op,
                            None => error!(Error {
                                kind: ErrorKind::Expecting {
                                    expecting: Expecting::Expr,
                                    found: Some(last_token!().kind.clone()),
                                    context: ExpectingContext::ExprPrefixOp,
                                },
                                src: last_token_slice!(),
                            }),
                        };
                        let expr = call!(
                            Expr::consume_with_min_bp;
                            prefix_op.binding_power(), allow_curly_call
                        );
                        Expr {
                            kind: ExprKind::PrefixOp {
                                op: prefix_op,
                                expr: Box::new(expr),
                            },
                            src: src!(),
                        }
                    }
                    Some(TokenKind::Ident(name)) => match call!(GenericArgs::consume_expr_args) {
                        None => Expr {
                            kind: ExprKind::Name(name),
                            src: src!(),
                        },
                        Some(generic_args) => Expr {
                            kind: ExprKind::Type {
                                name, generic_args,
                            },
                            src: src!(),
                        },
                    },
                    Some(TokenKind::Literal(s, literal_kind)) => Expr {
                        kind: ExprKind::RawLiteral(*s, *literal_kind),
                        src: src!(),
                    },
                    Some(TokenKind::Keyword(Kwd::Let)) => call!(Expr::consume_let; allow_curly_call),
                    Some(TokenKind::Keyword(Kwd::If)) => call!(Expr::consume_if),
                    Some(TokenKind::Keyword(Kwd::Loop)) => call!(Expr::consume_loop),
                    Some(TokenKind::Keyword(Kwd::While)) => call!(Expr::consume_while),
                    Some(TokenKind::Keyword(Kwd::Do)) => call!(Expr::consume_do_while),
                    Some(TokenKind::Keyword(Kwd::For)) => call!(Expr::consume_for),
                    Some(TokenKind::Keyword(Kwd::Match)) => call!(Expr::consume_match),

                    Some(TokenKind::Tree {
                        delim: Delim::Curlies,
                        inner, ..
                    }) => all!(Expr::parse_curlies_inner, inner; last_token_slice!()),

                    Some(TokenKind::Tree {
                        delim: Delim::Parens,
                        inner, ..
                    }) => Expr {
                        kind: ExprKind::Struct {
                            fields: all!(Expr::parse_tuple_inner, inner),
                            delim: Delim::Parens,
                        },
                        src: last_token_slice!(),
                    },

                    found => error!(Error {
                        kind: ErrorKind::Expecting {
                            expecting: Expecting::Expr,
                            found: found.cloned(),
                            context: ExpectingContext::Expr,
                        },
                        src: match found {
                            Some(_) => last_token_slice!(),
                            None => &[],
                        },
                    }),
                },
            };

            loop {
                match peek!().kind() {
                    Some(TokenKind::Punctuation(punc)) => {
                        if let Some(bin_op) = BinaryOp::try_from(punc) {
                            let (left_bp, right_bp) = bin_op.binding_power();
                            if left_bp < min_bp {
                                return ret!(lhs);
                            }
                            skip!();

                            let rhs = call!(Expr::consume_with_min_bp; right_bp, allow_curly_call);

                            lhs = Expr {
                                kind: ExprKind::BinaryOp {
                                    lhs: Box::new(lhs),
                                    op: bin_op,
                                    rhs: Box::new(rhs),
                                },
                                src: src!(),
                            };
                        } else if let Some(post_op) = PostfixOp::try_from(punc) {
                            if post_op.binding_power() < min_bp {
                                return ret!(lhs);
                            }
                            skip!();

                            lhs = Expr {
                                kind: ExprKind::PostfixOp {
                                    expr: Box::new(lhs),
                                    op: post_op,
                                },
                                src: src!(),
                            };
                        } else {
                            return ret!(lhs);
                        }
                    }

                    Some(TokenKind::Tree {
                        delim,
                        inner,
                        leading_whitespace: _,
                    }) => {
                        if APPLY_BP < min_bp || contains_newline(last_token!().trailing_whitespace) {
                            return ret!(lhs);
                        }

                        let kind = match delim {
                            Delim::Parens => {
                                skip!();
                                let arguments = all!(Expr::parse_tuple_inner, inner);
                                ExprKind::FnCall {
                                    func: Box::new(lhs),
                                    arguments,
                                }
                            }
                            Delim::Squares => {
                                skip!();
                                let inner_expr = all!(Expr::consume, inner; true);
                                ExprKind::Index {
                                    expr: Box::new(lhs),
                                    index: Box::new(inner_expr),
                                }
                            },
                            Delim::Curlies if !allow_curly_call => return ret!(lhs),
                            Delim::Curlies => {
                                skip!();
                                let arguments = all!(Expr::parse_struct_inner, inner);
                                ExprKind::CurlyFnCall {
                                    func: Box::new(lhs),
                                    arguments,
                                }
                            },
                        };

                        lhs = Expr {
                            kind,
                            src: src!(),
                        };
                    }

                    _ => return ret!(lhs),
                };
            }
        }
    );

    parser!(
        pub(crate) fn consume_loop(inp: ParseInp<'a, 'b>) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            ret!(Expr {
                kind: ExprKind::Loop {
                    block: Box::new(curlies!(LoopBlock)),
                },
                src: src!(),
            })
        }
    );

    parser!(
        pub(crate) fn consume_while(inp: ParseInp<'a, 'b>) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            let condition = call!(Expr::consume; false);
            let block = curlies!(WhileBlock);
            let else_block = else_block!(WhileElseBlock);

            ret!(Expr {
                kind: ExprKind::While {
                    condition: Box::new(condition),
                    block: Box::new(block),
                    else_block,
                },
                src: src!(),
            })
        }
    );

    parser!(
        pub(crate) fn consume_do_while(inp: ParseInp<'a, 'b>) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            let block = curlies!(DoWhileBlock);
            expect_kwd!(While, DoWhileWhile);
            let condition = call!(Expr::consume; true);
            let else_block = else_block!(DoWhileElseBlock);

            ret!(Expr {
                kind: ExprKind::While {
                    condition: Box::new(condition),
                    block: Box::new(block),
                    else_block,
                },
                src: src!(),
            })
        }
    );

    parser!(
        pub(crate) fn consume_for(inp: ParseInp<'a, 'b>) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            let variable = expect_ident!(ForName);
            expect_kwd!(In, ForIn);
            let expr = call!(Expr::consume; false);
            let block = curlies!(ForBlock);
            let else_block = else_block!(ForElseBlock);

            ret!(Expr {
                kind: ExprKind::For {
                    variable,
                    expr: Box::new(expr),
                    block: Box::new(block),
                    else_block,
                },
                src: src!(),
            })
        }
    );

    parser!(
        pub(crate) fn consume_let(inp: ParseInp<'a, 'b>; allow_curly_call: bool) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            let pat = call!(Pat::consume);
            expect_punc!(Eq, LetEq);
            let expr = call!(Expr::consume_with_min_bp; LET_BP, allow_curly_call);

            ret!(Expr {
                kind: ExprKind::Let {
                    pat,
                    expr: Box::new(expr)
                },
                src: src!(),
            })
        }
    );

    parser!(
        pub(crate) fn consume_match(inp: ParseInp<'a, 'b>) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            let expr = call!(Expr::consume; false);

            let arms = all!(Expr::parse_match_arms, expect_delim!(Curlies, MatchCurlies));

            ret!(Expr {
                kind: ExprKind::Match {
                    expr: Box::new(expr),
                    arms,
                },
                src: src!(),
            })
        }
    );

    parser!(
        pub(crate) fn parse_match_arms(
            inp: ParseInp<'a, 'b>,
        ) -> ParseRet<Vec<(Pat<'a>, Expr<'a>)>> {
            let mut tok_idx = 0;

            let mut arms = Vec::new();
            punc_separated!(Comma, MatchComma, {
                let pat = call!(Pat::consume);
                expect_punc!(RightArrow, MatchArrow);
                let expr = call!(Expr::consume; true);
                arms.push((pat, expr));
            });

            ret!(arms)
        }
    );

    parser!(
        pub(crate) fn consume_if(inp: ParseInp<'a, 'b>) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            let condition = call!(Expr::consume; false);
            let block = curlies!(DoWhileBlock);
            let else_block = match maybe_kwd!(Else) {
                false => None,
                true => {
                    use Kwd::If;
                    use TokenKind::{Keyword, Tree};
                    match token!().kind() {
                        Some(Keyword(If)) => Some(Box::new(call!(Expr::consume_if))),

                        Some(Tree {
                            delim: Delim::Curlies,
                            inner,
                            leading_whitespace: _,
                        }) => Some(Box::new(
                            call!(Expr::parse_curlies_inner, inner; last_token_slice!()).0,
                        )),

                        Some(_) => error!(Error {
                            kind: ErrorKind::Expecting {
                                expecting: Expecting::ElseExpr,
                                found: Some(last_token!().kind.clone()),
                                context: ExpectingContext::Else,
                            },
                            src: last_token_slice!(),
                        }),
                        None => error!(Error {
                            kind: ErrorKind::Expecting {
                                expecting: Expecting::ElseExpr,
                                found: None,
                                context: ExpectingContext::Else,
                            },
                            src: &[],
                        }),
                    }
                }
            };

            ret!(Expr {
                kind: ExprKind::If {
                    condition: Box::new(condition),
                    block: Box::new(block),
                    else_block,
                },
                src: src!(),
            })
        }
    );

    parser!(
        pub(crate) fn parse_curlies_inner(
            inp: ParseInp<'a, 'b>; src: &'a [Token<'a>]
        ) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            // Parse the tokens as a block
            // (Used later in a couple of cases)
            macro_rules! block {
                () => {
                    Expr {
                        kind: ExprKind::Block {
                            stmts: call!(Expr::consume_block),
                            delim: Delim::Curlies,
                        },
                        src,
                    }
                };
            }

            // {} == UNIT
            if inp.tokens.len() == 0 {
                return ret!(Expr {
                    kind: ExprKind::Struct {
                        delim: Delim::Curlies,
                        fields: Struct::UNIT,
                    },
                    src,
                });
            }

            // { ident } == { ident: ident } OR { (ident) }
            if inp.tokens.len() == 1 {
                if let TokenKind::Ident(name) = inp.tokens[0].kind {
                    skip!();
                    return ret!(Expr {
                        kind: ExprKind::BlockOrStruct {
                            ident: name,
                            delim: Delim::Curlies,
                        },
                        src,
                    });
                }

                return ret!(block!());
            }

            // Look ahead at the next 2 tokens to decide.
            match [&inp.tokens[0].kind, &inp.tokens[1].kind] {
                [TokenKind::Ident(_), TokenKind::Punctuation(Punc::Comma)] |
                [TokenKind::Ident(_), TokenKind::Punctuation(Punc::Colon)] => {
                    ret!(Expr {
                        kind: ExprKind::Struct{
                            fields: call!(Expr::parse_struct_inner),
                            delim: Delim::Curlies,
                        },
                        src: src!(),
                    })
                }

                _ => ret!(block!()),
            }
        }
    );

    parser!(
        pub(crate) fn consume_block(inp: ParseInp<'a, 'b>) -> ParseRet<Vec<Stmt<'a>>> {
            let mut tok_idx = 0;

            let mut stmts = Vec::new();

            punc_separated!(Semi, StmtSep, {
                if !has_next!() {
                    stmts.push(Stmt::EMPTY);
                    break;
                }

                let stmt = call!(Stmt::consume);
                stmts.push(stmt);
            });

            ret!(stmts)
        }
    );

    parser!(
        pub(crate) fn parse_struct_inner(inp: ParseInp<'a, 'b>) -> ParseRet<Struct<'a>> {
            let mut tok_idx = 0;

            let mut named_fields = Vec::new();
            while has_next!() {
                let name = expect_ident!(StructExprName);

                if !has_next!() {
                    named_fields.push((
                        name,
                        Expr {
                            kind: ExprKind::Name(name),
                            src: last_token_slice!(),
                        },
                    ));
                    break;
                }

                let expr = mtch_punc!(
                    Colon => {
                        let expr = call!(Expr::consume; true);
                        // Require a comma if there's more tokens
                        if has_next!() {
                            expect_punc!(Comma, StructExprComma);
                        }
                        expr
                    },
                    Comma => Expr {
                        kind: ExprKind::Name(name),
                        src: last_token_slice!(),
                    };
                    context: StructExprColon,
                );

                named_fields.push((name, expr));
            }

            ret!(Struct {
                named_fields,
                unnamed_fields: Vec::new(),
            })
        }
    );

    parser!(
        pub(crate) fn parse_tuple_inner(inp: ParseInp<'a, 'b>) -> ParseRet<Struct<'a>> {
            let mut tok_idx = 0;

            let mut unnamed_fields = Vec::new();
            let mut named_fields = Vec::new();

            /// Look ahead.
            /// Evaluates to true iff the next field is a named field.
            macro_rules! is_named {
                () => {{
                    use TokenKind::{Ident, Punctuation};
                    match [inp.tokens.get(0).kind(), inp.tokens.get(1).kind()] {
                        [Some(Ident(_)), Some(Punctuation(Punc::Colon))] => true,
                        _ => false,
                    }
                }};
            }

            punc_separated!(Comma, TupleExprComma, {
                if is_named!() {
                    break;
                }
                unnamed_fields.push(call!(Expr::consume; true));
            });
            punc_separated!(Comma, TupleExprComma, {
                let name = expect_ident!(TupleExprName);
                expect_punc!(Colon, TupleExprColon);
                let expr = call!(Expr::consume; true);
                named_fields.push((name, expr));
            });

            ret!(Struct {
                unnamed_fields,
                named_fields
            })
        }
    );

    parser!(
        pub(crate) fn consume_closure(
            inp: ParseInp<'a, 'b>;
            allow_curly_call: bool,
        ) -> ParseRet<Expr<'a>> {
            let mut tok_idx = 0;

            use TokenKind::{Ident, Tree};
            let params = mtch!(
                (Ident(name), Expecting::Ident) => vec![
                    NamedField {
                        name, typ: Type::OMMITED,
                    },
                ],

                (Tree {
                    delim: Delim::Parens,
                    inner,
                    ..
                }, Expecting::Delim(Delim::Parens)) => all!(Type::parse_struct_fields, inner; true);

                context: ClosureParams,
            );

            let ret_typ = if maybe_punc!(ThinRightArrow) {
                call!(Type::consume)
            } else {
                Type::OMMITED
            };

            expect_punc!(RightArrow, ClosureArrow);

            let body = call!(Expr::consume; allow_curly_call);

            ret!(Expr {
                kind: ExprKind::Closure {
                    params, ret_typ, body: Box::new(body),
                },
                src: src!(),
            })
        }
    );
}
