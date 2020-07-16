//! The main parser
//!
//! Parsers are functions which take a ParseInp (and optionally other parameters) and returns a
//! ParseRet struct. (These types are found in the prelude.)
//!
//! Parsers are usually defined using the parse macro, which provides a rich set of macros for
//! simple parsing.

pub(crate) mod prelude {
    // Error types
    pub use crate::ast::errors::{Error, Expecting, ExpectingContext, Kind as ErrorKind};
    // Token types
    pub use crate::token_tree::{Delim, Kwd, LiteralKind, Punc, Token, TokenKind};
    // AST types
    pub use super::{
        expr::{Expr, ExprKind},
        item::{Item, ItemKind},
        pat::{Pat, PatKind},
        stmt::{Stmt, StmtKind},
        types::{NamedField, Type, TypeKind},
    };

    /// Parser input.
    pub(crate) struct ParseInp<'a, 'b> {
        /// The tokens to consume. Parsing starts from token 0.
        pub tokens: &'a [Token<'a>],
        /// A Vec to push errors to.
        pub errors: &'b mut Vec<Error<'a>>,
    }
    /// A parser output.
    pub(crate) struct ParseRet<T> {
        /// The result of the parsing.
        pub result: Option<T>,
        /// The number of tokens (from ParseInp.tokens) consumed.
        pub consumed: usize,
    }

    /// Used to provide the `kind` method on Option<&Token> to produce an Option<&TokenKind>
    pub(crate) trait KindOption<'a> {
        fn kind(self) -> Option<&'a TokenKind<'a>>;
    }

    impl<'a> KindOption<'a> for Option<&'a Token<'a>> {
        fn kind(self) -> Option<&'a TokenKind<'a>> {
            self.map(|t| &t.kind)
        }
    }
}

/// A macro for defining a parser.
///
/// The ParseInp argument is listed first, followed by additional parameters after a semi-colon.
/// This mimics how parsers are called using the `call` macro.
///
/// The parser must return a ParseRet<T> with any T.
///
/// The parser body must contain a mutable `tok_idx` variable. This is used to keep track of the
/// current token index (the index within ParseInp.tokens).
///
/// This macro sets up the parsing macros as documented in [make_macros]
macro_rules! parser {
    (
        $vis:vis fn $name:ident(
            $inp:ident: ParseInp<$a:lifetime, $b:lifetime>
            // Optional extra params after a semi-colon
            $(; $($extra_param_name:ident: $extra_param_ty:ty),*)?
            $(,)?
        ) -> ParseRet<$res:ty> {
            // Index counter
            let mut $tok_idx:ident = $start_idx:expr;
            // Rest of the body
            $($tt:tt)*
        }
    ) => {
        $vis fn $name(
            $inp: ParseInp<$a, $b>
            $($(, $extra_param_name: $extra_param_ty)*)?
        ) -> ParseRet<$res> {
            setup!(
                input $inp;
                let mut $tok_idx = $start_idx;
            );
            $($tt)*
        }
    };
}

/// Sets up a parsing function.
/// This declares a mutable token index counter and a rich set of parsing macros.
/// See [make_macros] for the macro documentation.
macro_rules! setup {
    (
        input $inp:expr;
        let mut $tok_idx:ident = $start_idx:expr;
    ) => {
        let mut $tok_idx = $start_idx;
        make_macros!($inp.tokens, $inp.errors, $tok_idx);
    };
}

/// Creates a set of macros for parsing.
/// These may use and/or mutate $tokens, $errors and $tok_idx, along with returning from the
/// function.
///
/// See the doc comments within this macro body for the documentation of available macros.
macro_rules! make_macros {
    ($tokens:expr, $errors:expr, $tok_idx:ident) => {
        use crate::ast::prelude::*;

        /// Evaluates to a ParseRet with result `None`.
        #[allow(unused)]
        macro_rules! none {
            () => {
                ParseRet {
                    result: None,
                    consumed: $tok_idx,
                }
            };
        }

        /// Consume and give the current token.
        /// Evaluates to None on EOF.
        #[allow(unused)]
        macro_rules! token {
            () => {{
                let token = $tokens.get($tok_idx);
                if token.is_some() {
                    $tok_idx += 1;
                }
                token
            }};
        }

        /// Peeks to the nth next token.
        /// If no number is provided, defaults to the next token.
        #[allow(unused)]
        macro_rules! peek {
            ($n:expr) => {
                $tokens.get($tok_idx+$n)
            };

            () => {
                $tokens.get($tok_idx)
            };
        }

        /// Advances $tok_idx.
        #[allow(unused)]
        macro_rules! skip {
            () => {
                $tok_idx += 1
            };
        }

        /// Evaluates to the last token consumed.
        #[allow(unused)]
        macro_rules! last_token {
            () => {
                $tokens[$tok_idx - 1]
            };
        }

        /// Evaluates to a slice of just the last token consumed.
        #[allow(unused)]
        macro_rules! last_token_slice {
            () => {
                std::slice::from_ref(&last_token!())
            };
        }

        /// Evaluates to true iff there is a token yet to be consumed.
        #[allow(unused)]
        macro_rules! has_next {
            () => {
                $tok_idx < $tokens.len()
            };
        }

        macro_rules! make_separated {
            ($d:tt) => {
                /// Loops over $block, expecting $sep_pat between each iteration - apart from when there
                /// are no more tokens, in which case it's optional.
                #[allow(unused)]
                macro_rules! separated {
                    (
                        separator: {
                            pattern: $sep_pat:pat,
                            kind: $sep_kind:expr,
                            context: $context:ident,
                        }
                        terminators: [$d($term_pat:pat),*]
                        block: $block:block
                    ) => {
                        while has_next!() {
                            $block;

                            // A final separator is not required.
                            println!("Peeking {:?}", peek!().kind());
                            match peek!().kind() {
                                // So break if the next token kind matches a terminator
                                // pattern.
                                // This is likely to just be None - although may also be '>'
                                // for example.
                                $d($term_pat => {
                                    maybe!($sep_pat);
                                    break;
                                },)*
                                _ => (),
                            }
                            println!("Kk");

                            // A separator is optional after curlies with a trailing newline.
                            if let TokenKind::Tree {
                                delim: Delim::Curlies,
                                ..
                            } = last_token!().kind {
                                use crate::tokens::contains_newline;
                                if contains_newline(last_token!().trailing_whitespace) {
                                    maybe!($sep_pat);
                                    continue;
                                }
                            }

                            // TODO - For better error messages, we could, in the case of not finding a
                            // separator, push that as an unexpected tokens error and then scan ahead to
                            // the next separator and continue parsing.

                            // Otherwise, expect a separator.
                            expect!($sep_pat, $sep_kind, $context);
                        }
                    };

                    (
                        separator: {
                            pattern: $sep_pat:pat,
                            kind: $sep_kind:expr,
                            context: $context:ident,
                        }
                        block: $block:block
                    ) => {
                        separated!(
                            separator: {
                                pattern: $sep_pat,
                                kind: $sep_kind,
                                context: $context,
                            }
                            terminators: [None],
                            block: $block:block
                        );
                    };
                }

                /// Loops over $block, expecting $punc_variant between each iteration - apart from when
                /// there are no more tokens, in which case it's optional.
                #[allow(unused)]
                macro_rules! punc_separated {
                    (
                        $punc_variant:ident, $context:ident,
                        terminators: [$d($term_pat:pat),*],
                        $block:block
                    ) => {
                        separated!(
                            separator: {
                                pattern: TokenKind::Punctuation(Punc::$punc_variant),
                                kind: TokenKind::Punctuation(Punc::$punc_variant),
                                context: $context,
                            }
                            terminators: [$d($term_pat),*]
                            block: $block
                        )
                    };

                    ($punc_variant:ident, $context:ident, $block:block) => {
                        punc_separated!(
                            $punc_variant, $context,
                            terminators: [None],
                            $block
                        )
                    };
                }
            };
        }
        make_separated!($);

        /// Push the given error to the $errors Vec and return from the parser with a None result.
        #[allow(unused)]
        macro_rules! error {
            ($err:expr) => {{
                $errors.push($err);
                return none!();
            }};
        }

        /// Unwraps an option, returning from the parser if the option is None.
        #[allow(unused)]
        macro_rules! unwrap {
            ($option:expr) => {
                match $option {
                    Some(thing) => thing,
                    None => return none!(),
                }
            };
        }

        /// Unwraps a ParseRet. This returns from the parser with a None result if the ParseRet has
        /// a None result and adds the ParseRets consumed value to the current $tok_idx.
        #[allow(unused)]
        macro_rules! unwrap_ret {
            ($tup:expr) => {{
                let ParseRet { result, consumed } = $tup;
                $tok_idx += consumed;
                unwrap!(result)
            }};
        }

        // This macro is used to generate the `call` and `all` macros.
        // $d will be a `$` token
        macro_rules! make_call {
            ($d:tt) => {

                /// Call the given parser and unwraps the result.
                /// Extra params are passed after a semi-colon.
                ///
                /// If no tokens are provided, the tokens left to consume are passed and the amount
                /// consumed by the parser is added to this parsers $tok_idx.
                ///
                /// Otherwise, if custom tokens are provided, the consumed value is not added and
                /// instead passed down to the caller.
                #[allow(unused)]
                macro_rules! call {
                    (
                        $parser:expr, $new_tokens:expr
                        $d(; $d($extra_param:expr),*)?
                    ) => {{
                        let ParseRet { result, consumed } = $parser(
                            ParseInp {
                                tokens: $new_tokens,
                                errors: $errors,
                            },
                            $d($d($extra_param,)*)?
                        );
                        (unwrap!(result), consumed)
                    }};

                    (
                        $parser:expr
                        $d(; $d($extra_param:expr),*)?
                    ) => {
                        unwrap_ret!($parser(
                            ParseInp {
                                tokens: &$tokens[$tok_idx..],
                                errors: $errors,
                            },
                            $d($d($extra_param,)*)?
                        ))
                    };
                }

                /// Calls a parser with a custom sets of tokens and unwraps the result.
                /// The consumed tokens are not added to the current token index, but is compared
                /// to the size of the tokens passed.
                /// If it is less, an error is generated.
                ///
                /// This is useful for quickly calling a parser to act on *all* the tokens inside a
                /// tree.
                #[allow(unused)]
                macro_rules! all {
                    (
                        $parser:expr, $new_tokens:expr
                        $d(; $d($extra_param:expr),*)?
                    ) => {{
                        let new_tokens = $new_tokens;
                        let (result, consumed) = call!(
                            $parser, new_tokens
                            $d(; $d($extra_param),*)?
                        );
                        if consumed < new_tokens.len() {
                            $errors.push(Error {
                                kind: ErrorKind::Unexpected,
                                src: &new_tokens[consumed..],
                            });
                        }
                        result
                    }};
                }
            };
        }
        make_call!($);

        /// Generates a ParseRet with the given result.
        #[allow(unused)]
        macro_rules! ret {
            ($res:expr) => {
                ParseRet {
                    result: Some($res),
                    consumed: $tok_idx,
                }
            };
        }

        /// Evaluates to the slice of the consumed tokens.
        #[allow(unused)]
        macro_rules! src {
            () => {
                &$tokens[..$tok_idx]
            };
        }

        /// If the next token matches $pat, it is consumed and true is yielded; otherwise, no
        /// tokens are consumed and false is yielded.
        #[allow(unused)]
        macro_rules! maybe {
            ($pat:pat) => {
                match peek!().kind() {
                    Some($pat) => {
                        skip!();
                        true
                    },
                    _ => false,
                }
            };
        }

        /// Expect a TokenKind matching $pat next.
        /// If it does, it is consumed. Otherwise, an errors is pushed (using $kind to generate the
        /// expected kind) and the parser returns.
        #[allow(unused)]
        macro_rules! expect {
            ($pat:pat, $kind:expr, $context:ident) => {{
                let token_kind_option = peek!().kind();
                match token_kind_option {
                    Some($pat) => skip!(),
                    Some(_) => {
                        $errors.push(Error {
                            kind: ErrorKind::Expecting {
                                expecting: Expecting::Token($kind),
                                found: token_kind_option.cloned(),
                                context: ExpectingContext::$context,
                            },
                            src: &$tokens[$tok_idx..$tok_idx + 1],
                        });
                        return none!();
                    }
                    None => {
                        $errors.push(Error {
                            kind: ErrorKind::Expecting {
                                expecting: Expecting::Token($kind),
                                found: None,
                                context: ExpectingContext::$context,
                            },
                            src: &[],
                        });
                        return none!();
                    }
                }
            }};
        }

        /// Evaluates to true and consumes the next token if it is punctuation of the given variant.
        /// Otherwise, no token is consumed and false is yielded.
        #[allow(unused)]
        macro_rules! maybe_punc {
            ($punc_variant:ident) => {
                maybe!(TokenKind::Punctuation(Punc::$punc_variant))
            };
        }

        /// Consumes the next token if it is a punctuation of the given variant.
        /// Otherwise, push and error and return from the parser.
        #[allow(unused)]
        macro_rules! expect_punc {
            ($punc_variant:ident, $context:ident) => {
                expect!(
                    TokenKind::Punctuation(Punc::$punc_variant),
                    TokenKind::Punctuation(Punc::$punc_variant),
                    $context
                )
            };
        }

        /// Evaluates to true and consumes the next token if it is a keyword of the given variant.
        /// Otherwise, no token is consumed and false is yielded.
        #[allow(unused)]
        macro_rules! maybe_kwd {
            ($kwd_variant:ident) => {
                maybe!(TokenKind::Keyword(Kwd::$kwd_variant))
            };
        }

        /// Consumes the next token if it is a keyword of the given variant.
        /// Otherwise, push and error and return from the parser.
        #[allow(unused)]
        macro_rules! expect_kwd {
            ($kwd_variant:ident, $context:ident) => {
                expect!(
                    TokenKind::Keyword(Kwd::$kwd_variant),
                    TokenKind::Keyword(Kwd::$kwd_variant),
                    $context
                )
            };
        }

        /// Consumes the next token if it is an Ident and evaluates to the name.
        /// Otherwise, push and error and return from the parser.
        #[allow(unused)]
        macro_rules! expect_ident {
            ($context:ident) => {{
                let token_kind_option = peek!().kind();
                match token_kind_option {
                    Some(TokenKind::Ident(name)) => {
                        skip!();
                        *name
                    }
                    Some(_) => {
                        $errors.push(Error {
                            kind: ErrorKind::Expecting {
                                expecting: Expecting::Ident,
                                found: token_kind_option.cloned(),
                                context: ExpectingContext::$context,
                            },
                            src: std::slice::from_ref(peek!().unwrap()),
                        });
                        return none!();
                    }
                    None => {
                        $errors.push(Error {
                            kind: ErrorKind::Expecting {
                                expecting: Expecting::Ident,
                                found: None,
                                context: ExpectingContext::$context,
                            },
                            src: &[],
                        });
                        return none!();
                    }
                }
            }};
        }

        /// Consumes the next token if it is a Tree and evaluates to the token.
        /// Otherwise, push and error and return from the parser.
        #[allow(unused)]
        macro_rules! expect_delim {
            ($delim:ident, $context:ident) => {{
                let token_kind_option = peek!().kind();
                match token_kind_option {
                    Some(TokenKind::Tree {
                        inner,
                        delim: Delim::$delim,
                        leading_whitespace: _,
                    }) => {
                        skip!();
                        inner
                    }
                    Some(_) => {
                        $errors.push(Error {
                            kind: ErrorKind::Expecting {
                                expecting: Expecting::Delim(Delim::$delim),
                                found: token_kind_option.cloned(),
                                context: ExpectingContext::$context,
                            },
                            src: std::slice::from_ref(peek!().unwrap()),
                        });
                        return none!();
                    }
                    None => {
                        $errors.push(Error {
                            kind: ErrorKind::Expecting {
                                expecting: Expecting::Delim(Delim::$delim),
                                found: None,
                                context: ExpectingContext::$context,
                            },
                            src: &[],
                        });
                        return none!();
                    }
                }
            }};
        }

        // Same as with call.
        // $d with be a `$` token.
        macro_rules! make_mtch {
            ($d:tt) => {
                /// Match on the next TokenKind.
                ///
                /// Each arms pattern is a tuple, the first element is the pattern to match the
                /// kind against and the left is an expression to generate the expected TokenKind.
                ///
                /// The default cases are handled implicitly and generate errors.
                #[allow(unused)]
                macro_rules! mtch {
                    (
                        $d(($pat:pat, $expecting:expr) => $arm:expr),+;
                        context: $context:ident $d(,)?
                    ) => {{
                        let token_kind_option = peek!().kind();
                        match token_kind_option {
                            $d(Some($pat) => {
                                skip!();
                                $arm
                            },)+
                            Some(_) => {
                                $errors.push(Error {
                                    kind: ErrorKind::Expecting {
                                        expecting: Expecting::OneOf(
                                            &[$d($expecting),+],
                                        ),
                                        found: token_kind_option.cloned(),
                                        context: ExpectingContext::$context,
                                    },
                                    src: last_token_slice!(),
                                });
                                return none!();
                            }
                            None => {
                                $errors.push(Error {
                                    kind: ErrorKind::Expecting {
                                        expecting: Expecting::OneOf(
                                            &[$d($expecting),+],
                                        ),
                                        found: None,
                                        context: ExpectingContext::$context,
                                    },
                                    src: &[],
                                });
                                return none!();
                            }
                        }
                    }};
                }

                /// Match on the next TokenKind.
                ///
                /// Each arms pattern is a Punc variant.
                ///
                /// The default cases are handled implicitly and generate errors.
                #[allow(unused)]
                macro_rules! mtch_punc {
                    (
                        $d($punc_variant:ident => $arm:expr),+;
                        context: $context:ident $d(,)?
                    ) => {
                        mtch!(
                            $d(
                                (
                                    TokenKind::Punctuation(Punc::$punc_variant),
                                    Expecting::Token(TokenKind::Punctuation(Punc::$punc_variant))
                                ) => $arm
                            ),+;
                            context: $context,
                        )
                    };
                }

                /// Match on the next TokenKind.
                ///
                /// Each arms pattern is a Kwd variant.
                ///
                /// The default cases are handled implicitly and generate errors.
                #[allow(unused)]
                macro_rules! mtch_kwd {
                    (
                        $d($kwd_variant:ident => $arm:expr),+;
                        context: $context:ident $d(,)?
                    ) => {
                        mtch!(
                            $d(
                                (
                                    TokenKind::Keyword(Kwd::$kwd_variant),
                                    Expecting::Token(TokenKind::Keyword(Kwd::$kwd_variant))
                                ) => $arm
                            ),+;
                            context: $context,
                        )
                    };
                }
            };
        }
        make_mtch!($);

        /// Expect and parse curlies.
        #[allow(unused)]
        macro_rules! curlies {
            ($context:ident) => {
                all!(
                    Expr::parse_curlies_inner, expect_delim!(Curlies, $context);
                    /* src: */ last_token_slice!()
                );
            };
        }
    };
}

pub mod errors;
pub mod expr;
pub mod item;
pub mod pat;
pub mod readable;
pub mod stmt;
pub mod types;

use self::prelude::*;

pub fn try_parse<'a>(tokens: &'a [Token<'a>]) -> Result<Vec<Item<'a>>, Vec<Error<'a>>> {
    let mut errors = Vec::new();

    let ParseRet { result, .. } = Item::consume_items(ParseInp {
        tokens,
        errors: &mut errors,
    });

    if errors.is_empty() {
        Ok(result.unwrap())
    } else {
        Err(errors)
    }
}
