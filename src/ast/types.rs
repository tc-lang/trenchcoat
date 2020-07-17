use super::prelude::*;
use std::ops::Deref;

#[derive(Debug, Clone)]
pub struct Type<'a> {
    pub kind: TypeKind<'a>,
    pub src: &'a [Token<'a>],
}
#[derive(Debug, Clone)]
pub enum TypeKind<'a> {
    Name {
        name: &'a str,
        args: GenericArgs<'a>,
    },
    Enum(Vec<EnumVariant<'a>>),
    Struct {
        unnamed_fields: Vec<Type<'a>>,
        named_fields: Vec<NamedField<'a>>,
        /// True iff the order of fields is specified.
        ordered: bool,
    },
    Slice(Box<Type<'a>>),
    Array {
        len: u64,
        typ: Box<Type<'a>>,
    },
    Ommited,
}

#[derive(Debug, Clone)]
pub struct Trait<'a> {
    pub kind: TraitKind<'a>,
    pub src: &'a [Token<'a>],
}
#[derive(Debug, Clone)]
pub enum TraitKind<'a> {
    Name {
        name: &'a str,
        path: Vec<&'a str>,
        args: GenericArgs<'a>,
    },
}

#[derive(Debug, Clone)]
pub struct EnumVariant<'a> {
    pub name: &'a str,
    pub data: Option<Type<'a>>,
}

#[derive(Debug, Clone)]
pub struct NamedField<'a> {
    pub name: &'a str,
    pub typ: Type<'a>,
}

#[derive(Debug, Clone)]
pub struct GenericParam<'a> {
    pub name: &'a str,
    pub kind: GenericParamKind<'a>,
}

#[derive(Debug, Clone)]
pub enum GenericParamKind<'a> {
    Type(Type<'a>),
    Trait(Trait<'a>),
}

#[derive(Debug, Clone)]
pub struct GenericArgs<'a> {
    pub unnamed: Vec<Type<'a>>,
    pub named: Vec<(&'a str, Type<'a>)>,
}

impl<'a> TypeKind<'a> {
    /// Formatted as {}
    pub const CURLY_UNIT: TypeKind<'a> = TypeKind::Struct {
        unnamed_fields: Vec::new(),
        named_fields: Vec::new(),
        ordered: false,
    };
    /// Formatted as ()
    pub const PAREN_UNIT: TypeKind<'a> = TypeKind::Struct {
        unnamed_fields: Vec::new(),
        named_fields: Vec::new(),
        ordered: true,
    };
}

impl<'a, 'b> Type<'a> {
    pub const OMMITED: Type<'a> = Type {
        kind: TypeKind::Ommited,
        src: &[],
    };

    pub const CURLY_UNIT: Type<'a> = Type {
        kind: TypeKind::CURLY_UNIT,
        src: &[],
    };
    pub const PAREN_UNIT: Type<'a> = Type {
        kind: TypeKind::PAREN_UNIT,
        src: &[],
    };

    parser!(
        pub(crate) fn consume(inp: ParseInp<'a, 'b>) -> ParseRet<Type<'a>> {
            let mut tok_idx = 0;

            use TokenKind::{Ident, Tree};

            ret!(match token!().kind() {
                // Named type
                Some(Ident(name)) => Type {
                    kind: TypeKind::Name {
                        name,
                        args: call!(Type::consume_generic_args),
                    },
                    src: src!(),
                },

                // {..} / (..) / [..]
                Some(Tree { delim, inner, .. }) => match delim {
                    // {..}
                    Delim::Curlies => Type {
                        kind: TypeKind::Struct {
                            named_fields: call!(Type::parse_struct_fields, inner.deref(); false).0,
                            unnamed_fields: Vec::new(),
                            ordered: false,
                        },
                        src: src!(),
                    },

                    // (..)
                    Delim::Parens => Type {
                        kind: call!(Type::parse_tuple, inner.deref()).0,
                        src: src!(),
                    },

                    // [..]
                    Delim::Squares => todo!(),
                },

                // enum
                Some(TokenKind::Keyword(Kwd::Enum)) => todo!(),

                Some(_) => error!(Error {
                    kind: ErrorKind::Expecting {
                        expecting: Expecting::Type,
                        found: Some(last_token!().kind.clone()),
                        context: ExpectingContext::Type,
                    },
                    src: std::slice::from_ref(&last_token!()),
                }),

                None => error!(Error {
                    kind: ErrorKind::Expecting {
                        expecting: Expecting::Type,
                        found: None,
                        context: ExpectingContext::Type,
                    },
                    src: &[],
                }),
            })
        }
    );

    parser!(
        fn parse_tuple(inp: ParseInp<'a, 'b>) -> ParseRet<TypeKind<'a>> {
            let mut tok_idx = 0;

            let mut unnamed_fields = Vec::new();

            // while .. else would be so nice here!
            let named_fields = loop {
                if !has_next!() {
                    break Vec::new();
                }

                let loop_start_tok_idx = tok_idx;
                let typ = call!(Type::consume);

                match token!().kind() {
                    Some(TokenKind::Punctuation(Punc::Comma)) | None => {
                        unnamed_fields.push(typ);
                    }
                    Some(TokenKind::Punctuation(Punc::Colon)) => {
                        // Backtrack to the start of this field and try to parse struct fields.
                        tok_idx = loop_start_tok_idx;
                        break call!(Type::parse_struct_fields; false);
                    }

                    Some(_) => error!(Error {
                        kind: ErrorKind::Expecting {
                            expecting: Expecting::OneOf(&[
                                Expecting::Token(TokenKind::Punctuation(Punc::Comma)),
                                Expecting::Token(TokenKind::Punctuation(Punc::Colon)),
                            ]),
                            found: Some(last_token!().kind.clone()),
                            context: ExpectingContext::TupleCommaOrColon,
                        },
                        src: &inp.tokens[tok_idx - 1..tok_idx],
                    }),
                }
            };

            ret!(TypeKind::Struct {
                unnamed_fields,
                named_fields,
                ordered: true,
            })
        }
    );

    parser!(
        pub(crate) fn parse_struct_fields(
            inp: ParseInp<'a, 'b>;
            allow_inferred_types: bool,
        ) -> ParseRet<Vec<NamedField<'a>>> {
            let mut tok_idx = 0;
            let mut fields = Vec::new();

            punc_separated!(Comma, StructFieldComma, {
                let name = expect_ident!(StructFieldName);
                let typ = if allow_inferred_types {
                    if maybe_punc!(Colon) {
                        call!(Type::consume)
                    } else {
                        Type::OMMITED
                    }
                } else {
                    expect_punc!(Colon, StructFieldColon);
                    call!(Type::consume)
                };
                fields.push(NamedField { name, typ });
            });

            ret!(fields)
        }
    );

    parser!(
        pub(crate) fn consume_generic_params(
            inp: ParseInp<'a, 'b>,
        ) -> ParseRet<Vec<GenericParam<'a>>> {
            let mut tok_idx = 0;

            if !maybe_punc!(Lt) {
                ret!(Vec::new())
            } else {
                let params = call!(Type::consume_generic_params_inner);
                expect_punc!(Gt, CloseGenericParams);
                ret!(params)
            }
        }
    );

    parser!(
        pub(crate) fn consume_generic_params_inner(
            inp: ParseInp<'a, 'b>,
        ) -> ParseRet<Vec<GenericParam<'a>>> {
            let mut tok_idx = 0;

            let mut params = Vec::new();
            punc_separated!(
                Comma,
                GenericParamComma,
                terminators: [Some(TokenKind::Punctuation(Punc::Gt))],
                {
                    let name = expect_ident!(GenericParamName);
                    let kind = mtch_punc!(
                        Colon => GenericParamKind::Type(call!(Type::consume)),
                        ColonColon => GenericParamKind::Trait(call!(Trait::consume));
                        context: GenericParamColon,
                    );
                    params.push(GenericParam { name, kind });
                }
            );
            ret!(params)
        }
    );

    parser!(
        pub(crate) fn consume_generic_args(inp: ParseInp<'a, 'b>) -> ParseRet<GenericArgs<'a>> {
            let mut tok_idx = 0;

            if !maybe_punc!(Lt) {
                ret!(GenericArgs {
                    unnamed: Vec::new(),
                    named: Vec::new(),
                })
            } else {
                let params = call!(Type::consume_generic_args_inner);
                expect_punc!(Gt, CloseGenericArgs);
                ret!(params)
            }
        }
    );

    parser!(
        pub(crate) fn consume_generic_args_inner(
            inp: ParseInp<'a, 'b>,
        ) -> ParseRet<GenericArgs<'a>> {
            let mut tok_idx = 0;

            let mut unnamed = Vec::new();
            punc_separated!(
                Comma,
                GenericArgComma,
                terminators: [Some(TokenKind::Punctuation(Punc::Gt))],
                {
                    unnamed.push(call!(Type::consume));
                }
            );
            ret!(GenericArgs {
                unnamed,
                named: Vec::new(),
            })
        }
    );
}

impl<'a, 'b> Trait<'a> {
    parser!(
        pub(crate) fn consume(inp: ParseInp<'a, 'b>) -> ParseRet<Trait<'a>> {
            let mut tok_idx = 0;

            ret!(Trait {
                kind: TraitKind::Name {
                    name: expect_ident!(TraitName),
                    path: Vec::new(),
                    args: call!(Type::consume_generic_args),
                },
                src: src!(),
            })
        }
    );
}
