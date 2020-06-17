//! Parsing for proof statements

use crate::ast::{Error, ErrorContext, ErrorKind, Ident, IdentSource, Node, ParseRet};
use crate::tokens::{self, Oper, Token, TokenKind};
use std::convert::{TryFrom, TryInto};

/// Consumes all given lines of proof
pub(super) fn consume_proof_lines<'a>(
    tokens: &'a [Token<'a>],
) -> (usize, ParseRet<'a, Vec<Stmt<'a>>>) {
    let mut stmts = Vec::new();
    let mut errors = Vec::new();

    for (consumed, t) in tokens.iter().enumerate() {
        let ts = match &t.kind {
            TokenKind::ProofLine(ts) => ts,
            _ => return (consumed, ParseRet::with_soft_errs(stmts, errors)),
        };

        // The success type of `Stmt::parse` is an `Option<Stmt>`, because empty proof lines are
        // allowed.
        let stmt: Option<Stmt> = match Stmt::parse(ts) {
            ParseRet::Ok(s) => s,
            ParseRet::SoftErr(s, es) => {
                errors.extend(es);
                s
            }
            ParseRet::Err(es) => {
                errors.extend(es);
                return (consumed, ParseRet::Err(errors));
            }
        };

        if let Some(s) = stmt {
            stmts.push(s);
        }
    }

    (tokens.len(), ParseRet::with_soft_errs(stmts, errors))
}

/// A single proof statement
///
/// While this shares a name with `ast::Stmt`, it bears no other relation to that type.
#[derive(Debug, Clone)]
pub struct Stmt<'a> {
    pub kind: StmtKind<'a>,

    /// The source of the proof statement. These will always exactly use a single line, so the
    /// source token has kind `TokenKind::ProofLine`.
    pub source: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
pub enum StmtKind<'a> {
    /// A 'require' statement indicates some form of strict requirement for function arguments.
    /// Here are a couple examples:
    /// ```text
    /// # require x <= 4
    /// ```
    /// and
    /// ```text
    /// # require x + y >= z - x
    /// ```
    Require(Condition<'a>),

    /// A contract indicates a promise by the function; if a certain condition is met of the
    /// inputs, a separate condition will be met by the output.
    ///
    /// Conditions in contracts are separated by the 'implies' operator, `=>`. Here is an example:
    /// ```text
    /// # x < 4 => _ < 3
    /// ```
    /// Note that the return value is referred to by the identifier `_`.
    Contract {
        /// The pre-condition
        ///
        /// This is optional in order to allow unconditional return values. This could be written
        /// as the following:
        /// ```text
        /// # => _ >= x
        /// ```
        /// where the return value is given to be always greater than or equal to some input `x`.
        pre: Option<Condition<'a>>,

        /// The post-condition
        post: Condition<'a>,
    },

    /// A sentinel value for signaling a failure to parse a statement, when we don't want to give a
    /// hard error.
    Malformed,
}

/// A generic condition, e.g. `x + 4 < y` or `3 * _ >= z`.
///
/// A condition is broken into three parts: two expressions and a comparison operator between them.
/// The following diagram illustrates each of the parts of the condition for the example of
/// `x + 4 < y`:
/// ```text
///   x + 4 < y
///   ──┬── ┬ ┬
///    lhs  │ └ rhs
///        op
/// ```
///
/// It is worth noting that many *syntactically valid* conditions will never be semantically valid.
/// For example: `x - 4` is a syntactically valid condition but cannot be semantically valid
/// because there is no actual condition on `x`.
#[derive(Debug, Clone)]
pub struct Condition<'a> {
    pub kind: ConditionKind<'a>,
    pub source: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
pub enum ConditionKind<'a> {
    /// A condition composed of two conditions, joined by a logical operator
    Compound {
        lhs: Box<Condition<'a>>,
        op: LogicOp,
        rhs: Box<Condition<'a>>,
    },
    /// A simple condition; two expressions, joined by a comparison operator
    Simple {
        lhs: Expr<'a>,
        op: CompareOp,
        rhs: Expr<'a>,
    },
    /// A sentinel value for a failure to parse
    Malformed,
}

/// A simple arithmetic expression
///
/// These expressions are always composed either of a single value (a constant or a named variable)
/// or a compound expression, composed of an arithmetic operator and two sub-expressions.
#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
    pub source: &'a [Token<'a>],
}

#[derive(Debug, Clone)]
pub enum ExprKind<'a> {
    Compound {
        lhs: Box<Expr<'a>>,
        op: ArithOp,
        rhs: Box<Expr<'a>>,
    },

    Named(Ident<'a>),

    // TODO: It might be the case that this shouldn't be an isize, so that we can allow values
    // above isize::MAX in proof statments, but this should be discussed further.
    Literal(isize),

    /// A malformed expression. This is used as a sentinel value for places where an error has
    /// already occured in parsing, but we don't want to give a 'hard' error.
    Malformed,
}

/// A comparison operator, either `<=` or `>=`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum CompareOp {
    /// Less than or equal to; `<=`
    Le,
    /// Greater than or equal to; `>=`
    Ge,
}

/// A logical operator, either `&&` or `||`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum LogicOp {
    /// Logical AND; `&&`
    And,
    /// Logical OR; `||`
    Or,
}

/// An arithemtic operator
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ArithOp {
    /// Addition; `+`
    Add,
    /// Subtraction; `-`
    Sub,
    /// Multiplication; `*`
    Mul,
    /// Division; `/`
    Div,
    // The modulo operator is intentionally left out
}

// These are ordered by precedence from least to greatest
static LOGIC_OP_PRECEDENCE: &[LogicOp] = &[LogicOp::Or, LogicOp::And];
static ARITH_OP_PRECEDENCE: &[&[ArithOp]] =
    &[&[ArithOp::Add, ArithOp::Sub], &[ArithOp::Mul, ArithOp::Div]];

impl TryFrom<Oper> for CompareOp {
    type Error = ();

    fn try_from(op: Oper) -> Result<CompareOp, ()> {
        use CompareOp::{Ge, Le};

        match op {
            Oper::LtOrEqual => Ok(Le),
            Oper::GtOrEqual => Ok(Ge),
            _ => Err(()),
        }
    }
}

impl TryFrom<Oper> for LogicOp {
    type Error = ();

    fn try_from(op: Oper) -> Result<LogicOp, ()> {
        use LogicOp::{And, Or};

        match op {
            Oper::And => Ok(And),
            Oper::Or => Ok(Or),
            _ => Err(()),
        }
    }
}

impl TryFrom<Oper> for ArithOp {
    type Error = ();

    fn try_from(op: Oper) -> Result<ArithOp, ()> {
        use ArithOp::{Add, Div, Mul, Sub};

        match op {
            Oper::Add => Ok(Add),
            Oper::Sub => Ok(Sub),
            Oper::Star => Ok(Mul),
            Oper::Div => Ok(Div),
            _ => Err(()),
        }
    }
}

impl<'a> Stmt<'a> {
    /// Produces an AST node containing the proof statement
    pub fn node(&'a self) -> Node<'a> {
        Node::ProofStmt(self)
    }

    /// Attempts to parse a single proof statment from the all of the tokens composing a proof line
    ///
    /// This function will return `None` if and only if the input set of tokens is empty; this
    /// symbolizes an empty proof line.
    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, Option<Self>> {
        // For a detailed walkthrough of the types of statments we could parse, refer to the
        // documentation for the variants of `StmtKind`.

        // If there are no tokens, it's an empty statement
        if tokens.is_empty() {
            return ParseRet::Ok(None);
        }

        Stmt::parse_require(tokens)
            .unwrap_or_else(|| Stmt::parse_contract(tokens))
            // Wrap the inner `Stmt` into an `Option<Stmt>`
            .map(Some)
    }

    /// Attempts to parse a 'require' statment from the entire given set of tokens
    ///
    /// A 'require' statement starts with the `require` keyword, and is followed by a condition.
    fn parse_require(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        use tokens::Keyword::Require;
        use TokenKind::Keyword;

        match &tokens[0].kind {
            Keyword(Require) => (),
            _ => return None,
        }

        let stmt_res = Condition::parse(&tokens[1..]).map(|cond| Stmt {
            kind: StmtKind::Require(cond),
            source: tokens,
        });

        Some(stmt_res)
    }

    /// Attempts to parse a contract statement from the entire set of tokens
    fn parse_contract(tokens: &'a [Token<'a>]) -> ParseRet<'a, Self> {
        // A contract consists of two conditions, separated by a `=>` (Oper::Implies) token
        // The first condition is optional, so we split based on the first instance of `=>`

        let conditions = tokens
            .split(|t| t.kind == TokenKind::Oper(Oper::Implies))
            .collect::<Vec<_>>();

        if conditions.len() != 2 {
            let malformed_stmt = Stmt {
                kind: StmtKind::Malformed,
                source: tokens,
            };

            let err = match conditions.len() {
                1 => Error {
                    kind: ErrorKind::SingleContractCondition,
                    context: ErrorContext::ProofStmt,
                    source: tokens.first(),
                },
                n => Error {
                    kind: ErrorKind::TooManyContractConditions(n),
                    context: ErrorContext::ProofStmt,
                    source: tokens.first(),
                },
            };

            return ParseRet::SoftErr(malformed_stmt, vec![err]);
        }

        let mut errors = Vec::new();

        let pre = match conditions[0].is_empty() {
            true => None,
            false => Some(next!(Condition::parse(conditions[0]), errors)),
        };

        let post = next!(Condition::parse(conditions[1]), errors);

        ParseRet::with_soft_errs(
            Stmt {
                source: tokens,
                kind: StmtKind::Contract { pre, post },
            },
            errors,
        )
    }
}

impl<'a> Condition<'a> {
    pub fn node(&'a self) -> Node<'a> {
        Node::ProofCond(self)
    }

    /// Attempts to parse a condition from the entirety of the given set of tokens
    pub fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, Self> {
        // There are fundamentally two types of conditions: compound conditions, which consist of a
        // condition joined by a logical operator, and 'simple' conditions, which consist of two
        // (integer-valued) expressions joined by a comparison operator.
        //
        // So: If there's a logical operator, we'll create a compound condition from it, and if
        // there isn't, we'll try to parse a simple condition.
        //
        // This algorithm is O(n^2) but that's okay for now.

        // We'll search for a logic operator and split there if possible.

        let logic_op_indices = tokens
            .iter()
            .enumerate()
            .filter_map(|(i, t)| match t.kind {
                TokenKind::Oper(op) => op.try_into().ok().map(|op: LogicOp| (i, op)),
                _ => None,
            })
            // // We don't need to reverse here because associativity doesn't affect logical
            // // operators
            // .rev()
            .collect::<Vec<_>>();

        for op in LOGIC_OP_PRECEDENCE.iter() {
            // Check if there's a token that will give us the operator we want
            if let Some((idx, _)) = logic_op_indices.iter().find(|(_, o)| o == op) {
                // We found an operator that'll work, so we'll split and recursively parse
                let mut errors = Vec::new();
                let lhs = next!(Condition::parse(&tokens[..*idx]), errors);
                let rhs = next!(
                    Condition::parse(tokens.get(idx + 1..).unwrap_or(&[])),
                    //               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                    // We need to use `get` here in order to accound for the possibility of a trailing
                    // operator; if idx + 1 = tokens.len, evaluating tokens[idx+1..] will panic.
                    errors
                );

                let cond = Condition {
                    source: tokens,
                    kind: ConditionKind::Compound {
                        lhs: Box::new(lhs),
                        op: *op,
                        rhs: Box::new(rhs),
                    },
                };

                return ParseRet::with_soft_errs(cond, errors);
            }
        }

        // Because there wasn't a logical operator, we'll expect a single comparison operator.
        // We collect all possible matches and then check that the number matches what is expected
        let compare_op_indices = tokens
            .iter()
            .enumerate()
            .filter_map(|(i, t)| match t.kind {
                TokenKind::Oper(op) => op.try_into().ok().map(|op: CompareOp| (i, op)),
                _ => None,
            })
            .collect::<Vec<_>>();

        match compare_op_indices.len() {
            1 => (),
            0 => {
                return ParseRet::SoftErr(
                    Condition {
                        kind: ConditionKind::Malformed,
                        source: tokens,
                    },
                    vec![Error {
                        kind: ErrorKind::CondWithoutCompareOp,
                        context: ErrorContext::ProofCond,
                        source: tokens.first(),
                    }],
                )
            }
            _ => {
                return ParseRet::SoftErr(
                    Condition {
                        kind: ConditionKind::Malformed,
                        source: tokens,
                    },
                    vec![Error {
                        kind: ErrorKind::ChainedComparison,
                        context: ErrorContext::ProofCond,
                        source: tokens.first(),
                    }],
                )
            }
        }

        // There's a single copmarsion operator, so we split along that

        let (op_idx, op) = compare_op_indices[0];
        let mut errors = Vec::new();
        let lhs = next!(Expr::parse(&tokens[..op_idx]), errors);
        let rhs = next!(Expr::parse(tokens.get(op_idx + 1..).unwrap_or(&[])), errors);

        let cond = Condition {
            source: tokens,
            kind: ConditionKind::Simple { lhs, op, rhs },
        };

        ParseRet::with_soft_errs(cond, errors)
    }
}

impl<'a> Expr<'a> {
    pub fn parse(mut tokens: &'a [Token<'a>]) -> ParseRet<'a, Self> {
        // If the tokens have been parenthesized, we'll expand those
        if tokens.len() == 1 {
            match &tokens[0].kind {
                TokenKind::Parens(ts) => tokens = &ts,
                _ => (),
            }
        }

        Expr::parse_named(tokens)
            .or_else(|| Expr::parse_literal(tokens))
            .or_else(|| Expr::parse_compound(tokens))
            .unwrap_or_else(|| {
                let expr = Expr {
                    kind: ExprKind::Malformed,
                    source: tokens,
                };

                let err = Error {
                    kind: ErrorKind::ExpectingExpr,
                    context: ErrorContext::ProofExpr,
                    source: tokens.first(),
                };

                ParseRet::SoftErr(expr, vec![err])
            })
    }

    fn parse_named(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        match tokens {
            [ref t] => match t.kind {
                TokenKind::NameIdent(name) => Some(ParseRet::Ok(Expr {
                    kind: ExprKind::Named(Ident {
                        name,
                        source: IdentSource::Token(t),
                    }),
                    source: tokens,
                })),
                _ => None,
            },
            _ => None,
        }
    }

    fn parse_literal(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        match tokens {
            [ref t] => match t.kind {
                TokenKind::Num(name) => match name.parse::<isize>() {
                    Err(_) => Some(ParseRet::SoftErr(
                        Expr {
                            kind: ExprKind::Malformed,
                            source: tokens,
                        },
                        vec![Error {
                            kind: ErrorKind::IntegerValueTooLarge,
                            context: ErrorContext::ProofExpr,
                            source: Some(t),
                        }],
                    )),
                    Ok(n) => Some(ParseRet::Ok(Expr {
                        kind: ExprKind::Literal(n),
                        source: tokens,
                    })),
                },
                _ => None,
            },
            _ => None,
        }
    }

    fn parse_compound(tokens: &'a [Token<'a>]) -> Option<ParseRet<'a, Self>> {
        let op_indices = tokens
            .iter()
            .enumerate()
            .filter_map(|(i, t)| match t.kind {
                TokenKind::Oper(op) => op.try_into().ok().map(|op: ArithOp| (i, op)),
                _ => None,
            })
            .rev() // Reversing because these operators are left-associative
            .collect::<Vec<_>>();

        for ops in ARITH_OP_PRECEDENCE.iter() {
            for &op in ops.iter() {
                if let Some((idx, _)) = op_indices.iter().find(|(_, o)| *o == op) {
                    use ParseRet::{Err, Ok, SoftErr};

                    let mut errors = Vec::new();

                    let lhs = match Expr::parse(&tokens[..*idx]) {
                        Ok(expr) => Box::new(expr),
                        SoftErr(expr, es) => {
                            errors.extend(es);
                            Box::new(expr)
                        }
                        Err(es) => return Some(Err(es)),
                    };

                    let rhs = match Expr::parse(tokens.get(idx + 1..).unwrap_or(&[])) {
                        Ok(expr) => Box::new(expr),
                        SoftErr(expr, es) => {
                            errors.extend(es);
                            Box::new(expr)
                        }
                        Err(es) => {
                            errors.extend(es);
                            return Some(Err(errors));
                        }
                    };

                    let expr = Expr {
                        kind: ExprKind::Compound { lhs, op, rhs },
                        source: tokens,
                    };

                    return Some(ParseRet::with_soft_errs(expr, errors));
                }
            }
        }

        // If we couldn't find an operator, this isn't a compound expression
        None
    }
}
