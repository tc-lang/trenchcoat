//! Parsing for proof statements

use crate::ast::{Error, ErrorContext, ErrorKind, Ident, ParseRet};
use crate::tokens::{Token, TokenKind};

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

        match Stmt::parse(ts) {
            ParseRet::Ok(s) => stmts.push(s),
            ParseRet::SoftErr(s, es) => {
                stmts.push(s);
                errors.extend(es);
            }
            ParseRet::Err(es) => {
                errors.extend(es);
                return (consumed, ParseRet::Err(errors));
            }
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
    source: &'a [Token<'a>],
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
    /// Conditions in contracts are separated by the 'implies' operator: `=>`. Here is an example:
    /// ```text
    /// # x < 4 => _ < 3
    /// ```
    /// Note that the return value is referred to by the identifier `_`.
    Contract {
        /// The pre-condition
        pre: Condition<'a>,
        /// The post-condition
        post: Condition<'a>,
    },
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
    source: &'a [Token<'a>],
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
}

/// A simple arithmetic expression
///
/// These expressions are always composed either of a single value (a constant or a named variable)
/// or a compound expression, composed of an arithmetic operator and two sub-expressions.
#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
    source: &'a [Token<'a>],
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
}

/// A comparison operator, either `<=` or `>=`.
#[derive(Debug, Clone)]
pub enum CompareOp {
    /// Less than or equal to; `<=`
    Le,
    /// Greater than or equal to; `>=`
    Ge,
}

/// A logical operator, either `&&` or `||`.
#[derive(Debug, Clone)]
pub enum LogicOp {
    /// Logical AND; `&&`
    And,
    /// Logical OR; `||`
    Or,
}

/// An arithemtic operator
#[derive(Debug, Clone)]
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

impl<'a> Stmt<'a> {
    /// Attempts to parse a single proof statment from the all of the tokens composing a proof line
    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, Self> {
        // For a detailed walkthrough of the types of statments we could parse, refer to the
        // documentation for the variants of `StmtKind`.
        todo!()
    }
}

impl<'a> Condition<'a> {
    /// Attempts to parse a condition from the entirety of the given set of tokens
    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, Self> {
        todo!()
    }
}

impl<'a> Expr<'a> {
    fn parse(tokens: &'a [Token<'a>]) -> ParseRet<'a, Self> {
        todo!()
    }
}
