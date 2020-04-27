//! The production of the abstract syntax tree for a source file

use crate::tokens::Token;

////////////////////////////////////////////////////////////////////////////////
// Top-level interface                                                        //
////////////////////////////////////////////////////////////////////////////////

pub fn try_parse<'a>(tokens: &'a [Token<'a>]) -> Result<Vec<Item<'a>>, Vec<AstError>> {
    let mut items = Vec::new();

    // Our place in the list of tokens
    let mut idx = 0;

    while idx < tokens.len() {
        let item = Item::parse(tokens)?;
        idx += item.consumed();
        items.push(item);
    }

    Ok(items)
}

////////////////////////////////////////////////////////////////////////////////
// Type definitions                                                           //
////////////////////////////////////////////////////////////////////////////////

/// Currently nothing's here because parsing hasn't been implemented yet!
#[derive(Debug)]
pub enum AstError {}

#[derive(Debug)]
pub struct Item<'a> {
    kind: ItemKind<'a>,
    source: &'a [Token<'a>],
}

#[derive(Debug)]
pub struct Stmt<'a> {
    kind: ExprKind<'a>,
    source: &'a [Token<'a>],
}

#[derive(Debug)]
pub struct Expr<'a> {
    kind: ExprKind<'a>,
    source: &'a [Token<'a>],
}

/// A top-level item in the source
///
/// Currently only function declarations are supported.
#[derive(Debug)]
pub enum ItemKind<'a> {
    FnDecl {
        name: Ident<'a>,
        params: FnParams<'a>,
        body: Vec<Stmt<'a>>,
        tail: Option<Expr<'a>>,
    },
}

#[derive(Debug)]
pub struct Ident<'a> {
    name: &'a str,
    source: &'a Token<'a>,
}

pub type FnArgs<'a> = Vec<Expr<'a>>;
pub type FnParams<'a> = Vec<Ident<'a>>;

/// A semicolon-terminated statement
#[derive(Debug)]
pub enum StmtKind<'a> {
    /// A `let` statement binding a value given by the `Expr` to a variable name given by the
    /// identifier. For example: `let x = g(y);`
    Let(Ident<'a>, Expr<'a>),

    /// An assignemnt, e.g. `x = 4;`. In this example, 'x' would be the `Ident`, and '4' would be
    /// the `Expr`
    Assign(Ident<'a>, Expr<'a>),

    /// Printing a value, e.g. `print foo(1);`
    Print(Expr<'a>),

    /// The simple evaluation of a single expression, treated as a statement. This might be
    /// something like: `foo(bar(3));`, where `foo` and `bar` might have side effects.
    Eval(Expr<'a>),
}

#[derive(Debug)]
pub enum ExprKind<'a> {
    /// An expression representing a function call. The left-hand `Expr` is the function, and the
    /// right-hand `FnArgs` gives its arguments.
    FnCall(Box<Expr<'a>>, FnArgs<'a>),

    /// An expression produced from a binary operator. The elements of the tuple are placed as they
    /// would be in the source (i.e. the left-hand `Expr` is the left-hand argument to the
    /// operator). For example: `3 + 4`
    BinOp(Box<Expr<'a>>, BinOp, Box<Expr<'a>>),

    /// A prefix operator expression, e.g. `!f(x)` or `&y`
    PrefixOp(PrefixOp, Box<Expr<'a>>),

    /// An expression that simply references the value of a variable, e.g. `x` or `foo`.
    Named(Ident<'a>),

    /// A raw number, e.g. `420`
    Num(usize),

    /// A bracketed expression, using either curly-braces or parentheses. For example: `(x + y)` or
    /// `{ foo(x); y }`
    Bracket(Vec<Stmt<'a>>, Box<Expr<'a>>),
}

/// A binary operator
#[derive(Debug)]
pub enum BinOp {
    /// Addition: `+`
    Add,
    /// Subtraction: `-`
    Sub,
    /// Multiplication: `*`
    Mul,
    /// Division: `/`
    Div,
    /// Equality: `==`
    Eq,
    /// Less than: `<`
    Lt,
    /// Less than or equal to: `<=`
    Le,
    /// Greater than: `>`
    Gt,
    /// Greater than or equal to: `>=`
    Ge,
    /// Logical "or": `||`
    Or,
    /// Logical "and": `&&`
    And,
}

/// A prefix operator. This is currently lacking most of the prefix operators that will be added
/// later. This is intentional.
#[derive(Debug)]
pub enum PrefixOp {
    /// Unary not: `!`
    Not,
}

////////////////////////////////////////////////////////////////////////////////
// Implementations and other functions                                        //
//                                                                            //
// These are ordered by the required recusive depth from the top-level        //
// `try_parse` to reach them.                                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

type FnDecl<'a> = (Ident<'a>, FnParams<'a>, Vec<Stmt<'a>>, Option<Expr<'a>>);

impl<'a> Item<'a> {
    /// Returns the number of tokens consumed to produce this type
    fn consumed(&self) -> usize {
        self.source.len()
    }

    /// Attempts to parse the set of tokens into an item, returning the number of tokens consumed
    /// if successful.
    fn parse(tokens: &'a [Token<'a>]) -> Result<Self, Vec<AstError>> {
        let (fn_decl, consumed) = Self::parse_fn_decl(tokens)?;
        let (name, params, body, tail) = fn_decl;
        Ok(Item {
            source: &tokens[..consumed],
            kind: ItemKind::FnDecl {
                name,
                params,
                body,
                tail,
            },
        })
    }

    fn parse_fn_decl(tokens: &'a [Token<'a>]) -> Result<(FnDecl<'a>, usize), Vec<AstError>> {
        todo!()
    }
}
