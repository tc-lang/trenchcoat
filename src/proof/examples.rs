use super::expr::{Atom, Expr, ONE, ZERO};
use super::optimiser::{Maximizer, Minimizer};
use super::{Relation, RelationKind};
use super::bound_method::FullProver;
use crate::ast::{self, Ident};

/*
pub fn examples() {
    /// Parse tokens into and Expr
    fn parse_expr<'a>(tokens: &'a [crate::tokens::Token<'a>]) -> Expr<'a> {
        match ast::proof::Expr::parse(tokens) {
            ast::ParseRet::Ok(expr) => Expr::from(expr),
            ast::ParseRet::Err(errs) | ast::ParseRet::SoftErr(_, errs) => {
                panic!(format!("{:?}", errs))
            }
        }
    }

    use crate::tokens::{tokenize, FAKE_TOKEN};

    // should simplify to 2*x*y
    let tokens = tokenize("y * x/y * 1/x * x * y + 2 + x + y + 3 - 5 - x*y + 2*x*y - 2*x - y + x");
    let mut expr = parse_expr(&tokens);
    println!("1.0) {}", expr);
    expr = expr.simplify();
    println!("1.1) {}", expr);

    /*
    let tokens = tokenize("x + z*x + x*y + 2*x + 3 - y");
    let mut expr = parse_expr(&tokens);
    println!("2.0) {}", expr);
    expr = expr.simplify();
    println!("2.1) {}", expr);
    let x = Expr::Atom(Atom::Named(Ident {
        name: "x",
        source: &FAKE_TOKEN,
    }));
    expr = expr.single_x(&x).unwrap();
    println!("2.2) {}", expr);
    let mut x_bounds = Relation {
        left: expr.clone(),
        relation: RelationKind::Le,
        right: ZERO,
    }
    .rearrange_unsafe(&x)
    .unwrap();
    x_bounds.right = x_bounds.right.simplify();
    println!("2.3) {}", x_bounds);

    let tokens = tokenize("1/x - y");
    let mut expr = parse_expr(&tokens);
    println!("3.0) {}", expr);
    expr = expr.simplify();
    println!("3.1) {}", expr);
    let x = Expr::Atom(Atom::Named(Ident {
        name: "x",
        source: &FAKE_TOKEN,
    }));

    expr = expr.single_x(&x).unwrap();
    println!("3.2) {}", expr);
    let mut x_bounds = Relation {
        left: expr.clone(),
        relation: RelationKind::Le,
        right: ZERO,
    }
    .rearrange_unsafe(&x)
    .unwrap();
    x_bounds.right = x_bounds.right.simplify();
    println!("3.3) {}", x_bounds);
    */

    let tokens = tokenize("10 - 2*x - y/4");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr); // so 10 - 2*x - y/4 >= 0
    for (variable, bound) in cond.bounds() {
        println!("{} {}", variable, bound.simplify());
    }

    fn is_literal(expr: &Expr) -> bool {
        match expr {
            Expr::Atom(Atom::Literal(_)) => true,
            Expr::Neg(inner) => match **inner {
                Expr::Atom(Atom::Literal(_)) => true,
                _ => false,
            },
            _ => false,
        }
    }

    let tokens = tokenize("10 - x - y");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr); // so  10 - x - y >= 0  thus  x + y <= 10
    for (variable, bound) in cond.bounds() {
        println!("{} {}", variable, bound.simplify());
    }

    let mut given = cond.bounds();

    let tokens = tokenize("x");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr); // so x >= 0
    given.extend(cond.bounds());

    let tokens = tokenize("y");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr.clone()); // so y >= 0
    given.extend(cond.bounds());

    let tokens = tokenize("7-x");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr.clone()); // so 7 >= x
    given.extend(cond.bounds());

    let tokens = tokenize("17-2*y");
    let expr = parse_expr(&tokens);
    let cond = Condition::Ge0(expr.clone()); // so 17 >= 2*y
    given.extend(cond.bounds());

    given = given
        .iter()
        .map(|(x, bound)| (*x, bound.simplify()))
        .collect();

    println!("Let's bound y");
    for (x, bound) in given.clone() {
        println!("Given {} {}", x, bound);
    }

    let tokens = tokenize("y");
    let expr = parse_expr(&tokens);
    let mini = Minimizer::new(given.clone(), expr.clone(), 10).int_bounds();
    for bound in mini {
        println!("y >= {}", bound);
    }

    let maxi = Maximizer::new(given.clone(), expr, 10).int_bounds();
    for bound in maxi {
        println!("y <= {}", bound);
    }

    println!("Let's bound x+y");
    for (x, bound) in given.clone() {
        println!("Given {} {}", x, bound);
    }

    let tokens = tokenize("x+y");
    let expr = parse_expr(&tokens);
    let mini = Minimizer::new(given.clone(), expr.clone(), 10).int_bounds();
    for bound in mini {
        println!("x+y >= {}", bound);
    }

    let maxi = Maximizer::new(given.clone(), expr, 10).int_bounds();
    for bound in maxi {
        println!("x+y <= {}", bound);
    }

    println!("Let's bound 2*x+y");
    for (x, bound) in given.clone() {
        println!("Given {} {}", x, bound);
    }

    let tokens = tokenize("2*x+y");
    let expr = parse_expr(&tokens).simplify();
    let mini = Minimizer::new(given.clone(), expr.clone(), 10).int_bounds();
    for bound in mini {
        println!("2*x+y >= {}", bound);
    }

    let maxi = Maximizer::new(given, expr, 10).int_bounds();
    for bound in maxi {
        println!("2*x+y <= {}", bound);
    }
}
*/
