use super::bound_method::{FullProver, Prover as BoundsProver};
use super::{ProofResult, Prover, Requirement, SimpleProver};
use crate::ast::proof::Condition;
use crate::tokens::tokenize;

fn prove<'a>(prover: &impl Prover<'a>, stmt: &'a str) -> ProofResult {
    let tokens = tokenize(stmt);
    let cond = Condition::parse(&tokens).unwrap();
    let req = Requirement::from(&cond);
    prover.prove(&req)
}

#[test]
fn example_test() {
    // Also, to get an idea for the running time of the algorithm, this would be the time for a
    // function with 5 requirements and 21 unique statements to prove.

    // These are our function requirements
    let cond0 = tokenize("x >= 0");
    let cond1 = tokenize("0 <= y");
    let cond2 = tokenize("x+y <= 10");
    let cond3 = tokenize("2*y <= 17");
    let cond4 = tokenize("x/2+y >= 1");
    // y <= 7?
    // 1-x/2 <= y <= 7
    // -6 <= x/2

    let cond0 = Condition::parse(&cond0).unwrap();
    let cond1 = Condition::parse(&cond1).unwrap();
    let cond2 = Condition::parse(&cond2).unwrap();
    let cond3 = Condition::parse(&cond3).unwrap();
    let cond4 = Condition::parse(&cond4).unwrap();

    let mut reqs = Vec::new();
    reqs.push(Requirement::from(&cond0));
    reqs.push(Requirement::from(&cond1));
    reqs.push(Requirement::from(&cond2));
    reqs.push(Requirement::from(&cond3));
    reqs.push(Requirement::from(&cond4));

    let mut bounds_prover = BoundsProver::new(reqs.clone());
    // We can garentee that this will be worst case O(n^4)
    bounds_prover.set_max_depth(4);
    let prover = FullProver::from(bounds_prover);

    /*
    let tokens = tokenize("8 - y");
    let expr = crate::ast::proof::Expr::parse(&tokens).unwrap();

    let mini = super::optimiser::Minimizer::new(
        reqs.iter()
            .map(|req| {
                req.simplify()
                    .bounds()
                    .iter()
                    .map(|(ident, bound)| (*ident, bound.simplify()))
                    .collect()
            })
            .collect(),
        super::expr::Expr::from(&expr).simplify(),
        6,
    );
    let mut bounds = mini.collect::<Vec<super::expr::Expr>>();
    //let mut bounds = mini.int_bounds().collect::<Vec<super::int::Int>>();
    bounds.dedup();
    for bound in bounds.iter() {
        print!("YIELDS {}", bound);
        match bound.eval() {
            Some(x) => println!(" = {}", x),
            None => println!(""),
        };
    }
    */
    //panic!("Hi");

    //println!("{:?}", prove(&prover, "2*x+y <= 18"));
    //println!("{:?}", prove(&prover, "x+y <= 10"));
    //println!("{:?}", prove(&prover, "x <= 10"));
    //println!("{:?}", prove(&prover, "x <= 9"));
    //println!("{:?}", prove(&prover, "1 <= y"));
    //println!("{:?}", prove(&prover, "2*x+y <= 19"));
    //println!("{:?}", prove(&prover, "x+y <= 9"));
    //assert!(prove(&prover, "x+y <= 10") == ProofResult::True);

    // First off, let's start with the obvious proofs
    assert!(prove(&prover, "0 <= x") == ProofResult::True);
    assert!(prove(&prover, "0 <= y") == ProofResult::True);
    assert!(prove(&prover, "x+y <= 10") == ProofResult::True);
    // We can also say that
    assert!(prove(&prover, "0-3 <= x") == ProofResult::True);
    // But
    assert!(prove(&prover, "3 <= x") == ProofResult::Undetermined);
    // and
    assert!(prove(&prover, "11 <= x") == ProofResult::False);
    // Or that
    assert!(prove(&prover, "x <= 10") == ProofResult::True);
    assert!(prove(&prover, "y <= 10") == ProofResult::True);
    // In fact, 2*y <= 17 ==> y <= 8
    assert!(prove(&prover, "y <= 8") == ProofResult::True);
    // If we go too tight though, y *could* be in that range, but it won't always be:
    assert!(prove(&prover, "y <= 7") == ProofResult::Undetermined);
    assert!(prove(&prover, "y <= 5") == ProofResult::Undetermined);
    // Or, if we go crazy, the result is always false:
    assert!(prove(&prover, "y <= 0-1") == ProofResult::False);
    // We could also make some other combinations:
    assert!(prove(&prover, "2*x+y <= 20") == ProofResult::True);
    assert!(prove(&prover, "x+2*y <= 20") == ProofResult::True);
    assert!(prove(&prover, "x+2*y >= 0") == ProofResult::True);
    // And duplicating the above, using parentheticals
    assert!(prove(&prover, "2*(x+y)-y <= 20") == ProofResult::True);
    assert!(prove(&prover, "2*(x+y)-x <= 20") == ProofResult::True);
    assert!(prove(&prover, "2*(x+y)-x >= 0") == ProofResult::True);
    // Also, x/2 + y >= 1
    //   ==> x + 2*y >= 2
    assert!(prove(&prover, "x+2*y >= 1") == ProofResult::True);
    assert!(prove(&prover, "x+2*y >= 2") == ProofResult::True);
    assert!(prove(&prover, "x+2*y >= 3") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+2*y >= 31") == ProofResult::False);

    assert!(prove(&prover, "2*x+y <= 19") == ProofResult::Undetermined);

    // With some tighter bounds!
    assert!(prove(&prover, "x+2*y <= 18") == ProofResult::True);
    assert!(prove(&prover, "x+2*y <= 17") == ProofResult::Undetermined);
}

#[test]
fn test_3_vars_different_coeffs() {
    // These are our function requirements
    let cond0 = tokenize("x <= y+3");
    let cond1 = tokenize("x <= 2*y");
    let cond2 = tokenize("y <= z+2");

    let cond0 = Condition::parse(&cond0).unwrap();
    let cond1 = Condition::parse(&cond1).unwrap();
    let cond2 = Condition::parse(&cond2).unwrap();

    let mut reqs = Vec::new();
    reqs.push(Requirement::from(&cond0));
    reqs.push(Requirement::from(&cond1));
    reqs.push(Requirement::from(&cond2));

    let mut bounds_prover = BoundsProver::new(reqs);
    // We can garentee that this will be worst case O(n^3)
    bounds_prover.set_max_depth(3);
    let prover = FullProver::from(bounds_prover);

    assert!(prove(&prover, "x <= z+5") == ProofResult::True);
}

#[test]
fn test_3_variables_different_coeffs_2() {
    // These are our function requirements
    let cond0 = tokenize("x <= y+3");
    let cond1 = tokenize("x <= 2*y");
    let cond2 = tokenize("y <= z/2+2");

    let cond0 = Condition::parse(&cond0).unwrap();
    let cond1 = Condition::parse(&cond1).unwrap();
    let cond2 = Condition::parse(&cond2).unwrap();

    let mut reqs = Vec::new();
    reqs.push(Requirement::from(&cond0));
    reqs.push(Requirement::from(&cond1));
    reqs.push(Requirement::from(&cond2));

    let mut bounds_prover = BoundsProver::new(reqs);
    // We can garentee that this will be worst case O(n^3)
    bounds_prover.set_max_depth(3);
    let prover = FullProver::from(bounds_prover);

    assert!(prove(&prover, "x <= z+4") == ProofResult::True);
}

#[test]
fn test_3_variables() {
    // These are our function requirements
    let cond0 = tokenize("0-10 <= x");
    let cond1 = tokenize("x <= 10");
    let cond2 = tokenize("0-6 <= y");
    let cond3 = tokenize("y <= 7-z");
    let cond4 = tokenize("0-1 <= z");
    let cond5 = tokenize("z <= 3");

    let cond0 = Condition::parse(&cond0).unwrap();
    let cond1 = Condition::parse(&cond1).unwrap();
    let cond2 = Condition::parse(&cond2).unwrap();
    let cond3 = Condition::parse(&cond3).unwrap();
    let cond4 = Condition::parse(&cond4).unwrap();
    let cond5 = Condition::parse(&cond5).unwrap();

    let mut reqs = Vec::new();
    reqs.push(Requirement::from(&cond0));
    reqs.push(Requirement::from(&cond1));
    reqs.push(Requirement::from(&cond2));
    reqs.push(Requirement::from(&cond3));
    reqs.push(Requirement::from(&cond4));
    reqs.push(Requirement::from(&cond5));

    let mut bounds_prover = BoundsProver::new(reqs);
    bounds_prover.set_max_depth(4);
    let prover = FullProver::from(bounds_prover);

    assert!(prove(&prover, "x <= 11") == ProofResult::True);
    assert!(prove(&prover, "x <= 10") == ProofResult::True);
    assert!(prove(&prover, "x <= 9") == ProofResult::Undetermined);
    assert!(prove(&prover, "0-11 <= x") == ProofResult::True);
    assert!(prove(&prover, "0-10 <= x") == ProofResult::True);
    assert!(prove(&prover, "0-9 <= x") == ProofResult::Undetermined);
    assert!(prove(&prover, "11 <= x") == ProofResult::False);
    assert!(prove(&prover, "12 <= x") == ProofResult::False);
    assert!(prove(&prover, "x <= 0-10") == ProofResult::Undetermined);
    assert!(prove(&prover, "x <= 0-11") == ProofResult::False);
    assert!(prove(&prover, "x <= 0-12") == ProofResult::False);

    assert!(prove(&prover, "y+z <= 7") == ProofResult::True);
    assert!(prove(&prover, "y+z <= 8") == ProofResult::True);
    assert!(prove(&prover, "y+z <= 6") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+z <= 17") == ProofResult::True);
    assert!(prove(&prover, "x+y+z <= 18") == ProofResult::True);
    assert!(prove(&prover, "x+y+z <= 16") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+z <= 15") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+y+z <= x+14-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+y+z <= 10+14-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+y+z <= 24-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+y+z <= 25-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+2*y+z-y <= 24-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+y+z <= 23-z") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+y+z <= 23") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+y+z <= 24") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+z+y+y+z <= 23") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+z+y+y+z <= 24") == ProofResult::True);
    // Note that this is the only proof that requires O(n^4)
    assert!(prove(&prover, "x+y+y+z <= 25") == ProofResult::True);
}

#[test]
fn test_3_variables_2() {
    // These are our function requirements
    let cond0 = tokenize("0-10 <= x");
    let cond1 = tokenize("x <= 10");
    let cond2 = tokenize("0-6 <= y");
    let cond3 = tokenize("y <= 7-z");
    let cond4 = tokenize("0-1 <= z");
    let cond5 = tokenize("z <= 3");
    let cond6 = tokenize("z <= x");

    let cond0 = Condition::parse(&cond0).unwrap();
    let cond1 = Condition::parse(&cond1).unwrap();
    let cond2 = Condition::parse(&cond2).unwrap();
    let cond3 = Condition::parse(&cond3).unwrap();
    let cond4 = Condition::parse(&cond4).unwrap();
    let cond5 = Condition::parse(&cond5).unwrap();
    let cond6 = Condition::parse(&cond6).unwrap();

    let mut reqs = Vec::new();
    reqs.push(Requirement::from(&cond0));
    reqs.push(Requirement::from(&cond1));
    reqs.push(Requirement::from(&cond2));
    reqs.push(Requirement::from(&cond3));
    reqs.push(Requirement::from(&cond4));
    reqs.push(Requirement::from(&cond5));
    reqs.push(Requirement::from(&cond6));

    let mut bounds_prover = BoundsProver::new(reqs);
    bounds_prover.set_max_depth(4);
    let prover = FullProver::from(bounds_prover);

    assert!(prove(&prover, "x <= 11") == ProofResult::True);
    assert!(prove(&prover, "x <= 10") == ProofResult::True);
    assert!(prove(&prover, "x <= 9") == ProofResult::Undetermined);
    assert!(prove(&prover, "0-11 <= x") == ProofResult::True);
    assert!(prove(&prover, "0-10 <= x") == ProofResult::True);
    assert!(prove(&prover, "0-9 <= x") == ProofResult::True);
    assert!(prove(&prover, "0-1 <= x") == ProofResult::True);
    assert!(prove(&prover, "0 <= x") == ProofResult::Undetermined);
    assert!(prove(&prover, "11 <= x") == ProofResult::False);
    assert!(prove(&prover, "12 <= x") == ProofResult::False);
    assert!(prove(&prover, "x <= 0-10") == ProofResult::False);
    assert!(prove(&prover, "x <= 0-11") == ProofResult::False);
    assert!(prove(&prover, "x <= 0-12") == ProofResult::False);
    assert!(prove(&prover, "x <= 0-2") == ProofResult::False);
    assert!(prove(&prover, "x <= 0-1") == ProofResult::Undetermined);

    assert!(prove(&prover, "y+z <= 7") == ProofResult::True);
    assert!(prove(&prover, "y+z <= 8") == ProofResult::True);
    assert!(prove(&prover, "y+z <= 6") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+z <= 17") == ProofResult::True);
    assert!(prove(&prover, "x+y+z <= 18") == ProofResult::True);
    assert!(prove(&prover, "x+y+z <= 16") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+z <= 15") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+y+z <= x+14-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+y+z <= 10+14-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+y+z <= 24-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+y+z <= 25-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+2*y+z-y <= 24-z") == ProofResult::True);
    assert!(prove(&prover, "x+y+y+z <= 23-z") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+y+z <= 23") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+y+y+z <= 24") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+z+y+y+z <= 23") == ProofResult::Undetermined);
    assert!(prove(&prover, "x+z+y+y+z <= 24") == ProofResult::True);
    assert!(prove(&prover, "x+y+y+z <= 25") == ProofResult::True);
}

#[test]
fn test_lots_of_variables() {
    // These are our function requirements
    let cond0 = tokenize("2 <= x");
    let cond1 = tokenize("2*x <= n");
    let cond2 = tokenize("n <= y/3");
    let cond3 = tokenize("10*y+x <= z");
    let cond4 = tokenize("z <= 200");
    let cond5 = tokenize("z <= z*n");
    let cond6 = tokenize("x <= m");
    let cond7 = tokenize("m <= x+y+z+n");

    let cond0 = Condition::parse(&cond0).unwrap();
    let cond1 = Condition::parse(&cond1).unwrap();
    let cond2 = Condition::parse(&cond2).unwrap();
    let cond3 = Condition::parse(&cond3).unwrap();
    let cond4 = Condition::parse(&cond4).unwrap();
    let cond5 = Condition::parse(&cond5).unwrap();
    let cond6 = Condition::parse(&cond6).unwrap();
    let cond7 = Condition::parse(&cond7).unwrap();

    let mut reqs = Vec::new();
    reqs.push(Requirement::from(&cond0));
    reqs.push(Requirement::from(&cond1));
    reqs.push(Requirement::from(&cond2));
    reqs.push(Requirement::from(&cond3));
    reqs.push(Requirement::from(&cond4));
    reqs.push(Requirement::from(&cond5));
    reqs.push(Requirement::from(&cond6));
    reqs.push(Requirement::from(&cond7));

    let mut bounds_prover = BoundsProver::new(reqs.clone());
    bounds_prover.set_max_depth(5);
    let prover = FullProver::from(bounds_prover);

    let tokens = tokenize("y-2*n");
    let expr = crate::ast::proof::Expr::parse(&tokens).unwrap();

    /*
    let mini = super::optimiser::Minimizer::new(
        reqs.iter().map(|req| req.bounds()).flatten().collect(),
        super::expr::Expr::from(&expr).simplify(),
        5,
    );
    println!("{}", mini.enumerate().last().unwrap().0);
    */

    let mini = super::optimiser::Minimizer::new(
        reqs.iter()
            .map(|req| {
                req.simplify()
                    .bounds()
                    .iter()
                    .map(|(ident, bound)| (*ident, bound.simplify()))
                    .collect()
            })
            .collect(),
        super::expr::Expr::from(&expr).simplify(),
        6,
    );
    let mut bounds = mini.collect::<Vec<super::expr::Expr>>();
    //let mut bounds = mini.int_bounds().collect::<Vec<super::int::Int>>();
    bounds.dedup();
    for bound in bounds.iter() {
        println!(
            "YIELDS {} = {}",
            bound,
            match bound.eval() {
                Some(x) => x,
                None => super::int::EvalInt::from(super::int::Int::Infinity),
            }
        );
    }
    //panic!("Hi");

    assert!(prove(&prover, "0 <= n") == ProofResult::True);
    assert!(prove(&prover, "1 <= n") == ProofResult::True);
    assert!(prove(&prover, "4 <= n") == ProofResult::True);
    assert!(prove(&prover, "5 <= n") == ProofResult::Undetermined);
    assert!(prove(&prover, "n <= 5") == ProofResult::Undetermined);
    assert!(prove(&prover, "n <= 6") == ProofResult::True);
    assert!(prove(&prover, "n <= 7") == ProofResult::True);
    assert!(prove(&prover, "0 <= m") == ProofResult::True);
    assert!(prove(&prover, "0 <= x") == ProofResult::True);
    assert!(prove(&prover, "0 <= y") == ProofResult::True);
    assert!(prove(&prover, "z <= 200") == ProofResult::True);
    assert!(prove(&prover, "10*y+x <= z") == ProofResult::True);
    assert!(prove(&prover, "0 <= x") == ProofResult::True);
    assert!(prove(&prover, "10*y <= z") == ProofResult::True);
    assert!(prove(&prover, "10*y <= 200") == ProofResult::True);
    assert!(prove(&prover, "10*y <= 199") == ProofResult::True);
    assert!(prove(&prover, "10*y <= 198") == ProofResult::True);
    // TODO The next statement is true but quite hard to prove.
    // Maybe we can prove it?
    // assert!(prove(&prover, "10*y <= 197") == ProofResult::True);
    assert!(prove(&prover, "y <= 20") == ProofResult::True);
    assert!(prove(&prover, "y <= 19") == ProofResult::True);
    assert!(prove(&prover, "0 <= z") == ProofResult::True);
    // 3*(m-x-y-z) <= 3*n <= y
    // 3*(m-x-z) <= 4*y
    assert!(prove(&prover, "3*m-3*x-3*z <= 4*y") == ProofResult::True);
    assert!(prove(&prover, "3*m-3*x-3*z <= 5*y") == ProofResult::True);
    // x <= m
    assert!(prove(&prover, "3*x-3*x-3*z <= 4*y") == ProofResult::True);
    assert!(prove(&prover, "3*z >= 0-4*y") == ProofResult::True);
    assert!(prove(&prover, "0-4*y/3 <= z") == ProofResult::True);
    // But this is obvious anyway!
    assert!(prove(&prover, "0-y <= z") == ProofResult::True);

    assert!(prove(&prover, "y <= z") == ProofResult::True);
    assert!(prove(&prover, "10*y >= z") == ProofResult::False);
    // 3n <= y
    assert!(prove(&prover, "y >= z+1") == ProofResult::False);
    assert!(prove(&prover, "x <= z") == ProofResult::True);

    assert!(prove(&prover, "3*n <= y") == ProofResult::True);
    assert!(prove(&prover, "3*n <= y+x") == ProofResult::True);
    println!("pls pls");
    assert!(prove(&prover, "2*n <= y") == ProofResult::True);
    assert!(prove(&prover, "4*n <= y") == ProofResult::Undetermined);
}

macro_rules! requirements {
    (append($reqs:expr; $req:expr)) => {
        let tokens = tokenize($req);
        let cond = Condition::parse(&tokens).unwrap();
        $reqs.push(Requirement::from(&cond));
    };

    (append($reqs:expr; $head:expr,$($tail:expr),*)) => {
        requirements!(append($reqs; $head));
        requirements!(append($reqs; $($tail),+));
    };

    (let $name:ident = [$($strings:expr),+]) => {
        let mut $name = Vec::new();
        requirements!(append($name; $($strings),*));
        let $name = $name;
    };
}

macro_rules! prove {
    ($prover:ident: $stmt:expr => $expected:expr) => {
        let tokens = tokenize($stmt);
        let cond = Condition::parse(&tokens).unwrap();
        let req = Requirement::from(&cond);
        let result = $prover.prove(&req);
        if result != $expected {
            panic!("`{}` gave: {:?}, expected: {:?}", $stmt, result, $expected);
        }
    };
}

#[test]
fn new_tests<'a>() {
    requirements!(let reqs = [
        "x <= 2",
        "y >= 1",
        "z <= y",
        "l <= z",
        "a <= l",
        "b <= l",
        "c + d <= l",
        "f <= l/4",
        "g <= l/4",
        "y <= f + g + b/2",
        "a >= 0",
        "b >= 0",
        "c >= 0",
        "d >= 0",
        "f >= 0",
        "g >= 0",
        "l >= 0"
    ]);

    let mut bounds_prover = BoundsProver::new(reqs);
    bounds_prover.set_max_depth(8);
    let prover = FullProver::from(bounds_prover);

    prove!(prover: "x <= 5" => ProofResult::True);
    prove!(prover: "b <= l" => ProofResult::True);
    prove!(prover: "4*f <= l" => ProofResult::True);
    prove!(prover: "4*g <= l" => ProofResult::True);
    prove!(prover: "4*g + 4*f <= 2*l" => ProofResult::True);
    prove!(prover: "2*g + 2*f <= l" => ProofResult::True);
    prove!(prover: "g + f <= l/2" => ProofResult::True);
    prove!(prover: "g + f <= l/4" => ProofResult::Undetermined);
    prove!(prover: "g + f + b/2 <= l" => ProofResult::True);
    prove!(prover: "g + f + b <= l" => ProofResult::Undetermined);
}
