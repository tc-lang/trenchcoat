use super::bound_method::{FullProver, Prover as BoundsProver};
use super::graph::Prover as GraphProver;
use super::{ProofResult, Prover, Requirement, SimpleProver};
use crate::ast::proof::Condition;
use crate::tokens::tokenize;

#[cfg(not(any(feature = "graph", feature = "bounds")))]
compile_error!("Either the 'graph' feature or the 'bounds' feature must be enabled");

#[cfg(all(feature = "graph", feature = "bounds"))]
compile_error!("Only one of the 'graph' feature or the 'bounds' feature can be enabled");

#[cfg(feature = "bounds")]
macro_rules! make_prover {
    ($name:ident, $reqs:ident, max_depth=$depth:expr) => {
        // Option A: Bounds method
        let mut bounds_prover = BoundsProver::new($reqs.clone());
        bounds_prover.set_max_depth($depth);
        $name = FullProver::from(bounds_prover);
    };
}

#[cfg(feature = "graph")]
macro_rules! make_prover {
    ($name:ident, $reqs:ident, max_depth=$depth:expr) => {
        // Option B: Graph method
        $name = GraphProver::new($reqs.clone())
    };
}

const ONLY_TEST: Option<ProofResult> = None;

macro_rules! requirements {
    (append($reqs:expr; $($strings:expr),*)) => {
        $(
            let tokens = tokenize($strings);
            let cond = Condition::parse(&tokens).unwrap();
            $reqs.push(Requirement::from(&cond));
        )*
    };

    (let $name:ident = [$($strings:expr),+$(,)?], $prover:ident) => {
        let mut $name = Vec::new();
        requirements!(append($name; $($strings),*));
        let $name = $name;

        // A 4-tuple of of: (is_contra, stmt, result, expected)
        let mut errors = <Vec<(bool, &'static str, ProofResult, ProofResult)>>::new();

        macro_rules! prove {
            ($stmt:expr => $expected:expr) => {
                let tokens = tokenize($stmt);
                let cond = Condition::parse(&tokens).unwrap();
                let req = Requirement::from(&cond);
                if ONLY_TEST.map(|r| r == $expected).unwrap_or(true) {
                    let result = $prover.prove(&req);
                    if result != $expected {
                        errors.push((false, $stmt, result, $expected));
                    }
                }
                // Also try to prove the contra-positive.
                // If the result is Undetermined, both these proof attempts will be worse case.
                // If the result is True/False, the other will be the opposite so at least 1 worst case
                // optimiser run will occur. This therefore slows tests down by quite a bit.
                if ONLY_TEST.map(|r| r == !$expected).unwrap_or(true) {
                    let contra_req = req.contra_positive();
                    let contra_result = $prover.prove(&contra_req);
                    if contra_result != !$expected {
                        errors.push((true, $stmt, contra_result, !$expected));
                    }
                }
            };
        }

        macro_rules! cleanup {
            () => {
                if !errors.is_empty() {
                    panic!("{}", errors.into_iter().fold(
                        "\n\n".to_string(),
                        |mut s, (is_contra, stmt, result, expected)| {
                            s + &(match is_contra {
                                false => format!("    {} \t gave: {}, expected: {}", stmt, result, expected),
                                true => format!("  ¬({})\t gave: {}, expected: {}", stmt, result, expected),
                            } + "\n")
                        },
                    ) + "\n");
                }
            }
        }
    };
}

#[test]
fn contra_positive_test() {
    let tokens = tokenize("a >= z");
    let cond = Condition::parse(&tokens).unwrap();
    let req = Requirement::from(&cond);
    //   ¬(a >= z)
    // ==> a < z
    // ==> a+1 <= z
    assert_eq!(
        format!("{}", req.contra_positive().simplify()),
        "a + 1 <= z"
    );

    let tokens = tokenize("a <= z");
    let cond = Condition::parse(&tokens).unwrap();
    let req = Requirement::from(&cond);
    //   ¬(a <= z)
    // ==> a > z
    // ==> a-1 >= z
    assert_eq!(
        format!("{}", req.contra_positive().simplify()),
        "-(1) + a >= z"
    );
}

#[test]
fn example_test() {
    // Also, to get an idea for the running time of the algorithm, this would be the time for a
    // function with 5 requirements and 21 unique statements to prove.

    let prover;

    requirements!(let reqs = [
        "x >= 0",
        "0 <= y",
        "x+y <= 10",
        "2*y <= 17",
        "x/2+y >= 1",
    ], prover);

    // We can garentee that this will be worst case O(n^4)
    make_prover!(prover, reqs, max_depth = 3);

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
    prove!("0 <= x" => ProofResult::True);
    prove!("0 <= y" => ProofResult::True);
    prove!("x+y <= 10" => ProofResult::True);
    // We can also say that
    prove!("0-3 <= x" => ProofResult::True);
    // But
    prove!("3 <= x" => ProofResult::Undetermined);
    // and
    prove!("11 <= x" => ProofResult::False);
    // Or that
    prove!("x <= 10" => ProofResult::True);
    prove!("y <= 10" => ProofResult::True);
    // In fact, 2*y <= 17 ==> y <= 8
    prove!("y <= 8" => ProofResult::True);
    // If we go too tight though, y *could* be in that range, but it won't always be:
    prove!("y <= 7" => ProofResult::Undetermined);
    prove!("y <= 5" => ProofResult::Undetermined);
    // Or, if we go crazy, the result is always false:
    prove!("y <= 0-1" => ProofResult::False);
    // We could also make some other combinations:
    prove!("2*x+y <= 20" => ProofResult::True);
    prove!("x+2*y <= 20" => ProofResult::True);
    prove!("x+2*y >= 0" => ProofResult::True);
    // And duplicating the above, using parentheticals
    prove!("2*(x+y)-y <= 20" => ProofResult::True);
    prove!("2*(x+y)-x <= 20" => ProofResult::True);
    prove!("2*(x+y)-x >= 0" => ProofResult::True);
    // Also, x/2 + y >= 1
    //   ==> x + 2*y >= 2
    prove!("x+2*y >= 1" => ProofResult::True);
    prove!("x+2*y >= 2" => ProofResult::True);
    prove!("x+2*y >= 3" => ProofResult::Undetermined);
    prove!("x+2*y >= 31" => ProofResult::False);

    prove!("2*x+y <= 19" => ProofResult::Undetermined);

    // With some tighter bounds!
    prove!("x+2*y <= 18" => ProofResult::True);
    prove!("x+2*y <= 17" => ProofResult::Undetermined);

    cleanup!()
}

#[test]
fn test_3_vars_different_coeffs() {
    let prover;

    requirements!(let reqs = [
        "x <= y+3",
        "x <= 2*y",
        "y <= z+2",
    ], prover);

    // We can garentee that this will be worst case O(n^3)
    make_prover!(prover, reqs, max_depth = 3);

    prove!("x <= z+5" => ProofResult::True);

    cleanup!()
}

#[test]
fn test_3_variables_different_coeffs_2() {
    let prover;

    requirements!(let reqs = [
        "x <= y+3",
        "x <= 2*y",
        "y <= z/2+2",
    ], prover);

    // We can garentee that this will be worst case O(n^3)
    make_prover!(prover, reqs, max_depth = 3);

    prove!("x <= z+4" => ProofResult::True);

    cleanup!()
}

#[test]
fn test_3_variables() {
    let prover;

    requirements!(let reqs = [
        "0-10 <= x",
        "x <= 10",
        "0-6 <= y",
        "y <= 7-z",
        "0-1 <= z",
        "z <= 3",
    ], prover);

    make_prover!(prover, reqs, max_depth = 4);

    prove!("x <= 11" => ProofResult::True);
    prove!("x <= 10" => ProofResult::True);
    prove!("x <= 9" => ProofResult::Undetermined);
    prove!("0-11 <= x" => ProofResult::True);
    prove!("0-10 <= x" => ProofResult::True);
    prove!("0-9 <= x" => ProofResult::Undetermined);
    prove!("11 <= x" => ProofResult::False);
    prove!("12 <= x" => ProofResult::False);
    prove!("x <= 0-10" => ProofResult::Undetermined);
    prove!("x <= 0-11" => ProofResult::False);
    prove!("x <= 0-12" => ProofResult::False);

    prove!("y+z <= 7" => ProofResult::True);
    prove!("y+z <= 8" => ProofResult::True);
    prove!("y+z <= 6" => ProofResult::Undetermined);
    prove!("x+y+z <= 17" => ProofResult::True);
    prove!("x+y+z <= 18" => ProofResult::True);
    prove!("x+y+z <= 16" => ProofResult::Undetermined);
    prove!("x+y+z <= 15" => ProofResult::Undetermined);
    prove!("x+y+y+z <= x+14-z" => ProofResult::True);
    prove!("x+y+y+z <= 10+14-z" => ProofResult::True);
    prove!("x+y+y+z <= 24-z" => ProofResult::True);
    prove!("x+y+y+z <= 25-z" => ProofResult::True);
    prove!("x+y+2*y+z-y <= 24-z" => ProofResult::True);
    prove!("x+y+y+z <= 23-z" => ProofResult::Undetermined);
    prove!("x+y+y+z <= 23" => ProofResult::Undetermined);
    prove!("x+y+y+z <= 24" => ProofResult::Undetermined);
    prove!("x+z+y+y+z <= 23" => ProofResult::Undetermined);
    prove!("x+z+y+y+z <= 24" => ProofResult::True);
    // Note that this is the only proof that requires O(n^4)
    prove!("x+y+y+z <= 25" => ProofResult::True);

    cleanup!()
}

#[test]
fn test_3_variables_2() {
    let prover;

    requirements!(let reqs = [
        "0-10 <= x",
        "x <= 10",
        "0-6 <= y",
        "y <= 7-z",
        "0-1 <= z",
        "z <= 3",
        "z <= x",
    ], prover);

    make_prover!(prover, reqs, max_depth = 4);

    prove!("x <= 11" => ProofResult::True);
    prove!("x <= 10" => ProofResult::True);
    prove!("x <= 9" => ProofResult::Undetermined);
    prove!("0-11 <= x" => ProofResult::True);
    prove!("0-10 <= x" => ProofResult::True);
    prove!("0-9 <= x" => ProofResult::True);
    prove!("0-1 <= x" => ProofResult::True);
    prove!("0 <= x" => ProofResult::Undetermined);
    prove!("11 <= x" => ProofResult::False);
    prove!("12 <= x" => ProofResult::False);
    prove!("x <= 0-10" => ProofResult::False);
    prove!("x <= 0-11" => ProofResult::False);
    prove!("x <= 0-12" => ProofResult::False);
    prove!("x <= 0-2" => ProofResult::False);
    prove!("x <= 0-1" => ProofResult::Undetermined);

    prove!("y+z <= 7" => ProofResult::True);
    prove!("y+z <= 8" => ProofResult::True);
    prove!("y+z <= 6" => ProofResult::Undetermined);
    prove!("x+y+z <= 17" => ProofResult::True);
    prove!("x+y+z <= 18" => ProofResult::True);
    prove!("x+y+z <= 16" => ProofResult::Undetermined);
    prove!("x+y+z <= 15" => ProofResult::Undetermined);
    prove!("x+y+y+z <= x+14-z" => ProofResult::True);
    prove!("x+y+y+z <= 10+14-z" => ProofResult::True);
    prove!("x+y+y+z <= 24-z" => ProofResult::True);
    prove!("x+y+y+z <= 25-z" => ProofResult::True);
    prove!("x+y+2*y+z-y <= 24-z" => ProofResult::True);
    prove!("x+y+y+z <= 23-z" => ProofResult::Undetermined);
    prove!("x+y+y+z <= 23" => ProofResult::Undetermined);
    prove!("x+y+y+z <= 24" => ProofResult::Undetermined);
    prove!("x+z+y+y+z <= 23" => ProofResult::Undetermined);
    prove!("x+z+y+y+z <= 24" => ProofResult::True);
    prove!("x+y+y+z <= 25" => ProofResult::True);

    cleanup!()
}

#[test]
fn test_lots_of_variables() {
    let prover;

    requirements!(let reqs = [
        "2 <= x",
        "2*x <= n",
        "n <= y/3",
        "10*y+x <= z",
        "z <= 200",

        // FIXME Due to the changes in how signs are handled during rearrangement, the following
        // requirement can not longer be handled by the bounds method.
        // The 2 below it make the tests valid however this should be re-introduced when signs can
        // be properly handled.
        //"z <= z*n",
        "1 <= n",
        "0 <= z",

        "x <= m",
        "m <= x+y+z+n",

        // TODO Do we need this?
        "y >= 0",
    ], prover);

    make_prover!(prover, reqs, max_depth = 5);

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

    /*
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
    */
    //panic!("Hi");

    prove!("0 <= n" => ProofResult::True);
    prove!("1 <= n" => ProofResult::True);
    prove!("4 <= n" => ProofResult::True);
    prove!("5 <= n" => ProofResult::Undetermined);
    prove!("n <= 5" => ProofResult::Undetermined);
    prove!("n <= 6" => ProofResult::True);
    prove!("n <= 7" => ProofResult::True);
    prove!("0 <= m" => ProofResult::True);
    prove!("0 <= x" => ProofResult::True);
    prove!("0 <= y" => ProofResult::True);
    prove!("z <= 200" => ProofResult::True);
    prove!("10*y+x <= z" => ProofResult::True);
    prove!("0 <= x" => ProofResult::True);
    prove!("10*y <= z" => ProofResult::True);
    prove!("10*y <= 200" => ProofResult::True);
    prove!("10*y <= 199" => ProofResult::True);
    prove!("10*y <= 198" => ProofResult::True);
    // TODO The next statement is true but quite hard to prove.
    // Maybe we can prove it?
    prove!("10*y <= 197" => ProofResult::True);
    prove!("y <= 20" => ProofResult::True);
    prove!("y <= 19" => ProofResult::True);
    prove!("0 <= z" => ProofResult::True);
    // 3*(m-x-y-z) <= 3*n <= y
    // 3*(m-x-z) <= 4*y
    prove!("3*m-3*x-3*z <= 4*y" => ProofResult::True);
    prove!("3*m-3*x-3*z <= 5*y" => ProofResult::True);
    // x <= m
    prove!("3*x-3*x-3*z <= 4*y" => ProofResult::True);
    prove!("3*z >= 0-4*y" => ProofResult::True);
    prove!("0-4*y/3 <= z" => ProofResult::True);
    // But this is obvious anyway!
    prove!("0-y <= z" => ProofResult::True);

    prove!("y <= z" => ProofResult::True);
    prove!("10*y >= z" => ProofResult::False);
    // 3n <= y
    prove!("y >= z+1" => ProofResult::False);
    prove!("x <= z" => ProofResult::True);

    prove!("3*n <= y" => ProofResult::True);
    prove!("3*n <= y+x" => ProofResult::True);
    prove!("2*n <= y" => ProofResult::True);
    prove!("4*n <= y" => ProofResult::Undetermined);

    cleanup!()
}

#[test]
fn new_tests<'a>() {
    let prover;

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
        "l >= 0",
    ], prover);

    make_prover!(prover, reqs, max_depth = 7);
    // Note that l <= z <= y <= f + g + b/2 <= l/4 + l/4 + l/2 = l
    // Hence l = z = y = f + g + b/2

    prove!("x <= 5" => ProofResult::True);
    prove!("b <= l" => ProofResult::True);
    prove!("4*f <= l" => ProofResult::True);
    prove!("4*g <= l" => ProofResult::True);
    prove!("4*g + 4*f <= 2*l" => ProofResult::True);
    prove!("2*g + 2*f <= l" => ProofResult::True);
    prove!("g + f <= l/2" => ProofResult::True);
    prove!("l <= y" => ProofResult::True);
    prove!("y <= l" => ProofResult::True);
    // FIXME FIXME prove!("g + f <= l/4" => ProofResult::Undetermined);
    prove!("g + f + b/2 <= l" => ProofResult::True);
    prove!("g + f + b/2 >= l" => ProofResult::True);
    // FIXME prove!("g + f + b <= l" => ProofResult::False);
    // FIXME prove!("g + f + 2*b <= l" => ProofResult::False);
    prove!("l <= z" => ProofResult::True);
    prove!("z <= l" => ProofResult::True);
    prove!("z <= y" => ProofResult::True);
    // FIXME prove!("y <= z" => ProofResult::True);
    prove!("b <= f + b/2 + g" => ProofResult::True);
    prove!("b/2 <= f + g" => ProofResult::True);
    prove!("b <= 2*f + 2*g" => ProofResult::True);
    prove!("l <= 2*f + 2*g" => ProofResult::True);
    prove!("c+d <= 2*f + 2*g" => ProofResult::True);
    prove!("c+d-1 <= 2*f + 2*g" => ProofResult::True);
    prove!("c+d-2 <= 2*f + 2*g" => ProofResult::True);
    prove!("c+d+1 <= 2*f + 2*g" => ProofResult::Undetermined);
    prove!("c+d+2 <= 2*f + 2*g" => ProofResult::Undetermined);
    // TODO Properly check this prove!("l >= 2*f + 2*g" => ProofResult::True);
    prove!("l <= 2*f + 2*g" => ProofResult::True);

    prove!("5 >= 3*x" => ProofResult::Undetermined);
    prove!("6 >= 3*x" => ProofResult::True);
    prove!("7 >= 3*x" => ProofResult::True);

    prove!("6 >= 2*x" => ProofResult::True);
    prove!("6 >= 4*x" => ProofResult::Undetermined);
    prove!("6 >= 4*x - x/2" => ProofResult::Undetermined);
    prove!("6 >= 4*x - 2*x/2" => ProofResult::True);

    prove!("x <= y+3" => ProofResult::True);
    prove!("x <= y+2" => ProofResult::True);
    prove!("x <= y+1" => ProofResult::True);
    prove!("x <= y" => ProofResult::Undetermined);
    prove!("x <= y+4" => ProofResult::True);
    prove!("x-1 <= y+2" => ProofResult::True);

    prove!("x <= 2*f+2*g+b" => ProofResult::True);
    prove!("x+1 <= 2*f+2*g+b" => ProofResult::Undetermined);
    prove!("x-2 <= 2*f+2*g+b" => ProofResult::True);

    cleanup!()
}

#[test]
fn real_world_example() {
    let prover;

    requirements!(let reqs = [
        // So we're taking an array with a non-negative length
        "0 <= len",
        // We then take start and end values, which are in bounds.
        "0 <= start",
        "start <= len-1",
        "0 <= end",
        "end <= len-1",

        // Later on, we want to do something regarding pairs of indexs.
        // For example, adding arr[i] and arr[j] with i and j starting from opposite ends.
        // Or, in the context of this system, simplifying expression terms with other expression
        // terms!
        //
        // For this, we have 2 loop variables within the range specified by start and end.
        "start <= i",
        "i <= end",
        "start <= j",
        "j <= end",

        // This will be used later.
        "start <= i2-1",
        "i2-1 <= end",
    ], prover);

    make_prover!(prover, reqs, max_depth = 3);

    // So, we want to index with i and j!
    prove!("i >= 0" => ProofResult::True);
    prove!("i <= len-1" => ProofResult::True);
    prove!("j >= 0" => ProofResult::True);
    prove!("j <= len-1" => ProofResult::True);

    // Some different bounds tests
    prove!("1 <= i" => ProofResult::Undetermined);
    prove!("0-1 <= i" => ProofResult::True);
    prove!("i <= len" => ProofResult::True);
    prove!("i <= len-2" => ProofResult::Undetermined);

    // But now, we actually want to index i-1, this should clearly fail.
    prove!("i-1 >= 0" => ProofResult::Undetermined);
    // (This is still fine though)
    prove!("i-1 <= len-1" => ProofResult::True);
    // To solve this, we could change the requirements on i.
    // i2 has the correct requirements:
    prove!("i2-1 >= 0" => ProofResult::True);
    prove!("i2-1 <= len-1" => ProofResult::True);

    // YAY!

    cleanup!()
}

#[test]
fn really_long_chain() {
    let prover;

    requirements!(let reqs = [
        "a <= b",
        "b <= c",
        "c <= d",
        "d <= e",
        "e <= f",
        "f <= g",
        "g <= h",
        "h <= i",
        "i <= j",
        "j <= k",
        "k <= l",
        "l <= m",
        "m <= n",
        "n <= o",
        "o <= p",
        "p <= q",
        "q <= r",
        "r <= s",
        "s <= t",
        "t <= u",
        "u <= v",
        "v <= w",
        "w <= x",
        "x <= y",
        "y <= z",
    ], prover);

    make_prover!(prover, reqs, max_depth = 26);

    prove!("a <= z" => ProofResult::True);
    prove!("a+1 <= z" => ProofResult::Undetermined);
    prove!("a+1 >= z" => ProofResult::Undetermined);
    prove!("a+1 <= z+1" => ProofResult::True);
    prove!("a+1 >= z+1" => ProofResult::Undetermined);
    prove!("a <= 2*z" => ProofResult::Undetermined);
    prove!("a*2 <= 2*z" => ProofResult::True);
    prove!("a*2 >= 2*z" => ProofResult::Undetermined);
    prove!("a >= z" => ProofResult::Undetermined);
    prove!("0-a >= 0-z" => ProofResult::True);
    prove!("0-a <= 0-z" => ProofResult::Undetermined);

    prove!("d <= f" => ProofResult::True);
    prove!("d >= f" => ProofResult::Undetermined);

    cleanup!()
}

#[test]
fn really_long_cycle() {
    let prover;

    requirements!(let reqs = [
        "a <= b",
        "b <= c",
        "c <= d",
        "d <= e",
        "e <= f",
        "f <= g",
        "g <= h",
        "h <= i",
        "i <= j",
        "j <= k",
        "k <= l",
        "l <= m",
        "m <= n",
        "n <= o",
        "o <= p",
        "p <= q",
        "q <= r",
        "r <= s",
        "s <= t",
        "t <= u",
        "u <= v",
        "v <= w",
        "w <= x",
        "x <= y",
        "y <= z",
        "z <= a",
    ], prover);

    make_prover!(prover, reqs, max_depth = 30);

    prove!("a <= z" => ProofResult::True);
    prove!("z <= a" => ProofResult::True);
    prove!("a+1 <= z" => ProofResult::False);
    prove!("a+1 >= z" => ProofResult::True);
    prove!("a+1 <= z+1" => ProofResult::True);
    prove!("a+1 >= z+1" => ProofResult::True);
    prove!("a <= 2*z" => ProofResult::Undetermined);
    prove!("a*2 <= 2*z" => ProofResult::True);
    prove!("a*2 >= 2*z" => ProofResult::True);
    prove!("a >= z" => ProofResult::True);
    prove!("0-a >= 0-z" => ProofResult::True);
    prove!("0-a <= 0-z" => ProofResult::True);

    prove!("d <= f" => ProofResult::True);
    prove!("d >= f" => ProofResult::True);

    cleanup!()
}

#[test]
fn linked_cycles() {
    let prover;

    requirements!(let reqs = [
        "a <= b",
        "b <= c",
        "c <= d",
        "d <= e",
        "e <= f",
        "f <= g",
        "g <= h",
        "h <= i",
        "i <= j",
        "j <= k",
        "k <= l",
        "k <= a",
        "l <= m",
        "m <= n",
        "n <= o",
        "o <= p",
        "p <= q",
        "q <= r",
        "r <= s",
        "s <= t",
        "t <= u",
        "u <= v",
        "v <= w",
        "w <= x",
        "x <= y",
        "y <= z",
        "z <= p",
        // a = b = ... = k <= l <= m <= n <= o <= p = q = ... = z
    ], prover);

    make_prover!(prover, reqs, max_depth = 26);

    prove!("a <= z" => ProofResult::True);
    prove!("z <= a" => ProofResult::Undetermined);

    prove!("a <= k" => ProofResult::True);
    prove!("k <= a" => ProofResult::True);
    prove!("b <= k" => ProofResult::True);
    prove!("k <= b" => ProofResult::True);
    prove!("a <= j" => ProofResult::True);
    prove!("j <= a" => ProofResult::True);
    prove!("b <= j" => ProofResult::True);
    prove!("j <= b" => ProofResult::True);

    prove!("a <= l" => ProofResult::True);
    prove!("l <= a" => ProofResult::Undetermined);

    prove!("p <= z" => ProofResult::True);
    prove!("z <= p" => ProofResult::True);
    prove!("q <= z" => ProofResult::True);
    prove!("z <= q" => ProofResult::True);
    prove!("p <= x" => ProofResult::True);
    prove!("x <= p" => ProofResult::True);
    prove!("q <= y" => ProofResult::True);
    prove!("y <= q" => ProofResult::True);

    prove!("o <= z" => ProofResult::True);
    prove!("z <= o" => ProofResult::Undetermined);
    prove!("b <= z" => ProofResult::True);
    prove!("z <= b" => ProofResult::Undetermined);

    cleanup!()
}

#[test]
fn linked_cycles_2() {
    let prover;

    requirements!(let reqs = [
        "a <= b",
        "b <= c",
        "c <= d",
        "d <= e",
        "e <= f",
        "f <= g",
        "g <= h",
        "h <= i",
        "i <= j",
        "j <= k",
        "k <= l",
        "k <= a",
        "l <= m",
        "m <= n",
        "n <= o",
        "o <= p",
        "p <= q",
        "q <= r",
        "r <= s",
        "s <= t",
        "t <= u",
        "u <= v",
        "v <= w",
        "w <= x",
        "x <= y",
        "y <= z",
        "z <= p",
        // a = b = ... = k <= l <= m <= n <= o <= p = q = ... = z

        "m <= a",
        // a = b = .. = m <= n <= o <= p = q = .. z
    ], prover);

    make_prover!(prover, reqs, max_depth = 26);

    prove!("a <= z" => ProofResult::True);
    prove!("z <= a" => ProofResult::Undetermined);

    prove!("a <= k" => ProofResult::True);
    prove!("k <= a" => ProofResult::True);
    prove!("b <= k" => ProofResult::True);
    prove!("k <= b" => ProofResult::True);
    prove!("a <= j" => ProofResult::True);
    prove!("j <= a" => ProofResult::True);
    prove!("b <= j" => ProofResult::True);
    prove!("j <= b" => ProofResult::True);

    prove!("a <= l" => ProofResult::True);
    prove!("l <= a" => ProofResult::True);
    prove!("a <= m" => ProofResult::True);
    prove!("m <= a" => ProofResult::True);
    prove!("a <= n" => ProofResult::True);
    prove!("n <= a" => ProofResult::Undetermined);

    prove!("p <= z" => ProofResult::True);
    prove!("z <= p" => ProofResult::True);
    prove!("q <= z" => ProofResult::True);
    prove!("z <= q" => ProofResult::True);
    prove!("p <= x" => ProofResult::True);
    prove!("x <= p" => ProofResult::True);
    prove!("q <= y" => ProofResult::True);
    prove!("y <= q" => ProofResult::True);

    prove!("o <= z" => ProofResult::True);
    prove!("z <= o" => ProofResult::Undetermined);
    prove!("m <= z" => ProofResult::True);
    prove!("z <= m" => ProofResult::Undetermined);
    prove!("b <= z" => ProofResult::True);
    prove!("z <= b" => ProofResult::Undetermined);

    cleanup!()
}

#[test]
fn linked_cycles_3() {
    let prover;

    requirements!(let reqs = [
        "a <= b",
        "b <= c",
        "c <= d",
        "d <= e",
        "e <= f",
        "f <= g",
        "g <= h",
        "h <= i",
        "i <= j",
        "j <= k",
        "k <= l",
        "k <= a",
        "l <= m",
        "m <= n",
        "n <= o",
        "o <= p",
        "p <= q",
        "q <= r",
        "r <= s",
        "s <= t",
        "t <= u",
        "u <= v",
        "v <= w",
        "w <= x",
        "x <= y",
        "y <= z",
        "z <= p",
        // a = b = ... = k <= l <= m <= n <= o <= p = q = ... = z

        "p <= a",
        // a = b = .. z
    ], prover);

    make_prover!(prover, reqs, max_depth = 26);

    prove!("a <= z" => ProofResult::True);
    prove!("z <= a" => ProofResult::True);
    prove!("a+1 <= z" => ProofResult::False);
    prove!("a+1 >= z" => ProofResult::True);
    prove!("a+1 <= z+1" => ProofResult::True);
    prove!("a+1 >= z+1" => ProofResult::True);
    prove!("a <= 2*z" => ProofResult::Undetermined);
    prove!("a*2 <= 2*z" => ProofResult::True);
    prove!("a*2 >= 2*z" => ProofResult::True);
    prove!("a >= z" => ProofResult::True);
    prove!("0-a >= 0-z" => ProofResult::True);
    prove!("0-a <= 0-z" => ProofResult::True);

    prove!("d <= f" => ProofResult::True);
    prove!("d >= f" => ProofResult::True);

    cleanup!()
}

#[test]
fn sub_carry() {
    let prover;
    requirements!(let reqs = [
        "a <= b",
        "0-a <= c",
        "d >= 0",
    ], prover);

    make_prover!(prover, reqs, max_depth = 4);

    prove!("0 <= a+c" => ProofResult::True);
    prove!("0 <= a+b" => ProofResult::Undetermined);
    prove!("0 <= a-b" => ProofResult::Undetermined);
    prove!("0 >= a-b" => ProofResult::True);
    prove!("0 <= b+c" => ProofResult::True);

    // Let's do some trivial cases!
    prove!("0 <= 0" => ProofResult::True);
    prove!("a <= a" => ProofResult::True);
    prove!("a <= a+1" => ProofResult::True);
    prove!("a+1 <= a+1" => ProofResult::True);
    prove!("a+2 <= a+1" => ProofResult::False);
    prove!("a+2 <= a+2" => ProofResult::True);
    prove!("a+0 <= a+2" => ProofResult::True);
    prove!("b <= b+1" => ProofResult::True);
    prove!("b+1 <= b+1" => ProofResult::True);
    prove!("b+2 <= b+1" => ProofResult::False);
    prove!("b+2 <= b+2" => ProofResult::True);
    prove!("b+0 <= b+2" => ProofResult::True);
    prove!("c <= c+1" => ProofResult::True);
    prove!("c+1 <= c+1" => ProofResult::True);
    prove!("c+2 <= c+1" => ProofResult::False);
    prove!("c+2 <= c+2" => ProofResult::True);
    prove!("c+0 <= c+2" => ProofResult::True);

    prove!("a <= 2*a" => ProofResult::Undetermined);
    prove!("d <= 2*d" => ProofResult::True);
    prove!("a <= a+b" => ProofResult::Undetermined);
    prove!("a <= a+d" => ProofResult::True);
    prove!("a <= a+a+c" => ProofResult::True);
    prove!("a <= 2*a+c" => ProofResult::True);
    prove!("0-d <= 0" => ProofResult::True);
    prove!("0-d <= 1" => ProofResult::True);

    // Tiny bit harder
    prove!("0-d <= a+c" => ProofResult::True);
    prove!("0-d <= b+c" => ProofResult::True);
    prove!("0-d <= a+b" => ProofResult::Undetermined);
    prove!("0 <= a + b + 2*c" => ProofResult::True);
    prove!("0-d <= a + b + 2*c" => ProofResult::True);
    prove!("0-c <= a+b+c+d" => ProofResult::True);
    prove!("0 <= a+b+c+d" => ProofResult::Undetermined);

    cleanup!()
}
