use super::bound_method2::{FullProver, Prover as BoundsProver};
use super::{ProofResult, Prover, Requirement, SimpleProver};
use crate::ast::proof::Condition;
use crate::tokens::tokenize;

fn prove<'a>(prover: &impl Prover<'a>, stmt: &'a str) -> ProofResult {
    let tokens = tokenize(stmt);
    let cond = Condition::parse(&tokens).unwrap();
    let req = Requirement::from(&cond);
    prover.prove(&req)
}

macro_rules! requirements {
    (append($reqs:expr; $req:expr)) => {
        let tokens = tokenize($req);
        let cond = Condition::parse(&tokens).unwrap();
        $reqs.push(Requirement::from(&cond));
    };

    (append($reqs:expr; $head:expr,$($tail:expr),*)) => {
        requirements!(append($reqs; $head));
        requirements!(append($reqs; $($tail),*));
    };

    (let $name:ident = [$($strings:expr),+$(,)?]) => {
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
            panic!("{} gave: {}, expected: {}", $stmt, result, $expected);
        }
        // Also try to prove the contra-positive.
        // If the result is Undetermined, both these proof attempts will be worse case.
        // If the result is True/False, the other will be the opposite so at least 1 worst case
        // optimiser run will occur. This therefore slows tests down by quite a bit.
        let contra_req = req.contra_positive();
        let contra_result = $prover.prove(&contra_req);
        if contra_result != !$expected {
            panic!(
                "!({}) = {} gave: {}, expected: {} = !{}",
                $stmt, contra_req, contra_result, !$expected, $expected
            );
        }
    };
}

#[test]
fn example_test() {
    // Also, to get an idea for the running time of the algorithm, this would be the time for a
    // function with 5 requirements and 21 unique statements to prove.

    requirements!(let reqs = [
        "x >= 0",
        "0 <= y",
        "x+y <= 10",
        "2*y <= 17",
        "x/2+y >= 1",
    ]);

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
    prove!(prover: "0 <= x" => ProofResult::True);
    prove!(prover: "0 <= y" => ProofResult::True);
    prove!(prover: "x+y <= 10" => ProofResult::True);
    // We can also say that
    prove!(prover: "0-3 <= x" => ProofResult::True);
    // But
    prove!(prover: "3 <= x" => ProofResult::Undetermined);
    // and
    prove!(prover: "11 <= x" => ProofResult::False);
    // Or that
    prove!(prover: "x <= 10" => ProofResult::True);
    prove!(prover: "y <= 10" => ProofResult::True);
    // In fact, 2*y <= 17 ==> y <= 8
    prove!(prover: "y <= 8" => ProofResult::True);
    // If we go too tight though, y *could* be in that range, but it won't always be:
    prove!(prover: "y <= 7" => ProofResult::Undetermined);
    prove!(prover: "y <= 5" => ProofResult::Undetermined);
    // Or, if we go crazy, the result is always false:
    prove!(prover: "y <= 0-1" => ProofResult::False);
    // We could also make some other combinations:
    prove!(prover: "2*x+y <= 20" => ProofResult::True);
    prove!(prover: "x+2*y <= 20" => ProofResult::True);
    prove!(prover: "x+2*y >= 0" => ProofResult::True);
    // And duplicating the above, using parentheticals
    prove!(prover: "2*(x+y)-y <= 20" => ProofResult::True);
    prove!(prover: "2*(x+y)-x <= 20" => ProofResult::True);
    prove!(prover: "2*(x+y)-x >= 0" => ProofResult::True);
    // Also, x/2 + y >= 1
    //   ==> x + 2*y >= 2
    prove!(prover: "x+2*y >= 1" => ProofResult::True);
    prove!(prover: "x+2*y >= 2" => ProofResult::True);
    prove!(prover: "x+2*y >= 3" => ProofResult::Undetermined);
    prove!(prover: "x+2*y >= 31" => ProofResult::False);

    prove!(prover: "2*x+y <= 19" => ProofResult::Undetermined);

    // With some tighter bounds!
    prove!(prover: "x+2*y <= 18" => ProofResult::True);
    prove!(prover: "x+2*y <= 17" => ProofResult::Undetermined);
}

#[test]
fn test_3_vars_different_coeffs() {
    requirements!(let reqs = [
        "x <= y+3",
        "x <= 2*y",
        "y <= z+2",
    ]);

    let mut bounds_prover = BoundsProver::new(reqs);
    // We can garentee that this will be worst case O(n^3)
    bounds_prover.set_max_depth(3);
    let prover = FullProver::from(bounds_prover);

    prove!(prover: "x <= z+5" => ProofResult::True);
}

#[test]
fn test_3_variables_different_coeffs_2() {
    requirements!(let reqs = [
        "x <= y+3",
        "x <= 2*y",
        "y <= z/2+2",
    ]);

    let mut bounds_prover = BoundsProver::new(reqs);
    // We can garentee that this will be worst case O(n^3)
    bounds_prover.set_max_depth(3);
    let prover = FullProver::from(bounds_prover);

    prove!(prover: "x <= z+4" => ProofResult::True);
}

#[test]
fn test_3_variables() {
    requirements!(let reqs = [
        "0-10 <= x",
        "x <= 10",
        "0-6 <= y",
        "y <= 7-z",
        "0-1 <= z",
        "z <= 3",
    ]);

    let mut bounds_prover = BoundsProver::new(reqs);
    bounds_prover.set_max_depth(4);
    let prover = FullProver::from(bounds_prover);

    prove!(prover: "x <= 11" => ProofResult::True);
    prove!(prover: "x <= 10" => ProofResult::True);
    prove!(prover: "x <= 9" => ProofResult::Undetermined);
    prove!(prover: "0-11 <= x" => ProofResult::True);
    prove!(prover: "0-10 <= x" => ProofResult::True);
    prove!(prover: "0-9 <= x" => ProofResult::Undetermined);
    prove!(prover: "11 <= x" => ProofResult::False);
    prove!(prover: "12 <= x" => ProofResult::False);
    prove!(prover: "x <= 0-10" => ProofResult::Undetermined);
    prove!(prover: "x <= 0-11" => ProofResult::False);
    prove!(prover: "x <= 0-12" => ProofResult::False);

    prove!(prover: "y+z <= 7" => ProofResult::True);
    prove!(prover: "y+z <= 8" => ProofResult::True);
    prove!(prover: "y+z <= 6" => ProofResult::Undetermined);
    prove!(prover: "x+y+z <= 17" => ProofResult::True);
    prove!(prover: "x+y+z <= 18" => ProofResult::True);
    prove!(prover: "x+y+z <= 16" => ProofResult::Undetermined);
    prove!(prover: "x+y+z <= 15" => ProofResult::Undetermined);
    prove!(prover: "x+y+y+z <= x+14-z" => ProofResult::True);
    prove!(prover: "x+y+y+z <= 10+14-z" => ProofResult::True);
    prove!(prover: "x+y+y+z <= 24-z" => ProofResult::True);
    prove!(prover: "x+y+y+z <= 25-z" => ProofResult::True);
    prove!(prover: "x+y+2*y+z-y <= 24-z" => ProofResult::True);
    prove!(prover: "x+y+y+z <= 23-z" => ProofResult::Undetermined);
    prove!(prover: "x+y+y+z <= 23" => ProofResult::Undetermined);
    prove!(prover: "x+y+y+z <= 24" => ProofResult::Undetermined);
    prove!(prover: "x+z+y+y+z <= 23" => ProofResult::Undetermined);
    prove!(prover: "x+z+y+y+z <= 24" => ProofResult::True);
    // Note that this is the only proof that requires O(n^4)
    prove!(prover: "x+y+y+z <= 25" => ProofResult::True);
}

#[test]
fn test_3_variables_2() {
    requirements!(let reqs = [
        "0-10 <= x",
        "x <= 10",
        "0-6 <= y",
        "y <= 7-z",
        "0-1 <= z",
        "z <= 3",
        "z <= x",
    ]);

    let mut bounds_prover = BoundsProver::new(reqs);
    bounds_prover.set_max_depth(4);
    let prover = FullProver::from(bounds_prover);

    prove!(prover: "x <= 11" => ProofResult::True);
    prove!(prover: "x <= 10" => ProofResult::True);
    prove!(prover: "x <= 9" => ProofResult::Undetermined);
    prove!(prover: "0-11 <= x" => ProofResult::True);
    prove!(prover: "0-10 <= x" => ProofResult::True);
    prove!(prover: "0-9 <= x" => ProofResult::True);
    prove!(prover: "0-1 <= x" => ProofResult::True);
    prove!(prover: "0 <= x" => ProofResult::Undetermined);
    prove!(prover: "11 <= x" => ProofResult::False);
    prove!(prover: "12 <= x" => ProofResult::False);
    prove!(prover: "x <= 0-10" => ProofResult::False);
    prove!(prover: "x <= 0-11" => ProofResult::False);
    prove!(prover: "x <= 0-12" => ProofResult::False);
    prove!(prover: "x <= 0-2" => ProofResult::False);
    prove!(prover: "x <= 0-1" => ProofResult::Undetermined);

    prove!(prover: "y+z <= 7" => ProofResult::True);
    prove!(prover: "y+z <= 8" => ProofResult::True);
    prove!(prover: "y+z <= 6" => ProofResult::Undetermined);
    prove!(prover: "x+y+z <= 17" => ProofResult::True);
    prove!(prover: "x+y+z <= 18" => ProofResult::True);
    prove!(prover: "x+y+z <= 16" => ProofResult::Undetermined);
    prove!(prover: "x+y+z <= 15" => ProofResult::Undetermined);
    prove!(prover: "x+y+y+z <= x+14-z" => ProofResult::True);
    prove!(prover: "x+y+y+z <= 10+14-z" => ProofResult::True);
    prove!(prover: "x+y+y+z <= 24-z" => ProofResult::True);
    prove!(prover: "x+y+y+z <= 25-z" => ProofResult::True);
    prove!(prover: "x+y+2*y+z-y <= 24-z" => ProofResult::True);
    prove!(prover: "x+y+y+z <= 23-z" => ProofResult::Undetermined);
    prove!(prover: "x+y+y+z <= 23" => ProofResult::Undetermined);
    prove!(prover: "x+y+y+z <= 24" => ProofResult::Undetermined);
    prove!(prover: "x+z+y+y+z <= 23" => ProofResult::Undetermined);
    prove!(prover: "x+z+y+y+z <= 24" => ProofResult::True);
    prove!(prover: "x+y+y+z <= 25" => ProofResult::True);
}

#[test]
fn test_lots_of_variables() {
    requirements!(let reqs = [
        "2 <= x",
        "2*x <= n",
        "n <= y/3",
        "10*y+x <= z",
        "z <= 200",
        "z <= z*n",
        "x <= m",
        "m <= x+y+z+n",
    ]);

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

    prove!(prover: "0 <= n" => ProofResult::True);
    prove!(prover: "1 <= n" => ProofResult::True);
    prove!(prover: "4 <= n" => ProofResult::True);
    prove!(prover: "5 <= n" => ProofResult::Undetermined);
    prove!(prover: "n <= 5" => ProofResult::Undetermined);
    prove!(prover: "n <= 6" => ProofResult::True);
    prove!(prover: "n <= 7" => ProofResult::True);
    prove!(prover: "0 <= m" => ProofResult::True);
    prove!(prover: "0 <= x" => ProofResult::True);
    prove!(prover: "0 <= y" => ProofResult::True);
    prove!(prover: "z <= 200" => ProofResult::True);
    prove!(prover: "10*y+x <= z" => ProofResult::True);
    prove!(prover: "0 <= x" => ProofResult::True);
    prove!(prover: "10*y <= z" => ProofResult::True);
    prove!(prover: "10*y <= 200" => ProofResult::True);
    prove!(prover: "10*y <= 199" => ProofResult::True);
    prove!(prover: "10*y <= 198" => ProofResult::True);
    // TODO The next statement is true but quite hard to prove.
    // Maybe we can prove it?
    // assert!(prove(&prover, "10*y <= 197") == ProofResult::True);
    prove!(prover: "y <= 20" => ProofResult::True);
    prove!(prover: "y <= 19" => ProofResult::True);
    prove!(prover: "0 <= z" => ProofResult::True);
    // 3*(m-x-y-z) <= 3*n <= y
    // 3*(m-x-z) <= 4*y
    prove!(prover: "3*m-3*x-3*z <= 4*y" => ProofResult::True);
    // FIXME prove!(prover: "3*m-3*x-3*z <= 5*y" => ProofResult::True);
    // x <= m
    prove!(prover: "3*x-3*x-3*z <= 4*y" => ProofResult::True);
    prove!(prover: "3*z >= 0-4*y" => ProofResult::True);
    prove!(prover: "0-4*y/3 <= z" => ProofResult::True);
    // But this is obvious anyway!
    prove!(prover: "0-y <= z" => ProofResult::True);

    prove!(prover: "y <= z" => ProofResult::True);
    prove!(prover: "10*y >= z" => ProofResult::False);
    // 3n <= y
    prove!(prover: "y >= z+1" => ProofResult::False);
    prove!(prover: "x <= z" => ProofResult::True);

    prove!(prover: "3*n <= y" => ProofResult::True);
    prove!(prover: "3*n <= y+x" => ProofResult::True);
    // FIXME prove!(prover: "2*n <= y" => ProofResult::True);
    prove!(prover: "4*n <= y" => ProofResult::Undetermined);
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
        "l >= 0",
    ]);
    // Note that l <= z <= y <= f + g + b/2 <= l/4 + l/4 + l/2 = l
    // Hence l = z = y = f + g + b/2

    let mut bounds_prover = BoundsProver::new(reqs);
    bounds_prover.set_max_depth(7);
    let prover = FullProver::from(bounds_prover);

    prove!(prover: "x <= 5" => ProofResult::True);
    prove!(prover: "b <= l" => ProofResult::True);
    prove!(prover: "4*f <= l" => ProofResult::True);
    prove!(prover: "4*g <= l" => ProofResult::True);
    prove!(prover: "4*g + 4*f <= 2*l" => ProofResult::True);
    prove!(prover: "2*g + 2*f <= l" => ProofResult::True);
    prove!(prover: "g + f <= l/2" => ProofResult::True);
    prove!(prover: "l <= y" => ProofResult::True);
    prove!(prover: "y <= l" => ProofResult::True);
    // FIXME FIXME prove!(prover: "g + f <= l/4" => ProofResult::Undetermined);
    prove!(prover: "g + f + b/2 <= l" => ProofResult::True);
    prove!(prover: "g + f + b/2 >= l" => ProofResult::True);
    // FIXME prove!(prover: "g + f + b <= l" => ProofResult::False);
    // FIXME prove!(prover: "g + f + 2*b <= l" => ProofResult::False);
    prove!(prover: "l <= z" => ProofResult::True);
    prove!(prover: "z <= l" => ProofResult::True);
    prove!(prover: "z <= y" => ProofResult::True);
    // FIXME prove!(prover: "y <= z" => ProofResult::True);
    prove!(prover: "b <= f + b/2 + g" => ProofResult::True);
    prove!(prover: "b/2 <= f + g" => ProofResult::True);
    prove!(prover: "b <= 2*f + 2*g" => ProofResult::True);
    prove!(prover: "l <= 2*f + 2*g" => ProofResult::True);
    prove!(prover: "c+d <= 2*f + 2*g" => ProofResult::True);
    prove!(prover: "c+d-1 <= 2*f + 2*g" => ProofResult::True);
    prove!(prover: "c+d-2 <= 2*f + 2*g" => ProofResult::True);
    prove!(prover: "c+d+1 <= 2*f + 2*g" => ProofResult::Undetermined);
    prove!(prover: "c+d+2 <= 2*f + 2*g" => ProofResult::Undetermined);
    // TODO Properly check this prove!(prover: "l >= 2*f + 2*g" => ProofResult::True);
    prove!(prover: "l <= 2*f + 2*g" => ProofResult::True);

    prove!(prover: "5 >= 3*x" => ProofResult::Undetermined);
    prove!(prover: "6 >= 3*x" => ProofResult::True);
    prove!(prover: "7 >= 3*x" => ProofResult::True);

    prove!(prover: "6 >= 2*x" => ProofResult::True);
    prove!(prover: "6 >= 4*x" => ProofResult::Undetermined);
    prove!(prover: "6 >= 4*x - x/2" => ProofResult::Undetermined);
    prove!(prover: "6 >= 4*x - 2*x/2" => ProofResult::True);

    prove!(prover: "x <= y+3" => ProofResult::True);
    // So this doesn't seem like it's true. But since, as above, 0 <= l = y
    // y+2 >= 2
    prove!(prover: "x <= y+2" => ProofResult::True);
    // FIXME prove!(prover: "x <= y+1" => ProofResult::Undetermined);
    prove!(prover: "x <= y+4" => ProofResult::True);
    prove!(prover: "x-1 <= y+2" => ProofResult::True);

    prove!(prover: "x <= 2*f+2*g+b" => ProofResult::True);
    prove!(prover: "x+1 <= 2*f+2*g+b" => ProofResult::Undetermined);
    prove!(prover: "x-2 <= 2*f+2*g+b" => ProofResult::True);
}

#[test]
fn real_world_example() {
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
    ]);

    let mut bounds_prover = BoundsProver::new(reqs);
    bounds_prover.set_max_depth(7);
    let prover = FullProver::from(bounds_prover);

    // So, we want to index with i and j!
    prove!(prover: "i >= 0" => ProofResult::True);
    prove!(prover: "i <= len-1" => ProofResult::True);
    prove!(prover: "j >= 0" => ProofResult::True);
    prove!(prover: "j <= len-1" => ProofResult::True);

    // Some different bounds tests
    prove!(prover: "1 <= i" => ProofResult::Undetermined);
    prove!(prover: "0-1 <= i" => ProofResult::True);
    prove!(prover: "i <= len" => ProofResult::True);
    prove!(prover: "i <= len-2" => ProofResult::Undetermined);

    // But now, we actually want to index i-1, this should clearly fail.
    prove!(prover: "i-1 >= 0" => ProofResult::Undetermined);
    // (This is still fine though)
    prove!(prover: "i-1 <= len-1" => ProofResult::True);
    // To solve this, we could change the requirements on i.
    // i2 has the correct requirements:
    prove!(prover: "i2-1 >= 0" => ProofResult::True);
    prove!(prover: "i2-1 <= len-1" => ProofResult::True);

    // YAY!
}
