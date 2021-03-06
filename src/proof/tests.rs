use super::graph::Prover as GraphProver;
use super::{ProofResult, Prover, Requirement, SimpleProver};
use crate::ast::proof::Condition;
use crate::tokens::tokenize;

#[cfg(not(any(feature = "graph", feature = "bounds", feature = "dummy-prover")))]
compile_error!("Either the 'graph' feature, the 'bounds' feature or the 'dummy-prover' feature must be enabled");

#[cfg(all(feature = "graph", feature = "bounds"))]
compile_error!("Only one of the 'graph' feature or the 'bounds' feature can be enabled");
#[cfg(all(feature = "graph", feature = "dummy-prover"))]
compile_error!("Only one of the 'graph' feature or the 'dummy-prover' feature can be enabled");
#[cfg(all(feature = "dummy-prover", feature = "bounds"))]
compile_error!("Only one of the 'bounds' feature or the 'dummy-prover' feature can be enabled");

#[cfg(feature = "bounds")]
macro_rules! make_prover {
    ($name:ident, $reqs:ident, max_depth=$depth:expr) => {
        // Option A: Bounds method
        $name = super::bound_method::DefaultSimpleProver::new(&$reqs);
        //$name = FullProver::from(bounds_prover);
    };
}

#[cfg(feature = "graph")]
macro_rules! make_prover {
    ($name:ident, $reqs:ident, max_depth=$depth:expr) => {
        // Option B: Graph method
        $name = super::graph::Prover::new(&$reqs)
    };
}

#[cfg(any(
    not(any(feature = "bounds", feature = "graph")),
    all(feature = "bounds", feature = "graph")
))]
macro_rules! make_prover {
    ($name:ident, $reqs:ident, max_depth=$depth:expr) => {
        // A dummy macro so that we only get one error if the features are wrong
        // This will also be used when the dummy-prover feature is passed
        $name = super::dummy::Prover::new(&$reqs)
    };
}

const ONLY_TEST: Option<ProofResult> = None;

macro_rules! requirements {
    (append($reqs:expr; $($strings:expr),*)) => {
        $(
            let tokens = tokenize($strings);
            let cond = Condition::parse(&tokens).unwrap();
            let reqs: Vec<Requirement> = (&cond).into();
            $reqs.extend(reqs);
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
                let reqs: Vec<Requirement> = (&cond).into();
                for req in reqs {
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
                }
            };
        }

        macro_rules! cleanup {
            () => {
                if !errors.is_empty() {
                    panic!("\n\n{}\n", errors.into_iter().fold(
                        String::new(),
                        |s, (is_contra, stmt, result, expected)| {
                            s + &(match is_contra {
                                false => format!("    {} \t gave: {}, expected: {}", stmt, result, expected),
                                true  => format!("  ¬({})\t gave: {}, expected: {}", stmt, result, expected),
                            } + "\n")
                        },
                    ));
                }
            }
        }
    };
}

fn budget(n: usize) -> usize {
    //(2*n).min(n+16)//.min(n/8+32)
    //8*(0_usize.leading_zeros()-(n+1).leading_zeros()) as usize + (n/8).min(16)
    //(0_usize.leading_zeros()-(n+1).saturating_pow(8).leading_zeros()) as usize + (n/8).min(16)
    //(0_usize.leading_zeros()-(n+1).saturating_pow(4).leading_zeros()) as usize + n
    2 * n
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
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    let tokens = tokenize("y-2*n");
    let expr = crate::ast::proof::Expr::parse(&tokens).unwrap();

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
    // z <= y <= f + g + b/2 <= l
    //
    // 1) z <= y
    // 2) y <= f + g + b/2
    // 3) f <= l/4
    // 4) g <= l/4
    // 5) b <= l

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));
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
    prove!("g + f <= l/4" => ProofResult::Undetermined);
    prove!("g + f + b/2 <= l" => ProofResult::True);
    prove!("g + f + b/2 >= l" => ProofResult::True);
    // FIXME prove!("g + f + b <= l" => ProofResult::False);
    // FIXME prove!("g + f + 2*b <= l" => ProofResult::False);
    prove!("l <= z" => ProofResult::True);
    prove!("z <= l" => ProofResult::True);
    prove!("z <= y" => ProofResult::True);
    prove!("y <= z" => ProofResult::True);
    prove!("b <= f + b/2 + g" => ProofResult::True);
    prove!("b/2 <= f + g" => ProofResult::True);
    prove!("b <= 2*f + 2*g" => ProofResult::True);
    prove!("l <= 2*f + 2*g" => ProofResult::True);
    prove!("c+d <= 2*f + 2*g" => ProofResult::True);
    prove!("c+d-1 <= 2*f + 2*g" => ProofResult::True);
    prove!("c+d-2 <= 2*f + 2*g" => ProofResult::True);
    prove!("c+d+1 <= 2*f + 2*g" => ProofResult::Undetermined);
    prove!("c+d+2 <= 2*f + 2*g" => ProofResult::Undetermined);
    prove!("l >= 2*f + 2*g" => ProofResult::True);
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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

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

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    prove!("0 <= a+c" => ProofResult::True);
    prove!("0 <= a+b" => ProofResult::Undetermined);
    prove!("0 <= a-b" => ProofResult::Undetermined);
    prove!("0 >= a-b" => ProofResult::True);
    prove!("0 <= b+c" => ProofResult::True);

    // Let's do some trivial cases!
    prove!("0 <= 0" => ProofResult::True);
    prove!("0 <= 1" => ProofResult::True);
    prove!("0-3 <= 7" => ProofResult::True);
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

#[test]
fn large_tree() {
    let prover;

    requirements!(let reqs = [
        "a <= b",
        "a <= c",
        "a <= d",
        "b <= e",
        "b <= f",
        "b <= g",
        "c <= h",
        "c <= i",
        "c <= j",
        "d <= k",
        "d <= l",
        "d <= m",
        "e <= n",
        "e <= o",
        "e <= p",
        "f <= q",
        "f <= r",
        "f <= s",
        "g <= t",
        "g <= u",
        "g <= v",
        "h <= w",
        "h <= x",
        "h <= y",
        "i <= z",
        "i <= aa",
        "i <= ab",
        "j <= ac",
        "j <= ad",
        "j <= ae",
        "k <= af",
        "k <= ag",
        "k <= ah",
        "l <= ai",
        "l <= aj",
        "l <= ak",
        "m <= al",
        "m <= am",
        "m <= an",
    ], prover);

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    prove!("a <= n" => ProofResult::True);
    prove!("a <= an" => ProofResult::True);

    cleanup!()
}

#[test]
fn dont_get_greedy() {
    let prover;

    requirements!(let reqs = [
        "0 <= a",
        "a <= b",
        "c <= b",
    ], prover);

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    prove!("a-c+b >= 0" => ProofResult::True);
    prove!("a-c+b+1 >= 0" => ProofResult::True);
    prove!("a-c+b-1 >= 0" => ProofResult::Undetermined);

    cleanup!()
}

#[test]
fn dont_get_greedy2() {
    let prover;

    requirements!(let reqs = [
        "0 <= c",
        "c <= b",
        "a <= b",
    ], prover);

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    prove!("c-a+b >= 0" => ProofResult::True);
    prove!("c-a+b+1 >= 0" => ProofResult::True);
    prove!("c-a+b-1 >= 0" => ProofResult::Undetermined);

    cleanup!()
}

#[test]
fn dont_get_greedy3() {
    let prover;

    requirements!(let reqs = [
        "c <= a",
        "0 <= c",
        "b <= a",
    ], prover);

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    prove!("c-b+a >= 0" => ProofResult::True);
    prove!("c-b+a+1 >= 0" => ProofResult::True);
    prove!("c-b+a-1 >= 0" => ProofResult::Undetermined);

    cleanup!()
}

#[test]
fn sign_consistency_pt1() {
    let prover;

    requirements!(let reqs = [
        "1 <= x",
        "y/x <= z", // ==> y <= z*x
    ], prover);

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    prove!("y <= z*x" => ProofResult::True);

    cleanup!()
}

#[test]
fn sign_consistency_pt2() {
    let prover;

    requirements!(let reqs = [
        "y/x <= z", // ==> y <= z*x
        "1 <= x",
    ], prover);

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    prove!("y <= z*x" => ProofResult::True);

    cleanup!()
}

#[test]
fn sign_consistency_pt3() {
    let prover;

    requirements!(let reqs = [
        "0-1 >= x",
        "y/x <= z", // ==> y >= z*x
    ], prover);

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    prove!("y >= z*x" => ProofResult::True);

    cleanup!()
}

#[test]
fn sign_consistency_pt4() {
    let prover;

    requirements!(let reqs = [
        "y/x <= z", // ==> y >= z*x
        "0-1 >= x",
    ], prover);

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    prove!("y >= z*x" => ProofResult::True);

    cleanup!()
}

macro_rules! multiple_bounds_stmts {
    () => {
        prove!("0-1 <= x" => ProofResult::True);
        prove!("0 <= x" => ProofResult::True);
        prove!("2 <= x" => ProofResult::True);
        prove!("3 <= x" => ProofResult::True);
        prove!("5 <= x" => ProofResult::True);
        prove!("6 <= x" => ProofResult::Undetermined);
        prove!("10 <= x" => ProofResult::Undetermined);
        prove!("50 <= x" => ProofResult::Undetermined);
        prove!("51 <= x" => ProofResult::False);
        prove!("x <= 50" => ProofResult::True);
        prove!("x <= 55" => ProofResult::True);
        prove!("x <= 60" => ProofResult::True);
        prove!("x <= 49" => ProofResult::Undetermined);
        prove!("x <= 30" => ProofResult::Undetermined);
        prove!("x <= 5" => ProofResult::Undetermined);
        prove!("x <= 4" => ProofResult::False);
    };
}

#[test]
fn multiple_bounds_order_1() {
    let prover;
    requirements!(let reqs = [
        "2 <= x",
        "5 <= x",
        "x <= 50",
        "x <= 60",
    ], prover);
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));
    multiple_bounds_stmts!();
    cleanup!()
}
#[test]
fn multiple_bounds_order_2() {
    let prover;
    requirements!(let reqs = [
        "5 <= x",
        "2 <= x",
        "x <= 60",
        "x <= 50",
    ], prover);
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));
    multiple_bounds_stmts!();
    cleanup!()
}
#[test]
fn multiple_bounds_order_3() {
    let prover;
    requirements!(let reqs = [
        "x <= 60",
        "x <= 50",
        "5 <= x",
        "2 <= x",
    ], prover);
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));
    multiple_bounds_stmts!();
    cleanup!()
}
#[test]
fn multiple_bounds_order_4() {
    let prover;
    requirements!(let reqs = [
        "x <= 60",
        "5 <= x",
        "x <= 50",
        "2 <= x",
    ], prover);
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));
    multiple_bounds_stmts!();
    cleanup!()
}
#[test]
fn multiple_bounds_order_5() {
    let prover;
    requirements!(let reqs = [
        "x <= 60",
        "2 <= x",
        "x <= 50",
        "5 <= x",
    ], prover);
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));
    multiple_bounds_stmts!();
    cleanup!()
}
#[test]
fn multiple_bounds_order_6() {
    let prover;
    requirements!(let reqs = [
        "x <= 50",
        "2 <= x",
        "x <= 60",
        "5 <= x",
    ], prover);
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));
    multiple_bounds_stmts!();
    cleanup!()
}
#[test]
fn multiple_bounds_order_7() {
    let prover;
    requirements!(let reqs = [
        "x <= 50",
        "5 <= x",
        "x <= 60",
        "2 <= x",
    ], prover);
    make_prover!(prover, reqs, max_depth = budget(reqs.len()));
    multiple_bounds_stmts!();
    cleanup!()
}

#[test]
fn non_linear() {
    let prover;

    requirements!(let reqs = [
        "2 <= x",
        "x <= 5",
        "0 <= y",
        "0 <= z",
        "z <= 10",
    ], prover);

    make_prover!(prover, reqs, max_depth = budget(reqs.len()));

    // It's a shame neither method can get 0 <= x*x.
    // I'm hesitant to add powers though.
    prove!("0 <= x*x" => ProofResult::True);
    prove!("4 <= x*x" => ProofResult::True);
    prove!("5 <= x*x" => ProofResult::Undetermined);
    prove!("25 <= x*x" => ProofResult::Undetermined);
    prove!("26 <= x*x" => ProofResult::False);
    prove!("x*x <= 25" => ProofResult::True);
    prove!("x*x <= 26" => ProofResult::True);
    prove!("x*x <= 24" => ProofResult::Undetermined);
    prove!("x*x <= 4" => ProofResult::Undetermined);
    prove!("x*x <= 3" => ProofResult::False);
    prove!("x*y <= 25*y" => ProofResult::True);
    prove!("x*y <= 26*y" => ProofResult::True);
    prove!("x*y <= 5*y" => ProofResult::True);
    prove!("x*y <= 4*y" => ProofResult::Undetermined);
    prove!("x*y <= 0" => ProofResult::Undetermined);
    prove!("x*(y+z)+y <= 6*y+5*z" => ProofResult::True);
    prove!("x*(y+z)+y <= 6*y+4*z" => ProofResult::Undetermined);
    prove!("x*(y+z)+y <= 5*y+5*z" => ProofResult::Undetermined);
    prove!("x*(y+z)+y <= 5*y+4*z" => ProofResult::Undetermined);
    prove!("x*(y+z)+y <= 6*y+50" => ProofResult::True);
    prove!("x*(y+z)+y <= 6*y+49" => ProofResult::Undetermined);
    prove!("x*(y+z)+y <= 6*y" => ProofResult::Undetermined);
    prove!("x*(y+z)+y <= 6*y+51" => ProofResult::True);
    prove!("0-x*(y+z)-y >= 0-6*y-50" => ProofResult::True);
    prove!("y-x*(y+z) >= 0-4*y-50" => ProofResult::True);
    prove!("0-x*(y+z)-y >= 0-6*y-49" => ProofResult::Undetermined);
    prove!("y-x*(y+z) >= 0-4*y-51" => ProofResult::True);
    prove!("0 <= x*z" => ProofResult::True);
    prove!("0-1 <= x*z" => ProofResult::True);
    prove!("1 <= x*z" => ProofResult::Undetermined);
    prove!("x*z <= 50" => ProofResult::True);
    prove!("x*z <= 51" => ProofResult::True);
    prove!("x*z <= 49" => ProofResult::Undetermined);
    prove!("x*z <= 0" => ProofResult::Undetermined);
    prove!("x*z <= 0-1" => ProofResult::False);
    prove!("x*z-y <= 50" => ProofResult::True);
    prove!("x*z-y <= 51" => ProofResult::True);
    prove!("x*z-y <= 49" => ProofResult::Undetermined);
    prove!("x*z-y >= 0" => ProofResult::Undetermined);

    cleanup!()
}
