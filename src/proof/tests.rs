use super::bound_method::FullProver;
use super::{ProofResult, Prover, Requirement};
use crate::ast::proof::Condition;
use crate::tokens::tokenize;

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

    let prover = FullProver::new(reqs);

    fn prove<'a>(prover: &impl Prover<'a>, stmt: &'a str) -> ProofResult {
        let tokens = tokenize(stmt);
        let cond = Condition::parse(&tokens).unwrap();
        let req = Requirement::from(&cond);
        prover.prove(&req)
    }

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
