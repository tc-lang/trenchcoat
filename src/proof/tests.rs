use super::{Prover, Requirement, ProofResult};
use super::bound_method::FullProver;
use crate::ast::proof::Condition;
use crate::tokens::tokenize;

#[test]
fn example_test() {
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

    assert!(prove(&prover, "0 <= x") == ProofResult::True);
    assert!(prove(&prover, "x <= 10") == ProofResult::True);
    assert!(prove(&prover, "y <= 10") == ProofResult::True);
    assert!(prove(&prover, "y <= 9") == ProofResult::True);
    assert!(prove(&prover, "x+y <= 10") == ProofResult::True);
    assert!(prove(&prover, "2*x+y <= 20") == ProofResult::True);
    assert!(prove(&prover, "x+2*y <= 20") == ProofResult::True);
    assert!(prove(&prover, "x+2*y <= 19") == ProofResult::True);
}

/* BBQ
 * Shed
 * Paracol */
