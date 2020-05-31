use super::bound::Bound;
use super::int::Int;
use super::optimiser::{Maximizer, Minimizer};
use super::{ProofResult, Requirement, SimpleProver, ScopedSimpleProver};
use crate::ast::Ident;

pub type FullProver<'a> = ScopedSimpleProver<'a, Prover<'a>>;

pub struct Prover<'a> {
    bounds: Vec<(Ident<'a>, Bound<'a>)>,
    max_depth: usize,
}

impl<'a> SimpleProver<'a> for Prover<'a> {
    fn new(reqs: Vec<Requirement<'a>>) -> Prover<'a> {
        Prover {
            bounds: reqs.iter().map(|req| req.bounds()).flatten().collect(),
            max_depth: 10,
        }
    }

    fn prove(&self, req: &Requirement) -> ProofResult {
        let mini = Minimizer::new(self.bounds.clone(), req.ge0.clone(), self.max_depth);
        // The statement is always true if a lower bound is >= 0
        if mini.int_bounds().any(|bound| bound >= Int::ZERO) {
            return ProofResult::True;
        }
        // The statement is always false if an upper bound is < 0
        let maxi = Maximizer::new(self.bounds.clone(), req.ge0.clone(), self.max_depth);
        if maxi.int_bounds().any(|bound| bound < Int::ZERO) {
            return ProofResult::False;
        }
        ProofResult::Undetermined
    }
}

impl<'a> Prover<'a> {
    pub fn max_depth(&self) -> usize { self.max_depth }
    pub fn set_max_depth(&mut self, max_depth: usize) { self.max_depth = max_depth }
}
