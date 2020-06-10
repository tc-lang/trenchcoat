use super::bound_group::BoundGroup;
use super::int::Int;
use super::optimiser::{Maximizer, Minimizer};
use super::{ProofResult, Requirement, ScopedSimpleProver, SimpleProver};

pub type FullProver<'a> = ScopedSimpleProver<'a, Prover<'a>>;

pub struct Prover<'a> {
    bound_group: BoundGroup<'a>,
    max_depth: usize,
}

impl<'a> SimpleProver<'a> for Prover<'a> {
    fn new(reqs: Vec<Requirement<'a>>) -> Prover<'a> {
        let reqs = reqs.iter().map(Requirement::simplify).collect();
        Prover {
            bound_group: BoundGroup::from_requirements(reqs),
            max_depth: 10,
        }
    }

    fn prove(&self, req: &Requirement) -> ProofResult {
        // The SimpleProver trait doesn't allow us to assume that req is simplified so we must
        // simplify it ourself.
        let req = req.simplify();

        let mini = Minimizer::new_root(
            req.ge0().simplify(),
            self.bound_group.clone(),
            self.max_depth,
        );
        // The statement is always true if a lower bound is >= 0
        if mini.int_bounds().any(|bound| bound >= Int::ZERO) {
            return ProofResult::True;
        }
        // The statement is always false if an upper bound is < 0
        let maxi = Maximizer::new_root(
            req.ge0().simplify(),
            self.bound_group.clone(),
            self.max_depth,
        );
        if maxi.int_bounds().any(|bound| bound < Int::ZERO) {
            return ProofResult::False;
        }
        ProofResult::Undetermined
    }
}

impl<'a> Prover<'a> {
    pub fn max_depth(&self) -> usize {
        self.max_depth
    }
    pub fn set_max_depth(&mut self, max_depth: usize) {
        self.max_depth = max_depth
    }
}
