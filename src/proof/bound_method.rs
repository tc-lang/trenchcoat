use super::bound_group::BoundGroup;
use super::int::Int;
use super::optimiser::{Maximizer, Minimizer};
use super::{ProofResult, Requirement, ScopedSimpleProver, SimpleProver};

pub type FullProver<'a> = ScopedSimpleProver<'a, Prover<'a>>;

pub struct Prover<'a> {
    bound_group: BoundGroup<'a>,
    max_depth: isize,
}

pub fn default_budget(n: usize) -> isize {
    let ni = n as isize;
    // There isn't much maths behind this, feel free to change it.
    ni + (ni*ni/32).min(32) + 3*ni.min(32)
}

impl<'a> SimpleProver<'a> for Prover<'a> {
    fn new(reqs: Vec<Requirement<'a>>) -> Prover<'a> {
        let reqs = reqs.iter().map(Requirement::simplify).collect();
        let bg = BoundGroup::from_requirements(reqs);
        Prover {
            bound_group: bg.clone(),
            max_depth: default_budget(bg.iter().count()),
        }
    }

    fn prove(&self, req: &Requirement) -> ProofResult {
        // req is true if and only if ge0 >= 0
        // So we will bound ge0 and see if we can prove that it's >= 0 or that it's < 0
        let ge0 = req.ge0().simplify();

        let mini = Minimizer::new(
            ge0.clone(),
            self.bound_group.clone(),
            self.max_depth,
        );
        if mini.int_bounds().any(|bound| bound >= Int::ZERO) {
            return ProofResult::True;
        }

        let maxi = Maximizer::new(
            ge0,
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
    pub fn max_depth(&self) -> isize {
        self.max_depth
    }
    pub fn set_max_depth(&mut self, max_depth: isize) {
        //self.max_depth = max_depth
    }
}
