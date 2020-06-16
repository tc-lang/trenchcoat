use super::expr::Expr;
use super::fast_optimiser::{Maximizer, Minimizer};
use super::int::Int;
use super::{ProofResult, Requirement, ScopedSimpleProver, SimpleProver};

pub type FullProver<'a> = ScopedSimpleProver<'a, Prover<'a>>;

pub struct Prover<'a> {
    given: Vec<Expr<'a>>,
    max_depth: isize,
}

pub fn default_budget(n: usize) -> isize {
    let ni = n as isize;
    // There's a bit of maths behind this, but not loads. Feel free to change it.
    ni * ni + ni + 1
}

impl<'a> SimpleProver<'a> for Prover<'a> {
    fn new(reqs: Vec<Requirement<'a>>) -> Prover<'a> {
        let reqs = reqs
            .iter()
            .map(|req| req.ge0().simplify())
            .collect::<Vec<Expr>>();
        let n = reqs.len();
        Prover {
            given: reqs,
            max_depth: default_budget(n),
        }
    }

    fn prove(&self, prop: &Requirement<'a>) -> ProofResult {
        // prop is true if and only if ge0 >= 0
        // So we will bound ge0 and see if we can prove that it's >= 0 or that it's < 0
        let ge0 = prop.ge0().simplify();

        let mini = Minimizer::new(ge0.clone(), self.given.clone(), self.max_depth);
        if mini.int_bounds().any(|bound| bound >= Int::ZERO) {
            return ProofResult::True;
        }

        let maxi = Maximizer::new(ge0, self.given.clone(), self.max_depth);
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
        self.max_depth = max_depth
    }
}
