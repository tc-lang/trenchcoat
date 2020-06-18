use super::bound::{bounds_on_ge0, Bound, Relation, RelationKind};
use super::expr::{zero, Expr};
use super::int::Int;
use super::optimiser::{options, options::Options, Maximizer, Minimizer};
use super::{ProofResult, Requirement, ScopedSimpleProver, SimpleProver};
use crate::ast::Ident;
use crate::little_cache::Cache as LittleCache;

pub type DefaultSimpleProver<'a> = Prover<'a, options::DefaultMode, options::LemmaMode>;
pub type DefaultProver<'a, 'b> = ScopedSimpleProver<'a, 'b, DefaultSimpleProver<'a>>;

pub struct Prover<'a, Opt: Options, LOpt: Options> {
    given: Vec<Expr<'a>>,
    max_depth: isize,
    sign_cache: LittleCache<Ident<'a>, i8>,
    options: Opt,
    lemma_options: LOpt,
}

pub fn default_budget(n: usize) -> isize {
    let ni = n as isize;
    // There's a bit of maths behind this, but not loads. Feel free to change it.
    ni * ni + ni + 1 + 10000000
}

impl<'a, Opt: Options, LOpt: Options> SimpleProver<'a> for Prover<'a, Opt, LOpt> {
    fn new(reqs: Vec<Requirement<'a>>) -> Prover<'a, Opt, LOpt> {
        let reqs = reqs
            .iter()
            .map(|req| req.ge0().simplify())
            .collect::<Vec<Expr>>();
        let n = reqs.len();
        let mut out = Prover {
            given: reqs,
            max_depth: default_budget(n),
            sign_cache: LittleCache::new(8),
            options: Opt::init(),
            lemma_options: LOpt::init(),
        };
        out.calc_signs();
        out
    }

    fn prove(&self, prop: &Requirement<'a>) -> ProofResult {
        self.prove_with_options(prop, self.options.clone())
    }
    fn prove_lemma(&self, prop: &Requirement<'a>) -> ProofResult {
        self.prove_with_options(prop, self.lemma_options.clone())
    }
}

impl<'a, Opt: Options, LOpt: Options> Prover<'a, Opt, LOpt> {
    fn prove_with_options(&self, prop: &Requirement<'a>, options: impl Options) -> ProofResult {
        // prop is true if and only if ge0 >= 0
        // So we will bound ge0 and see if we can prove that it's >= 0 or that it's < 0
        let ge0 = prop.ge0().simplify();

        let mini = Minimizer::new(
            ge0.clone(),
            self.given.clone(),
            self.max_depth,
            &self.sign_cache,
            options.clone(),
        );
        if mini.int_bounds().any(|bound| bound >= Int::ZERO) {
            return ProofResult::True;
        }

        let maxi = Maximizer::new(
            ge0,
            self.given.clone(),
            self.max_depth,
            &self.sign_cache,
            options,
        );
        if maxi.int_bounds().any(|bound| bound < Int::ZERO) {
            return ProofResult::False;
        }

        ProofResult::Undetermined
    }
}

/// Filters out elements of expr which contradict with the requirements `prover` has.
macro_rules! filter_contradictions {
    ($prover:expr, $props:expr) => {
        $props.filter(|prop| match $prover.prove(prop) {
            ProofResult::Undetermined => true,
            ProofResult::False => false,
            ProofResult::True => panic!("requirement already implied"),
        })
    };
}

/// Returns an iterator of requirements that:
/// - if added to `prover`, would make `prop` true and
/// - don't contradict with the pre-existing requirements.
macro_rules! help_suggestions {
    ($prover:expr, $prop:expr) => {
        filter_contradictions!($prover, $prover.sorted_implication_requirements($prop))
    };
}

impl<'a, Opt: Options, LOpt: Options> Prover<'a, Opt, LOpt> {
    pub fn max_depth(&self) -> isize {
        self.max_depth
    }
    pub fn set_max_depth(&mut self, max_depth: isize) {
        self.max_depth = max_depth
    }

    fn calc_signs(&mut self) {
        let mut variables = Vec::new();
        for req in self.given.iter() {
            variables.extend(req.variables());
        }
        variables.sort_unstable();
        variables.dedup();
        'idk: loop {
            for var in variables.iter() {
                if self.sign_cache.get(&var).is_some() {
                    continue;
                }
                for ge0 in self.given.iter() {
                    match bounds_on_ge0(&ge0, &var, |x| self.sign_cache.get(x)) {
                        Some(Bound::Le(expr)) => match expr.sign(|x| self.sign_cache.get(x)) {
                            Some(-1) => {
                                self.sign_cache.set(var.clone(), -1);
                                continue 'idk;
                            }
                            _ => (),
                        },
                        Some(Bound::Ge(expr)) => match expr.sign(|x| self.sign_cache.get(x)) {
                            Some(1) => {
                                self.sign_cache.set(var.clone(), 1);
                                continue 'idk;
                            }
                            _ => (),
                        },
                        None => (),
                    }
                }
            }
            break;
        }
    }

    /// Returns an iterator of expressions which, if ≥0, with the existing requirements, make
    /// `prop` provably true.
    pub fn implication_bounds(&self, prop: &Requirement<'a>) -> impl Iterator<Item = Expr<'a>> {
        Minimizer::new(
            prop.ge0(),
            self.given.clone(),
            self.max_depth,
            todo!(),
            options::HelpMode::init(),
        )
    }

    /// Returns the implication bounds for `prop` (as returned by self.implication_bounds()),
    /// ordered in increasing "complexity" (complexity is currently defined as the number
    /// of distinct variables in the requirement).
    pub fn sorted_implication_bounds(&self, prop: &Requirement<'a>) -> Vec<Expr<'a>> {
        let mut exprs = self.implication_bounds(prop).collect::<Vec<Expr<'a>>>();
        // This sort in intentionally stable since, if the bound was returned first, it would be
        // checked sooner in the proof run, so using an earlier returned bound yields faster proof
        // times.
        exprs.sort_by_key(|expr| expr.variables().len());
        exprs
    }

    /// Returns all of the least complex implication bounds (as returned by
    /// self.implication_bounds()).
    /// Complexity has the same definition as in self.sorted_implication_bounds.
    pub fn best_implication_bounds(&self, prop: &Requirement<'a>) -> Vec<Expr<'a>> {
        let exprs = self.implication_bounds(prop);
        let mut best_n = usize::MAX;
        let mut best_exprs = Vec::new();
        for expr in exprs {
            // TODO Perhaps filter by what the bounds method can prove with?
            let n_vars = expr.variables().len();
            if n_vars == best_n {
                best_exprs.push(expr);
            } else if n_vars < best_n {
                best_n = n_vars;
                best_exprs.clear();
                best_exprs.push(expr);
            }
        }
        best_exprs
    }

    /// Returns the values from self.best_implication_bounds as Requirements
    pub fn best_implication_requirements(
        &self,
        prop: &Requirement<'a>,
    ) -> impl Iterator<Item = Requirement<'a>> {
        self.best_implication_bounds(prop)
            .into_iter()
            .map(|expr| Requirement {
                // TODO Rearrange to make this look nicer
                relation: Relation {
                    left: expr.clone(),
                    kind: RelationKind::Ge,
                    right: zero(),
                },
            })
    }

    /// Returns the values from self.sorted_implication_bounds as Requirements
    pub fn sorted_implication_requirements(
        &self,
        prop: &Requirement<'a>,
    ) -> impl Iterator<Item = Requirement<'a>> {
        self.sorted_implication_bounds(prop)
            .into_iter()
            .map(|expr| Requirement {
                // TODO Rearrange to make this look nicer
                relation: Relation {
                    left: expr.clone(),
                    kind: RelationKind::Ge,
                    right: zero(),
                },
            })
    }

    /// Returns up to n help suggestions.
    /// A help suggestion is a requirement that can be added to self which would make `prop`
    /// provably true without contradicting the existing requirements.
    /// The suggestions are ordered in increasing order of complexity as defined by
    /// self.sorted_implication_bounds.
    pub fn some_help_suggestions(&self, n: usize, prop: &Requirement<'a>) -> Vec<Requirement<'a>> {
        help_suggestions!(self, prop).take(n).collect()
    }
}
