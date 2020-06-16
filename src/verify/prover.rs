use crate::ast::Ident;
use crate::proof::expr::Atom;
use crate::proof::{Expr, ProofResult, Prover, Requirement, ScopedSimpleProver, SimpleProver};
use crate::tokens::FAKE_TOKEN;
use std::ops::Deref;
use std::pin::Pin;

#[cfg(feature = "bounds")]
use crate::proof::fast_bound_method::FullProver as InnerProver;
#[cfg(feature = "graph")]
use crate::proof::graph::FullProver as InnerProver;

#[cfg(not(any(feature = "bounds", feature = "graph")))]
compile_error!("Either the 'graph' feature or the 'bounds' feature must be enabled");

#[cfg(not(any(feature = "bounds", feature = "graph")))]
type InnerProver<'a> = ScopedSimpleProver<'a, Dummy>;

const MIN_TMP_UNDERSCORES: usize = 2;

pub struct WrappedProver<'a> {
    /// The inner prover
    ///
    /// This is stored as an `Option` so that temporary movement in and out of this field can be
    /// done safely. This value will always be `Some` before and after each method call.
    ///
    /// This prover may have been created with borrowed content from the last value in
    /// `dependent_provers`.
    prover: Option<InnerProver<'a>>,

    /// A stored list of the current requirements
    ///
    /// This is used so that we can re-build the prover upon adding new requirements
    reqs: Vec<Requirement<'a>>,

    /// The provers used to build the current one. Each value may have borrowed content from the
    /// prover at the previous index.
    dependent_provers: Vec<Pin<Box<InnerProver<'a>>>>,

    /// The set of temporary variables used, by name
    ///
    /// These may sometimes be referenced by the requirements in `prover`, so they must be treated
    /// carefully. The implementation of `Drop` reflects this.
    temp_vars: Vec<Pin<String>>,

    /// The next id to use for a temp variable. For example, if this value is 4, the next temp
    /// variable generated will be '<4>'
    next_temp_id: usize,
}

impl<'a> Drop for WrappedProver<'a> {
    fn drop(&mut self) {
        // We provide a manual implementation of `Drop` in order to ensure that the lifetime of any
        // temporary variables in `temp_vars` exceeds where they are used - which could be in
        // `prover`
        self.prover = None;

        // We also need to drop each of the dependent provers in the reverse order that they were
        // created, because they reference earlier ones.
        self.dependent_provers
            .drain(..)
            .rev()
            .for_each(std::mem::drop);

        // and now we drop the variables themselves
        //
        // This doesn't *really* need to be done, but we have it here for the sake of explicitness,
        // and because rust doesn't necessarily guarantee drop order if left to its own devices.
        self.temp_vars = Vec::new();
    }
}

impl<'a> WrappedProver<'a> {
    pub fn new(reqs: Vec<Requirement<'a>>) -> Self {
        Self {
            prover: Some(InnerProver::new(reqs.clone())),
            reqs,
            dependent_provers: Vec::new(),
            temp_vars: Vec::new(),
            next_temp_id: 0,
        }
    }

    pub fn prove(&self, req: &Requirement) -> ProofResult {
        self.prover.as_ref().unwrap().prove(req)
    }

    pub fn define(&mut self, x: Ident<'a>, expr: Expr<'a>) {
        self.dependent_provers
            .push(Pin::new(Box::new(self.prover.take().unwrap())));
        let new_prover: InnerProver = self.dependent_provers.last().unwrap().define(x, expr);

        // We now know that this the data stored here will be valid later, so we're free to extend
        // the lifetime of `new_prover` via transmute.
        let new_prover: InnerProver = unsafe { std::mem::transmute(new_prover) };
        self.prover = Some(new_prover);
    }

    pub fn shadow(&mut self, x: Ident<'a>) {
        self.dependent_provers
            .push(Pin::new(Box::new(self.prover.take().unwrap())));
        let new_prover: InnerProver = self.dependent_provers.last().unwrap().shadow(x);

        // We now know that this the data stored here will be valid later, so we're free to extend
        // the lifetime of `new_prover` via transmute.
        let new_prover: InnerProver = unsafe { std::mem::transmute(new_prover) };
        self.prover = Some(new_prover);
    }

    /// Generates a new temporary identifier, based on the prover
    ///
    /// This identifier *MUST* be passed back into the prover or dropped before the prover. Any
    /// other usage will not guarantee proper behavior.
    ///
    /// The referenced content of the `Ident` may also move upon any call to `add_reqs`. Holding
    /// onto the returned `Ident` under those conditions *will* produce exceptionally rare
    /// segfaults.
    #[allow(unused_unsafe)]
    pub unsafe fn gen_new_tmp(&mut self) -> Ident<'a> {
        self.temp_vars
            .push(Pin::new(format!("<{}>", self.next_temp_id)));
        self.next_temp_id += 1;

        let name: &str = &self.temp_vars.last().unwrap();

        // Lifetime extension - this is guaranteed by the promise on this function.
        let name: &str = unsafe { &*(name as *const str) };

        Ident {
            name,
            source: &FAKE_TOKEN,
        }
    }

    /// Adds the list of requirements to the prover, adjusting the names of any temporary variables
    /// as necessary.
    pub fn add_reqs(&mut self, reqs: Vec<Requirement<'a>>) {
        if reqs.is_empty() {
            return;
        }

        fn remake<'b>(
            prover: &InnerProver<'b>,
            mut base: Vec<Requirement<'b>>,
            with: Vec<Requirement<'b>>,
        ) -> (
            Vec<Pin<Box<InnerProver<'b>>>>,
            InnerProver<'b>,
            Vec<Requirement<'b>>,
        ) {
            use std::mem::transmute;
            use ScopedSimpleProver::{Defn, Root, Shadow};

            match prover {
                Defn { x, expr, parent } => {
                    let with = with
                        .into_iter()
                        .map(|req| req.substitute(*x, expr))
                        .collect::<Vec<_>>();
                    let (mut new_deps, new_prover, new_reqs) = remake(parent, base, with);
                    new_deps.push(Pin::new(Box::new(new_prover)));
                    let prover: InnerProver = new_deps.last().unwrap().define(*x, expr.clone());
                    let prover: InnerProver = unsafe { transmute(prover) };

                    (new_deps, prover, new_reqs)
                }
                Shadow { x, parent } => {
                    let with = with
                        .into_iter()
                        .filter(|req| !req.variables().contains(x))
                        .collect::<Vec<_>>();
                    let (mut new_deps, new_prover, new_reqs) = remake(parent, base, with);
                    new_deps.push(Pin::new(Box::new(new_prover)));
                    let prover: InnerProver = new_deps.last().unwrap().shadow(*x);
                    let prover: InnerProver = unsafe { transmute(prover) };

                    (new_deps, prover, new_reqs)
                }
                Root(p) => {
                    base.extend(with);
                    (Vec::new(), Prover::new(base.clone()), base)
                }
            }
        }

        let old_reqs = std::mem::replace(&mut self.reqs, Vec::new());
        let (new_deps, new_prover, new_reqs) =
            remake(self.prover.as_ref().unwrap(), old_reqs, reqs);

        // Carefully drop all of the old provers
        self.prover = None;
        self.dependent_provers
            .drain(..)
            .rev()
            .for_each(std::mem::drop);

        // Lifetime extension - safe for the same reasons as given in other functions
        self.reqs = new_reqs;
        self.dependent_provers = new_deps;
        self.prover = Some(new_prover);
    }
}

/// A dummy implemetor of `proof::SimpleProver` so that we reduce the number of errors if no
/// features are given.
#[derive(Debug)]
struct Dummy;

impl<'a> SimpleProver<'a> for Dummy {
    fn new(_: Vec<Requirement<'a>>) -> Self {
        unreachable!()
    }

    fn prove(&self, _: &Requirement) -> ProofResult {
        unreachable!()
    }
}