use crate::ast::{self, Ident, IdentSource, Node};
use crate::proof::{Expr, ProofResult, Prover, Requirement, ScopedSimpleProver, SimpleProver};
use crate::tokens::FAKE_TOKEN;
use std::ops::{BitOr, BitOrAssign, Deref, DerefMut};
use std::pin::Pin;

#[cfg(feature = "bounds")]
use crate::proof::bound_method::DefaultProver as InnerProver;
#[cfg(feature = "graph")]
use crate::proof::graph::FullProver as InnerProver;

#[cfg(not(any(feature = "bounds", feature = "graph")))]
use crate::proof::StandardProver as InnerProver;

pub struct WrappedProver<'a, 'b> {
    /// The inner prover
    ///
    /// This is stored as an `Option` so that temporary movement in and out of this field can be
    /// done safely. This value will always be `Some` before and after each method call.
    ///
    /// This prover may have been created with borrowed content from the last value in
    /// `dependent_provers`.
    prover: Option<InnerProver<'a, 'b>>,

    /// A stored list of the current requirements
    ///
    /// This is used so that we can re-build the prover upon adding new requirements
    reqs: Vec<Requirement<'a>>,

    /// The provers used to build the current one. Each value may have borrowed content from the
    /// prover at the previous index.
    dependent_provers: Vec<Pin<Box<InnerProver<'a, 'b>>>>,

    /// The set of temporary variables used, by name
    ///
    /// These may sometimes be referenced by the requirements in `prover`, so they must be treated
    /// carefully. The implementation of `Drop` reflects this.
    temp_vars: Vec<Pin<String>>,

    /// The next id to use for a temp variable. For example, if this value is 4, the next temp
    /// variable generated will be '<4>'
    next_temp_id: usize,
}

/// A wrapper type for maintaining multiple different sets of proofs at the same time
pub struct Provers<'a, 'b> {
    provers: Vec<ProverSetItem<'a, 'b>>,
    mask: Mask,
}

/// A single item in a prover set
pub struct ProverSetItem<'a, 'b> {
    pub prover: WrappedProver<'a, 'b>,

    /// Any *extra* requirements the prover was given, due to the precondition of a contract
    ///
    /// The added `Node` provides the original source of the requirement, so that we can point back
    /// to it later.
    pub pre: &'a [Requirement<'a>],

    /// The source for the preconditions. This must be `Some(_)` if there are any
    /// pre-conditions, but having post-conditions does *not* necessarily imply this should exist
    pub pre_source: Option<Node<'a>>,

    /// Any requirements the prover must be able to show at the end of the function, given in terms
    /// of the function arguments and
    pub post: &'a [Requirement<'a>],

    /// The source for post-conditions. This should be `Some(_)` if there are any post-conditions.
    pub post_source: Option<Node<'a>>,
}

#[derive(Debug, Clone)]
pub struct Mask {
    size: usize,
    repr: MaskType,
}

#[derive(Debug, Clone)]
enum MaskType {
    All,
    Nothing,
    // The usize is the number of indices not currently masked
    Mix(Vec<bool>, usize),
}

impl<'a, 'p> Drop for WrappedProver<'a, 'p> {
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

impl<'a, 'p> WrappedProver<'a, 'p> {
    pub fn new(reqs: Vec<Requirement<'a>>) -> Self {
        Self {
            prover: Some(InnerProver::new(reqs.clone())),
            reqs,
            dependent_provers: Vec::new(),
            temp_vars: Vec::new(),
            next_temp_id: 0,
        }
    }

    pub fn prove(&self, req: &Requirement<'a>) -> ProofResult {
        self.prover.as_ref().unwrap().prove(req)
    }

    pub fn prove_lemma(&self, req: &Requirement<'a>) -> ProofResult {
        self.prover.as_ref().unwrap().prove_lemma(req)
    }

    pub fn prove_return(&self, req: &Requirement<'a>, ret_ident: Ident<'a>) -> ProofResult {
        use ScopedSimpleProver::{Defn, Root, Shadow};

        let mut replacement = Expr::from(ret_ident);

        // replace based on the current prover
        match self.prover.as_ref().unwrap() {
            Root(_) => (),
            Defn { x, expr, .. } => replacement = replacement.substitute(x, expr),
            Shadow { x, .. } => {
                if replacement.variables().contains(&x) {
                    return ProofResult::Undetermined;
                }
            }
        }

        for p in self.dependent_provers.iter().rev() {
            match p.deref() {
                Root(_) => (),
                Defn { x, expr, .. } => replacement = replacement.substitute(x, expr),
                Shadow { x, .. } => {
                    if replacement.variables().contains(&x) {
                        return ProofResult::Undetermined;
                    }
                }
            }
        }

        let return_ident = Ident {
            name: "_",
            source: IdentSource::Token(&FAKE_TOKEN),
        };
        let base_req = req.substitute(&return_ident, &replacement);

        let root_prover = match self.dependent_provers.deref() {
            [root, ..] => root,
            [] => self.prover.as_ref().unwrap(),
        };

        root_prover.prove(&base_req)
    }

    pub fn define(&mut self, x: Ident<'a>, expr: Expr<'a>) {
        self.dependent_provers
            .push(Pin::new(Box::new(self.prover.take().unwrap())));

        // We extend the lifetime of `last_prover` because the data we know the data we're storing
        // will be valid later
        //
        // Should you, oh foolish adventurer, think to abbreviate your incanatations by transmuting
        // before hinting, know that only danger lies down that road. Alas! Those who follow never
        // listen! So go ahead - see it for yourself. And watch it crash and burn in front of your
        // disbelieving eyes.
        //
        // For good fun, merge the following two lines into one. All the types are known, so it
        // should be fine, right?
        let last_prover: &InnerProver = self.dependent_provers.last().unwrap();
        let last_prover: &InnerProver = unsafe { std::mem::transmute(last_prover) };
        let new_prover: InnerProver = last_prover.define(x, expr);

        self.prover = Some(new_prover);
    }

    pub fn shadow(&mut self, x: Ident<'a>) {
        self.dependent_provers
            .push(Pin::new(Box::new(self.prover.take().unwrap())));

        // We extend the lifetime of `last_prover` because the data we know the data we're storing
        // will be valid later
        let last_prover: &InnerProver =
            unsafe { std::mem::transmute(self.dependent_provers.last().unwrap()) };
        let new_prover: InnerProver = last_prover.shadow(x);

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
    pub unsafe fn gen_new_tmp(&mut self, expr: &'a ast::Expr<'a>) -> Ident<'a> {
        self.temp_vars
            .push(Pin::new(format!("<{}>", self.next_temp_id)));
        self.next_temp_id += 1;

        let name: &str = &self.temp_vars.last().unwrap();

        // Lifetime extension - this is guaranteed by the promise on this function.
        let name: &str = unsafe { &*(name as *const str) };

        Ident {
            name,
            source: IdentSource::RefExpr(expr),
        }
    }

    /// Adds the list of requirements to the prover, adjusting the names of any temporary variables
    /// as necessary.
    pub fn add_reqs(&mut self, reqs: Vec<Requirement<'a>>) {
        if reqs.is_empty() {
            return;
        }

        fn remake<'b, 'p>(
            prover: &InnerProver<'b, 'p>,
            mut base: Vec<Requirement<'b>>,
            with: Vec<Requirement<'b>>,
        ) -> (
            Vec<Pin<Box<InnerProver<'b, 'p>>>>,
            InnerProver<'b, 'p>,
            Vec<Requirement<'b>>,
        ) {
            use std::mem::transmute;
            use ScopedSimpleProver::{Defn, Root, Shadow};

            match prover {
                Defn { x, expr, parent } => {
                    let with = with
                        .into_iter()
                        .map(|req| req.substitute(x, expr))
                        .collect::<Vec<_>>();
                    let (mut new_deps, new_prover, new_reqs) = remake(parent, base, with);
                    new_deps.push(Pin::new(Box::new(new_prover)));
                    let prover: InnerProver =
                        new_deps.last().unwrap().define(x.clone(), expr.clone());
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
                    let prover: InnerProver = new_deps.last().unwrap().shadow(x.clone());
                    let prover: InnerProver = unsafe { transmute(prover) };

                    (new_deps, prover, new_reqs)
                }
                Root(_) => {
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

impl<'a, 'b> ProverSetItem<'a, 'b> {
    pub fn new(
        base: &'a [Requirement<'a>],
        pre: &'a [Requirement<'a>],
        pre_source: Option<Node<'a>>,
        post: &'a [Requirement<'a>],
        post_source: Option<Node<'a>>,
    ) -> Self {
        let reqs = base.iter().cloned().chain(pre.iter().cloned()).collect();
        let prover = WrappedProver::new(reqs);

        Self {
            prover,
            pre,
            pre_source,
            post,
            post_source,
        }
    }
}

impl<'a, 'b> Provers<'a, 'b> {
    pub fn new(items: Vec<ProverSetItem<'a, 'b>>) -> Self {
        assert!(!items.is_empty());

        Provers {
            mask: Mask::none(items.len()),
            provers: items,
        }
    }

    pub fn get_mask(&self) -> Mask {
        self.mask.clone()
    }

    pub fn mask_mut(&mut self) -> &mut Mask {
        &mut self.mask
    }

    /// Returns the number of provers stored
    pub fn size(&self) -> usize {
        self.provers.len()
    }

    /// Attempts to prove the given requirements for all provers simultaneously, returning - for
    /// each prover - its index and whether the requirements were all proven true.
    ///
    /// The mask allows individual provers to be ignored - their values will always be true.
    pub fn prove_all(&self, reqs: &[Requirement<'a>]) -> Vec<(usize, bool)> {
        self.provers
            .iter()
            .enumerate()
            .map(|(i, p)| match self.mask.allows(i) {
                true => (i, reqs.iter().all(|req| p.prove(req) == ProofResult::True)),
                false => (i, true),
            })
            .collect()
    }

    /// Attempts to prove the requirements using the lemma prover for all provers simultaneously,
    /// returning - for each prover - its index and whether the requirement was proven true.
    ///
    /// The mask allows individual provers to be ignored - their values will always be true.
    pub fn prove_lemma(&self, reqs: &[Requirement<'a>]) -> Vec<(usize, bool)> {
        self.provers
            .iter()
            .enumerate()
            .map(|(i, p)| match self.mask.allows(i) {
                true => (
                    i,
                    reqs.iter()
                        .all(|req| p.prove_lemma(req) == ProofResult::True),
                ),
                false => (i, true),
            })
            .collect()
    }

    pub fn define(&mut self, x: Ident<'a>, expr: Expr<'a>) {
        self.provers
            .iter_mut()
            .for_each(|p| p.define(x.clone(), expr.clone()));
    }

    pub fn shadow(&mut self, x: Ident<'a>) {
        self.provers.iter_mut().for_each(|p| p.shadow(x.clone()));
    }

    pub unsafe fn gen_new_tmp(&mut self, expr: &'a ast::Expr<'a>) -> Ident<'a> {
        let tmp = self.provers[0].gen_new_tmp(expr);
        self.provers[1..]
            .iter_mut()
            .for_each(|p| assert_eq!(p.gen_new_tmp(expr), tmp));
        tmp
    }

    pub fn add_reqs(&mut self, reqs: Vec<Requirement<'a>>) {
        self.provers[1..]
            .iter_mut()
            .for_each(|p| p.add_reqs(reqs.clone()));
        self.provers[0].add_reqs(reqs);
    }
}

impl Mask {
    pub fn block(&mut self, idx: usize) {
        match &mut self.repr {
            MaskType::Nothing => {
                let mut v = vec![false; self.size];
                v[idx] = true;
                self.repr = MaskType::Mix(v, self.size - 1);
            }
            // Everything's already masked, so there's nothing more we can do
            MaskType::All => (),
            MaskType::Mix(v, ref mut n_open) => {
                if !v[idx] {
                    *n_open -= 1;
                    v[idx] = true;
                }

                if *n_open == 0 {
                    // drop((v, n_open));
                    self.repr = MaskType::All;
                }
            }
        }
    }

    pub fn allows(&self, idx: usize) -> bool {
        match &self.repr {
            MaskType::All => false,
            MaskType::Nothing => true,
            MaskType::Mix(v, _) => !v[idx],
        }
    }

    pub fn none(size: usize) -> Mask {
        Mask {
            size,
            repr: MaskType::Nothing,
        }
    }

    pub fn all(size: usize) -> Mask {
        Mask {
            size,
            repr: MaskType::All,
        }
    }
}

impl BitOr for Mask {
    type Output = Mask;

    fn bitor(self, rhs: Mask) -> Mask {
        use MaskType::{All, Mix, Nothing};

        assert_eq!(self.size, rhs.size);

        let repr = match (self.repr, rhs.repr) {
            (Nothing, Nothing) => Nothing,
            (All, _) | (_, All) => All,
            (Mix(v, n), Nothing) | (Nothing, Mix(v, n)) => Mix(v, n),
            (Mix(xs, _), Mix(ys, _)) => {
                let v = xs
                    .into_iter()
                    .zip(ys.into_iter())
                    .map(|(x, y)| x || y)
                    .collect::<Vec<_>>();
                let n = v.iter().filter(|&m| !m).count();

                match n {
                    0 => All,
                    _ => Mix(v, n),
                }
            }
        };

        Mask {
            size: self.size,
            repr,
        }
    }
}

impl BitOrAssign for Mask {
    fn bitor_assign(&mut self, that: Mask) {
        let this = std::mem::replace(self, Mask::none(1));
        *self = this.bitor(that);
    }
}

impl<'a, 'b> Deref for Provers<'a, 'b> {
    type Target = [ProverSetItem<'a, 'b>];

    fn deref(&self) -> &Self::Target {
        &self.provers
    }
}

impl<'a, 'b> DerefMut for Provers<'a, 'b> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.provers
    }
}

impl<'a, 'b> Deref for ProverSetItem<'a, 'b> {
    type Target = WrappedProver<'a, 'b>;

    fn deref(&self) -> &Self::Target {
        &self.prover
    }
}

impl<'a, 'b> DerefMut for ProverSetItem<'a, 'b> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.prover
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
