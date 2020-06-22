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

/// A wrapper around the raw prover API that provides certain pieces of additional functionality,
/// namely: producing and storing temporary variables, defining and shadowing in-line, and
/// rebuilding with new requirements.
///
/// For definitions and shadowing, `proof::ScopedSimpleProver` provides methods that are *almost*
/// what is needed, but they only borrow the contents, which requires a persistent place to store
/// the values they reference. The referenced provers are stored here and the drop order is managed
/// by this type.
///
// TODO:
/// Rebuilding with new requirements *is* supported by the `SimpleProver` API, but was added after
/// this type was made; it has not been integrated here yet.
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

/// A wrapper type for maintaining multiple different sets of proofs at the same time
pub struct Provers<'a> {
    provers: Vec<ProverSetItem<'a>>,

    /// The mask on none, some, or all of the provers. This can be used to disable further proof
    /// after critical errors.
    pub mask: Mask,
}

/// A single item in a prover set.
///
/// These are created from a list of contracts at the top of a function, with an additional one
/// coming from the "base" prover - the one without any assumptions from contracts.
pub struct ProverSetItem<'a> {
    /// The inner prover. A better implementation might have grouped the internals of the
    /// `WrappedProver` into the outer `Provers` set, but it's not super serious (aside from a bit
    /// of inefficiency) - the tech debt isn't too severe, and the next version can take this into
    /// account.
    pub prover: WrappedProver<'a>,

    /// Any *extra* requirements the prover was given, due to the precondition of a contract
    ///
    /// The added `Node` provides the original source of the requirement, so that we can point back
    /// to it later.
    pub pre: &'a [Requirement<'a>],

    /// The source for the preconditions. This must be `Some(_)` if there are any pre-conditions,
    /// but having post-conditions does *not* necessarily imply this will exist
    pub pre_source: Option<Node<'a>>,

    /// Any requirements the prover must be able to show at the end of the function, given in terms
    /// of the function arguments and the return identifier `_`.
    pub post: &'a [Requirement<'a>],

    /// The source for post-conditions. This should be `Some(_)` if there are any post-conditions.
    pub post_source: Option<Node<'a>>,
}

/// A mask for disabling certain provers (but not others) when certain types of failure occur.
///
/// This is currently not used beyond the all/nothing dichotomy, but has support for selective
/// disabling, should that be decided in the future.
#[derive(Debug, Clone)]
pub struct Mask {
    /// The number of items (in this case, provers) in the set available for masking. This is used
    /// for converting between mask types.
    size: usize,
    repr: MaskType,
}

/// A way of representing common mask types in a small amount of space
#[derive(Debug, Clone)]
enum MaskType {
    /// All items masked, i.e. all are disabled
    All,
    /// None of the items are masked, i.e. all are enabled
    Nothing,
    /// Some items are masked and some are not. The vector records - for each item - whether it is
    /// masked (`true` = masked). The second value gives the number of indices not currently
    /// masked, which allows us to switch back to one of the other two simple cases when
    /// applicable.
    Mix(Vec<bool>, usize),
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
    /// Constructs a new `WrappedProver` from the list of requirements
    pub fn new(reqs: Vec<Requirement<'a>>) -> Self {
        Self {
            // It's okay to pass a reference here because the definition of `SimpleProver::new`
            // provides that the reference need not live as long as the type - so the prover
            // shouldn't access it beyond the end of the function call.
            prover: Some(InnerProver::new(&reqs)),
            reqs,
            dependent_provers: Vec::new(),
            temp_vars: Vec::new(),
            next_temp_id: 0,
        }
    }

    /// Attempts to prove the given requiremnt, substituting definitions as needed.
    pub fn prove(&self, req: &Requirement<'a>) -> ProofResult {
        self.prover.as_ref().unwrap().prove(req)
    }

    // TODO: We might want this to only use the conditions given as part of the proof for the
    // lemma. This should be decided on later, but the placeholder for now is the `_given`
    // argument.
    pub fn prove_lemma(&self, _given: &[Requirement<'a>], req: &Requirement<'a>) -> ProofResult {
        self.prover.as_ref().unwrap().prove_lemma(req)
    }

    /// Attempts to prove the given requirement, only substituting definitions in for the return
    /// identifier `_` as `ret_ident`.
    ///
    /// This allows the requirement on a return value to be given at the top of a function and
    /// checked with whatever definitions or added requirements may have been given during the
    /// course of the function body.
    pub fn prove_return(&self, req: &Requirement<'a>, ret_ident: Ident<'a>) -> ProofResult {
        use ScopedSimpleProver::{Defn, Root, Shadow};

        // Our plan here is to only expand the definitions for the return identifier, which we're
        // replacing. That allows us to keep the values separate.
        //
        // If part of the return value is shadowed, we'll just return that it was undetermined - in
        // practice this *should not* happen.

        let mut replacement = Expr::from(ret_ident);

        macro_rules! substitute {
            ($prover:expr) => {
                match $prover {
                    Root(_) => (),
                    Defn { x, expr, .. } => replacement = replacement.substitute(x, expr),
                    Shadow { x, .. } => {
                        if replacement.variables().contains(&x) {
                            // This probably shouldn't have happened, so we'll log a warning
                            eprintln!(
                                "warning: `prove_return` ended early from shadowed variable {}",
                                x.name
                            );
                            return ProofResult::Undetermined;
                        }
                    }
                }
            };
        }

        substitute!(self.prover.as_ref().unwrap());
        // We go through the dependent provers backwards because later indices provide
        // modifications *on top of* earlier indices - we need to apply them first.
        for p in self.dependent_provers.iter().rev() {
            substitute!(p.deref());
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

        // We extend the lifetime of `last_prover` because we know the data we're storing will be
        // valid later
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

        // We extend the lifetime of `last_prover` because we know the data we're storing will be
        // valid later
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
                    // It's okay to pass a reference here because the definition of
                    // `SimpleProver::new` provides that the reference need not live as long as the
                    // type - so the prover shouldn't access it beyond the end of the function
                    // call.
                    (Vec::new(), Prover::new(&base), base)
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

impl<'a> ProverSetItem<'a> {
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

impl<'a> Provers<'a> {
    pub fn new(items: Vec<ProverSetItem<'a>>) -> Self {
        assert!(!items.is_empty());

        Provers {
            mask: Mask::none(items.len()),
            provers: items,
        }
    }

    /// Returns whether the mask prevents some provers from running
    pub fn masks_some(&self) -> bool {
        self.mask.masks_some()
    }

    /// Returns the number of provers stored
    pub fn size(&self) -> usize {
        self.provers.len()
    }

    /// Attempts to prove the given requirements for all provers simultaneously, returning - for
    /// each prover *unmasked* prover - its index and all of the requirements that failed. Note
    /// that the provers will be given in order of their indices.
    ///
    /// If no requirements failed, the returned list will be empty.
    ///
    /// So: masked provers will not be present, successes will be given by an empty list, and
    /// failure is given by a list of the results and failing requirement.
    pub fn prove_all(
        &self,
        reqs: &[Requirement<'a>],
    ) -> Vec<(usize, Vec<(ProofResult, Requirement<'a>)>)> {
        self.provers
            .iter()
            .enumerate()
            .filter_map(|(i, p)| match self.mask.allows(i) {
                false => None,
                true => {
                    let res = reqs
                        .iter()
                        .filter_map(|req| match p.prove(req) {
                            ProofResult::True => None,
                            res @ _ => Some((res, req.clone())),
                        })
                        .collect();

                    Some((i, res))
                }
            })
            .collect()
    }

    /// Attempts to prove the given requirements for all provers simultaneously, returning - for
    /// each prover - its index and whether the requirements were all proven true.
    ///
    /// The mask allows individual provers to be ignored - their values will always be true.
    pub fn prove_all_passed(&self, reqs: &[Requirement<'a>]) -> Vec<(usize, bool)> {
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
    pub fn prove_lemma(
        &self,
        given: &[Requirement<'a>],
        reqs: &[Requirement<'a>],
    ) -> Vec<(usize, bool)> {
        self.provers
            .iter()
            .enumerate()
            .map(|(i, p)| match self.mask.allows(i) {
                true => (
                    i,
                    reqs.iter()
                        .all(|req| p.prove_lemma(given, req) == ProofResult::True),
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

    /// Returns whether the mask prevents some provers from running
    pub fn masks_some(&self) -> bool {
        match self.repr {
            MaskType::All | MaskType::Mix(_, _) => true,
            MaskType::Nothing => false,
        }
    }
}

impl<M> BitOr<M> for Mask
where
    Mask: BitOrAssign<M>,
{
    type Output = Mask;

    fn bitor(mut self, rhs: M) -> Mask {
        self.bitor_assign(rhs);
        self
    }
}

impl BitOrAssign<&'_ Mask> for Mask {
    fn bitor_assign(&mut self, that: &Mask) {
        use MaskType::{All, Mix, Nothing};

        let this = std::mem::replace(self, Mask::none(1));

        assert_eq!(this.size, that.size);

        let repr = match (this.repr, that.repr.clone()) {
            (Nothing, Nothing) => Nothing,
            (All, _) | (_, All) => All,
            (Mix(v, n), Nothing) | (Nothing, Mix(v, n)) => Mix(v, n),
            (Mix(xs, _), Mix(ys, _)) => {
                let v = xs
                    .into_iter()
                    .zip(ys.iter())
                    .map(|(x, &y)| x || y)
                    .collect::<Vec<_>>();
                let n = v.iter().filter(|&m| !m).count();

                match n {
                    0 => All,
                    _ => Mix(v, n),
                }
            }
        };

        *self = Mask { repr, ..this };
    }
}

impl BitOrAssign for Mask {
    fn bitor_assign(&mut self, that: Mask) {
        self.bitor_assign(&that);
    }
}

impl<'a> Deref for Provers<'a> {
    type Target = [ProverSetItem<'a>];

    fn deref(&self) -> &Self::Target {
        &self.provers
    }
}

impl<'a> DerefMut for Provers<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.provers
    }
}

impl<'a> Deref for ProverSetItem<'a> {
    type Target = WrappedProver<'a>;

    fn deref(&self) -> &Self::Target {
        &self.prover
    }
}

impl<'a> DerefMut for ProverSetItem<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.prover
    }
}
