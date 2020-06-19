pub trait Options: Clone {
    fn init() -> Self;
    /// Returns true if the optimiser should yield all bounds found - not just ones at final nodes.
    fn yield_all(&self) -> bool;
    fn better_sign_handling(&self) -> bool;
}

/// Standard mode - not too fast, not too slow. Can't prove many non-linear things.
#[derive(Clone)]
pub struct DefaultMode;

impl Options for DefaultMode {
    fn init() -> Self {
        Self
    }
    fn yield_all(&self) -> bool {
        false
    }
    fn better_sign_handling(&self) -> bool {
        #[cfg(feature = "better-sign-handling")]
        return true;
        false
    }
}

/// Mode for use in lemma proofs.
/// Enables `better_sign_handling` which allows non-linear proofs in many more cases but has a
/// significant cost.
#[derive(Clone)]
pub struct LemmaMode;

impl Options for LemmaMode {
    fn init() -> Self {
        Self
    }
    fn yield_all(&self) -> bool {
        false
    }
    fn better_sign_handling(&self) -> bool {
        true
    }
}

/// Mode for generating help suggestions. It behaves the same as DefaultMode except for the fact it
/// enables `yield_all` so the optimiser iterator will yield all expressions as opposed to only
/// when no more substitutions can be made.
#[derive(Clone)]
pub struct HelpMode;

impl Options for HelpMode {
    fn init() -> Self {
        Self
    }
    fn yield_all(&self) -> bool {
        true
    }
    fn better_sign_handling(&self) -> bool {
        false
    }
}
