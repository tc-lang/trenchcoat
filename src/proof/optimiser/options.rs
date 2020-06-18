pub trait Options: Clone {
    fn init() -> Self;
    /// Returns true if the optimiser should yield all bounds found - not just ones at final nodes.
    fn yield_all(&self) -> bool;
    fn better_sign_handling(&self) -> bool;
}

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
        false
    }
}

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
