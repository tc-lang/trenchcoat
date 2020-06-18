pub trait Options: Clone {
    fn init() -> Self;
    /// Returns true if the optimiser should yield all bounds found - not just ones at final nodes.
    fn yield_all(&self) -> bool;
}

#[derive(Clone)]
pub struct DefaultOptions;

impl Options for DefaultOptions {
    fn init() -> Self {
        Self
    }

    fn yield_all(&self) -> bool {
        false
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
}
