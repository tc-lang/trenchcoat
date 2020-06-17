pub trait Options {
    /// Returns true if the optimiser should yield all bounds found - not just ones at final nodes.
    fn yield_all(&self) -> bool;
}

pub struct DefaultOptions;

impl Options for DefaultOptions {
    fn yield_all(&self) -> bool {
        false
    }
}

pub struct HelpMode;

impl Options for HelpMode {
    fn yield_all(&self) -> bool {
        true
    }
}
