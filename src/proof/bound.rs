use super::expr::Expr;

/// Represents a relation between 2 expressions.
/// For example: left <= (RelationKind::Le) right
///
/// This can be used to rearrange various relations to get particular bounds.
#[derive(Debug, Clone)]
pub struct Relation<'a> {
    pub left: Expr<'a>,
    pub relation: RelationKind,
    pub right: Expr<'a>,
}

/// A kind of a Relation
#[derive(Debug, Clone, Copy)]
pub enum RelationKind {
    /// Less than or equal to (<=)
    Le,
    /// Greater than or equal to (>=)
    Ge,
}
