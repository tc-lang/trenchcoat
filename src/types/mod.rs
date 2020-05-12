use crate::ast;

/// The kind of type expression
///
/// This is (currently) either a boolean or an integer, as those are the only two supported types.
#[derive(Debug, Clone)]
pub enum Type<'a> {
    /// A reference to a named type.
    /// These cannot be compared since they may be aliases so Named types should be resolved before
    /// verification.
    Named(&'a str),
    /// A distinct type is a user defined type.
    ///
    /// Two distinct types may have the same underlying type, for example:
    /// `type T int` and `type V int`,
    /// or `type T { a: int, b: bool }` and `type V { x: int, b: bool }`.
    /// In both cases, T and B have the same underlying types but, since they are not aliases, are
    /// not equal types.
    ///
    /// This is not yet fully supported.
    Distinct {
        /// The name given to the type. This will later be replaced with a stronger identifier
        /// which also includes source modules.
        name: &'a str,
    },
    /// A boolean
    Bool,
    /// An integer (architecture specific size)
    Int,
    /// An unsigned integer (architecture specific size)
    Uint,
    /// A struct consists of ordered fields.
    /// The field order is user defined (the order in which they list the fields).
    /// TODO Much later on, struct ordering will probably be done differently.
    Struct(Vec<StructField<'a>>),
}

/// Represents a field of a struct.
/// The typ field is a TypeExpr so to include source information. Equality checks between struct
/// fields do not compare the source and so 2 struct fields are equal iff they have the same name
/// and type.
#[derive(Debug, Clone)]
pub struct StructField<'a> {
    pub name: ast::Ident<'a>,
    pub type_expr: ast::TypeExpr<'a>,
}

impl<'a> PartialEq for Type<'a> {
    fn eq(&self, other: &Self) -> bool {
        use Type::*;

// So struct fields are equal iff they have the same name and type.
        if let Named(_) = other {
            panic!("cannot compare TypeExprKind::Named");
        }

        match self {
            Named(_) => panic!("cannot compare TypeExprKind::Named"),
            Bool => match other {
                Bool => true,
                _ => false,
            },
            Int => match other {
                Int => true,
                _ => false,
            },
            Uint => match other {
                Uint => true,
                _ => false,
            },
            Struct(fields) => match other {
                // TODO Note that the current implementation requires struct fields to be in the
                // same order for their structs to be equal. Details for struct equality will
                // have to be worked out when field ordering is decided. There are a couple of
                // valid approaches.
                Struct(other_fields) => other_fields == fields,
                _ => false,
            },
        }
    }
}

impl<'a> PartialEq for StructField<'a> {
    fn eq(&self, other: &Self) -> bool {
        // See the doc comment for StructField for the documentation of this comparison.
        self.name == other.name && self.type_expr.typ == other.type_expr.typ
    }
}

pub static empty_struct: Type = Type::Struct(Vec::new());
pub fn new_empty_struct<'a>() -> Type<'a> { Type::Struct(Vec::new()) }

