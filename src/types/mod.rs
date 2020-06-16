use crate::ast::Ident;
use std::fmt::{self, Display, Formatter};

/// The kind of type expression
///
/// This is (currently) either a boolean or an integer, as those are the only two supported types.
#[derive(Debug, Clone)]
pub enum Type<'a> {
    /// A reference to a named type.
    /// These cannot be compared since they may be aliases so Named types should be resolved before
    /// verification.
    Named(&'a str),

    /*
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
    */
    /// A boolean
    Bool,

    /// An integer (architecture specific size)
    Int,

    /// An unsigned integer (architecture specific size)
    UInt,

    /// A struct consists of ordered fields.
    ///
    /// The field order is user defined (the order in which they list the fields).
    /// TODO Much later on, struct ordering will probably be done differently.
    Struct(Vec<StructField<'a>>),

    /// For some reason, probably an error, the type is unknown.
    /// Note that unknown types are not equal to other unknown types.
    Unknown,
}

pub fn empty_struct<'a>() -> Type<'a> {
    Type::Struct(Vec::new())
}

pub fn field_type<'a, 'b: 'a>(fields: &'a [StructField<'b>], name: &str) -> Option<Type<'b>> {
    for field in fields {
        if field.name.name == name {
            return Some(field.typ.clone());
        }
    }
    None
}

/// Represents a field of a struct.
#[derive(Debug, Clone)]
pub struct StructField<'a> {
    pub name: Ident<'a>,
    pub typ: Type<'a>,
}

impl<'a> PartialEq for Type<'a> {
    fn eq(&self, other: &Self) -> bool {
        use Type::{Bool, Int, Named, Struct, UInt, Unknown};

        // So struct fields are equal iff they have the same name and type.
        if let Named(_) = other {
            panic!("cannot compare Type::Named");
        }

        match self {
            Named(_) => panic!("cannot compare Type::Named"),
            Bool => match other {
                Bool => true,
                _ => false,
            },
            Int => match other {
                Int => true,
                _ => false,
            },
            UInt => match other {
                UInt => true,
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
            // Unknown types aren't equal to other unknown types.
            Unknown => false,
        }
    }
}

impl<'a> PartialEq for StructField<'a> {
    fn eq(&self, other: &Self) -> bool {
        // See the doc comment for StructField for the documentation of this comparison.
        self.name.name == other.name.name && self.typ == other.typ
    }
}

impl Display for Type<'_> {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        use Type::{Bool, Int, Named, Struct, UInt, Unknown};

        match self {
            Named(s) => write!(fmt, "{}", s),
            Bool => write!(fmt, "bool"),
            Int => write!(fmt, "int"),
            UInt => write!(fmt, "uint"),
            Unknown => write!(fmt, "<unknown>"),
            Struct(fields) if fields.len() == 0 => write!(fmt, "{{}}"),
            Struct(fields) => {
                write!(fmt, "{{ {}: {}", fields[0].name, fields[0].typ)?;
                for f in fields[1..].iter() {
                    write!(fmt, ", {}: {}", f.name, f.typ)?;
                }
                write!(fmt, " }}")
            }
        }
    }
}
