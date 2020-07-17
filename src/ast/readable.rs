//! This is a temp module for generating readable AST strings.

use super::{
    expr::{Expr, ExprKind, Struct},
    pat::{Pat, PatKind},
    prelude::*,
    stmt::{Stmt, StmtKind},
    types::{
        GenericArgs, GenericParam, GenericParamKind, NamedField, Trait, TraitKind, Type, TypeKind,
    },
    Item, ItemKind,
};

use std::fmt::{Display, Error, Formatter, Result};
use std::ops::Deref;

fn intersperse<'a, T: Display, S: Display>(items: &'a [T], sep: S) -> Intersperse<'a, T, S> {
    Intersperse::new(items, sep)
}

macro_rules! impls {
    (
        $(
            impl Display for $type:ident, $type_kind:ident {
                fn fmt(&self, $f:ident) -> Result {
                    $($pat:pat => $expr:expr),* $(,)?
                }
            }
        )*
    ) => {
        $(
            impl<'a> Display for $type<'a> {
                fn fmt(&self, $f: &mut Formatter) -> Result {
                    self.kind.fmt($f)
                }
            }
            impl<'a> Display for $type_kind<'a> {
                fn fmt(&self, $f: &mut Formatter) -> Result {
                    match self {
                        $($pat => $expr),*
                    }
                }
            }
        )*
    };
}

impls!(
    impl Display for Pat, PatKind {
        fn fmt(&self, f) -> Result {
            PatKind::Ident(ident) => f.write_str(ident),
        }
    }

    impl Display for Stmt, StmtKind {
        fn fmt(&self, f) -> Result {
            StmtKind::Expr(expr) => expr.fmt(f),
            StmtKind::Assign { target, expr, pointer } => match pointer {
                false => write!(f, "{} = ({})", target, expr),
                true => write!(f, "*{} = ({})", target, expr),
            },
        }
    }

    impl Display for Item, ItemKind {
        fn fmt(&self, f) -> Result {
            ItemKind::Fn(decl) => {
                write!(
                    f,
                    "fn {name}({params}) -> {ret_typ} {body}",
                    name = decl.name,
                    params = intersperse(&decl.params, ", "),
                    ret_typ = decl.ret_typ,
                    body = decl.body,
                )
            },
            ItemKind::Type(decl) => {
                match decl.alias {
                    false => write!(f, "type {}<{}> {}", decl.name, intersperse(&decl.params, ", "), decl.typ),
                    true => write!(f, "type {}<{}> alias {}", decl.name, intersperse(&decl.params, ", "), decl.typ),
                }
            },

            _ => todo!(),
        }
    }

    impl Display for Type, TypeKind {
        fn fmt(&self, f) -> Result {
            TypeKind::Name{name, args} => {
                write!(f, "{}{}", name, args)
            },
            TypeKind::Struct { unnamed_fields, named_fields, ordered } => {
                match ordered {
                    true => f.write_str("( ")?,
                    false => f.write_str("{ ")?,
                }
                intersperse(&unnamed_fields, ", ").fmt(f)?;
                if named_fields.len() != 0 {
                    if unnamed_fields.len() != 0 {
                        f.write_str(", ")?;
                    }
                    intersperse(&named_fields, ", ").fmt(f)?;
                }
                match ordered {
                    true => f.write_str(" )"),
                    false => f.write_str(" }"),
                }
            },
            TypeKind::Ommited => write!(f, "_"),

            _ => todo!(),
        }
    }

    impl Display for Trait, TraitKind {
        fn fmt(&self, f) -> Result {
            TraitKind::Name{name, path, args} => {
                if path.len() != 0 {
                    todo!();
                }
                write!(f, "{}{}", name, args)
            },
        }
    }

    impl Display for Expr, ExprKind {
        fn fmt(&self, f) -> Result {
            ExprKind::Name(name) => f.write_str(&name),
            ExprKind::Type { name, generic_args } => write!(f, "{}~{}", name, generic_args),
            ExprKind::TypeHint { expr, typ } => write!(f, "{} ~ {}", expr, typ),
            ExprKind::RawLiteral(src, kind) => write!(f, "{:?}({})", kind, src),
            ExprKind::PrefixOp { op, expr } => write!(f, "<{:?}>({})", op, expr),
            ExprKind::PostfixOp { expr, op } => write!(f, "({})<{:?}>", expr, op),
            ExprKind::BinaryOp { lhs, op, rhs } => write!(f, "({})<{:?}>({})", lhs, op, rhs),
            ExprKind::Let { pat, expr } => write!(f, "<let {} = {}>", pat, expr),
            ExprKind::Block { stmts, delim } => {
                match delim {
                    Delim::Curlies => f.write_str("{\n")?,
                    Delim::Parens => f.write_str("(\n")?,
                    Delim::Squares => f.write_str("[\n")?,
                }
                for stmt in stmts {
                    write!(f, "{};\n", stmt)?;
                }
                match delim {
                    Delim::Curlies => f.write_str("}"),
                    Delim::Parens => f.write_str(")"),
                    Delim::Squares => f.write_str("]"),
                }
            },
            ExprKind::BlockOrStruct { ident, delim } => {
                match delim {
                    Delim::Curlies => f.write_str("{ <ambiguous> ")?,
                    Delim::Parens => f.write_str("( <ambiguous> ")?,
                    Delim::Squares => f.write_str("[ <ambiguous> ")?,
                }
                f.write_str(ident)?;
                match delim {
                    Delim::Curlies => f.write_str(" }"),
                    Delim::Parens => f.write_str(" )"),
                    Delim::Squares => f.write_str(" ]"),
                }
            },
            ExprKind::Struct { fields, delim } => {
                match delim {
                    Delim::Curlies => f.write_str("{ ")?,
                    Delim::Parens => f.write_str("( ")?,
                    Delim::Squares => f.write_str("[ ")?,
                }
                write!(f, "{}", fields)?;
                match delim {
                    Delim::Curlies => f.write_str(" }"),
                    Delim::Parens => f.write_str(" )"),
                    Delim::Squares => f.write_str(" ]"),
                }
            },
            ExprKind::Match { expr, arms } => {
                write!(f, "match ({}) {{\n", expr)?;
                for arm in arms {
                    write!(f, "{} => ({})\n", arm.0, arm.1)?;
                }
                f.write_str("}")
            },
            ExprKind::FnCall { func, arguments } => {
                write!(f, "({})({})", func, arguments)
            },
            ExprKind::CurlyFnCall { func, arguments } => {
                write!(f, "({}){{{}}}", func, arguments)
            },
            ExprKind::Index { expr, index } => {
                write!(f, "({})[{}]", expr, index)
            },
            ExprKind::If { condition, block, else_block } => {
                match else_block {
                    Some(else_block) => write!(f, "if {} {} else {}", condition, block, else_block),
                    None => write!(f, "if {} {}", condition, block),
                }
            },
            ExprKind::Closure { params, ret_typ, body } => {
                write!(f, "({}) -> {} => ({})", intersperse(params, ", "), ret_typ, body)
            },
            ExprKind::Empty => write!(f, "<EMPTY>"),

            _ => todo!(),
        }
    }
);

impl<'a> Display for Struct<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        intersperse(&self.unnamed_fields, ", ").fmt(f)?;
        if self.named_fields.len() != 0 {
            if self.unnamed_fields.len() != 0 {
                f.write_str(", ")?;
            }
            intersperse(
                unsafe { std::mem::transmute::<_, &[ExprNamedField]>(self.named_fields.deref()) },
                ", ",
            )
            .fmt(f)?;
        }
        Ok(())
    }
}

impl<'a> Display for NamedField<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}: {}", self.name, self.typ)
    }
}

struct ExprNamedField<'a>((&'a str, Expr<'a>));

impl<'a> Display for ExprNamedField<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}: {}", (self.0).1, (self.0).1)
    }
}

impl<'a> Display for GenericArgs<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        if self.named.len() != 0 {
            todo!();
        }
        if self.unnamed.len() != 0 {
            write!(f, "<{}>", intersperse(&self.unnamed, ", "))?;
        }
        Ok(())
    }
}

impl<'a> Display for GenericParam<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match &self.kind {
            GenericParamKind::Type(typ) => write!(f, "{}: {}", self.name, typ),
            GenericParamKind::Trait(trt) => write!(f, "{} :: {}", self.name, trt),
        }
    }
}

pub(crate) struct FmtItems<'a>(pub(crate) Vec<Item<'a>>);

impl<'a> Display for FmtItems<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        intersperse(&self.0, "\n\n").fmt(f)
    }
}

struct Intersperse<'a, T: Display, S: Display> {
    items: &'a [T],
    sep: S,
}

impl<'a, T: Display, S: Display> Intersperse<'a, T, S> {
    fn new(items: &'a [T], sep: S) -> Self {
        Self { items, sep }
    }
}

impl<'a, T: Display, S: Display> Display for Intersperse<'a, T, S> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        if self.items.len() == 0 {
            return Ok(());
        }
        for i in 0..self.items.len() - 1 {
            self.items[i].fmt(f)?;
            self.sep.fmt(f)?;
        }
        self.items[self.items.len() - 1].fmt(f)
    }
}
