//! This is a temp module for generating readable AST strings.

use super::{
    expr::{Expr, ExprKind, Struct},
    pat::{Pat, PatKind},
    prelude::*,
    stmt::{Stmt, StmtKind},
    types::{NamedField, Type, TypeKind},
    Item, ItemKind,
};

pub trait Readable {
    fn readable(&self) -> String;
}

macro_rules! impls {
    (
        $(
            impl Readable for $type:ident, $type_kind:ident {
                $($pat:pat => $expr:expr),* $(,)?
            }
        )*
    ) => {
        $(
            impl<'a> Readable for $type<'a> {
                fn readable(&self) -> String {
                    self.kind.readable()
                }
            }
            impl<'a> Readable for $type_kind<'a> {
                fn readable(&self) -> String {
                    match self {
                        $($pat => $expr),*
                    }
                }
            }
        )*
    };
}

impls!(
    impl Readable for Pat, PatKind {
        PatKind::Ident(ident) => ident.to_string(),
    }

    impl Readable for Stmt, StmtKind {
        StmtKind::Expr(expr) => expr.readable(),
        StmtKind::Assign { target, expr, pointer } => match pointer {
            false => format!("{} = ({})", target, expr.readable()),
            true => format!("*{} = ({})", target, expr.readable()),
        },
    }

    impl Readable for Item, ItemKind {
        ItemKind::Fn(decl) => {
            format!(
                "fn {}({}) -> {} {}",
                decl.name, decl.params.readable(), decl.ret_typ.readable(), decl.body.readable(),
            )
        },
        ItemKind::Type(decl) => {
            match decl.alias {
                false => format!("type {} {}", decl.name, decl.typ.readable()),
                true => format!("type {} alias {}", decl.name, decl.typ.readable()),
            }
        },

        _ => todo!(),
    }

    impl Readable for Type, TypeKind {
        TypeKind::Name(name) => name.to_string(),
        TypeKind::Struct { unnamed_fields, named_fields, ordered } => {
            let mut s = String::with_capacity(32);
            match ordered {
                true => s.push_str("( "),
                false => s.push_str("{ "),
            }
            for field in unnamed_fields {
                s.push_str(&field.readable());
                s.push_str(", ");
            }
            s.push_str(&named_fields.readable());
            match ordered {
                true => s.push_str(")"),
                false => s.push_str("}"),
            }
            s
        },

        _ => todo!(),
    }

    impl Readable for Expr, ExprKind {
        ExprKind::Name(name) => name.to_string(),
        ExprKind::RawLiteral(src, kind) => format!("{:?}({})", kind, src),
        ExprKind::PrefixOp { op, expr } => format!("<{:?}>({})", op, expr.readable()),
        ExprKind::PostfixOp { expr, op } => format!("({})<{:?}>", expr.readable(), op),
        ExprKind::BinaryOp { lhs, op, rhs } => format!("({})<{:?}>({})", lhs.readable(), op, rhs.readable()),
        ExprKind::Let { pat, expr } => format!("<let {} = {}>", pat.readable(), expr.readable()),
        ExprKind::Block { stmts, delim } => {
            let mut s = String::with_capacity(64);
            match delim {
                Delim::Curlies => s.push_str("{\n"),
                Delim::Parens => s.push_str("(\n"),
                Delim::Squares => s.push_str("[\n"),
            }
            for stmt in stmts {
                s.push_str(&stmt.readable());
                s.push_str(";\n");
            }
            match delim {
                Delim::Curlies => s.push_str("}"),
                Delim::Parens => s.push_str(")"),
                Delim::Squares => s.push_str("]"),
            }
            s
        },
        ExprKind::BlockOrStruct { ident, delim } => {
            let mut s = String::with_capacity(64);
            match delim {
                Delim::Curlies => s.push_str("{ "),
                Delim::Parens => s.push_str("( "),
                Delim::Squares => s.push_str("[ "),
            }
            s.push_str(ident);
            match delim {
                Delim::Curlies => s.push_str(" }"),
                Delim::Parens => s.push_str(" )"),
                Delim::Squares => s.push_str(" ]"),
            }
            s
        },
        ExprKind::Struct { fields, delim } => {
            let mut s = String::with_capacity(64);
            match delim {
                Delim::Curlies => s.push_str("{ "),
                Delim::Parens => s.push_str("( "),
                Delim::Squares => s.push_str("[ "),
            }
            s.push_str(&fields.readable());
            match delim {
                Delim::Curlies => s.push_str("}"),
                Delim::Parens => s.push_str(")"),
                Delim::Squares => s.push_str("]"),
            }
            s
        },
        ExprKind::FnCall { func, arguments } => {
            format!("({})({})", func.readable(), arguments.readable())
        },
        ExprKind::Index { expr, index } => {
            format!("({})[{}]", expr.readable(), index.readable())
        },
        ExprKind::If { condition, block, else_block } => {
            match else_block {
                Some(else_block) => format!("if {} {} {}", condition.readable(), block.readable(), else_block.readable()),
                None => format!("if {} {}", condition.readable(), block.readable()),
            }
        },
        ExprKind::Empty => "EMPTY".to_string(),

        _ => todo!(),
    }
);

impl<'a> Readable for Struct<'a> {
    fn readable(&self) -> String {
        let mut s = String::with_capacity(64);
        for field in self.unnamed_fields.iter() {
            s.push_str(&field.readable());
            s.push_str(", ");
        }
        for field in self.named_fields.iter() {
            s.push_str(&format!("{}: {}, ", field.0, field.1.readable()));
        }
        s
    }
}

impl<'a> Readable for NamedField<'a> {
    fn readable(&self) -> String {
        format!("{}: {}, ", self.name, self.typ.readable())
    }
}

impl<'a> Readable for Vec<NamedField<'a>> {
    fn readable(&self) -> String {
        let mut s = String::with_capacity(32);
        for field in self {
            s.push_str(&field.readable());
        }
        s
    }
}

impl<'a> Readable for Vec<Item<'a>> {
    fn readable(&self) -> String {
        let mut s = String::with_capacity(4096);
        for item in self {
            s.push_str(&item.readable());
            s.push_str("\n\n");
        }
        s
    }
}
