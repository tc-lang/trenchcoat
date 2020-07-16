//! This is a temp module for generating readable AST strings.

use super::{
    expr::{Expr, ExprKind, Struct},
    pat::{Pat, PatKind},
    prelude::*,
    stmt::{Stmt, StmtKind},
    types::{GenericArgs, NamedField, Type, TypeKind},
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
                decl.name, intersperse(&decl.params, ", "), decl.ret_typ.readable(), decl.body.readable(),
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
        TypeKind::Name{name, args} => {
            name.readable() + &args.readable()
        },
        TypeKind::Struct { unnamed_fields, named_fields, ordered } => {
            let mut s = String::with_capacity(32);
            match ordered {
                true => s.push_str("( "),
                false => s.push_str("{ "),
            }
            s.push_str(&intersperse(&unnamed_fields, ", "));
            if named_fields.len() != 0 {
                s.push_str(", ");
                s.push_str(&intersperse(&named_fields, ", "));
            }
            match ordered {
                true => s.push_str(")"),
                false => s.push_str("}"),
            }
            s
        },
        TypeKind::Ommited => "_".to_string(),

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
        ExprKind::Match { expr, arms } => {
            let mut s = format!("match ({}) ", expr.readable());
            s.push_str("{\n");
            for arm in arms {
                s.push_str(&format!("{} => ({})\n", arm.0.readable(), arm.1.readable()));
            }
            s.push_str("}");
            s
        },
        ExprKind::FnCall { func, arguments } => {
            format!("({})({})", func.readable(), arguments.readable())
        },
        ExprKind::CurlyFnCall { func, arguments } => {
            format!("({}){{{}}}", func.readable(), arguments.readable())
        },
        ExprKind::Index { expr, index } => {
            format!("({})[{}]", expr.readable(), index.readable())
        },
        ExprKind::If { condition, block, else_block } => {
            match else_block {
                Some(else_block) => format!("if {} {} else {}", condition.readable(), block.readable(), else_block.readable()),
                None => format!("if {} {}", condition.readable(), block.readable()),
            }
        },
        ExprKind::Closure { params, ret_typ, body } => {
            format!("({}) -> {} => ({})", intersperse(params, ", "), ret_typ.readable(), body.readable())
        },
        ExprKind::Empty => "EMPTY".to_string(),

        _ => todo!(),
    }
);

impl<'a> Readable for Struct<'a> {
    fn readable(&self) -> String {
        let mut s = String::with_capacity(64);
        s.push_str(&intersperse(&self.unnamed_fields, ", "));
        if self.named_fields.len() != 0 {
            s.push_str(", ");
            s.push_str(&intersperse(&self.named_fields, ", "));
        }
        s
    }
}

impl<'a> Readable for NamedField<'a> {
    fn readable(&self) -> String {
        format!("{}: {}", self.name, self.typ.readable())
    }
}

impl<'a> Readable for GenericArgs<'a> {
    fn readable(&self) -> String {
        if self.named.len() != 0 {
            todo!();
        }
        if self.unnamed.len() == 0 {
            return String::new();
        }
        format!("<{}>", intersperse(&self.unnamed, ", "))
    }
}

impl<'a> Readable for Vec<Item<'a>> {
    fn readable(&self) -> String {
        intersperse(self, "\n\n")
    }
}

impl<T: Readable, U: Readable> Readable for (T, U) {
    fn readable(&self) -> String {
        format!("{}: {}", self.0.readable(), self.1.readable())
    }
}

impl Readable for &str {
    fn readable(&self) -> String {
        self.to_string()
    }
}

fn intersperse<T: Readable>(items: &[T], sep: &str) -> String {
    if items.len() == 0 {
        return String::new();
    }
    let mut s = String::with_capacity(8 * items.len());
    for i in 0..items.len() - 1 {
        s.push_str(&items[i].readable());
        s.push_str(sep);
    }
    s.push_str(&items[items.len() - 1].readable());
    s
}
