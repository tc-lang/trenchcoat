use std::collections::HashMap;

use crate::ast;
use crate::types::{self, Type};
pub mod error;
use error::Error;

// Here, I'm using "item" to refer to things that exist in the language, for example variables,
// function and soon types. Please change the name item to something better.
//
// During verification, every kind of item is represented by a struct containing the required
// information.
//
// Then, a scope consists of a map from identifiers to items.
// Currently there are 2 types of scope, `TopLevelScope` and `Scope`. These will soon just be one
// however are separated for now to keep things simple as each kind of scope can only contain 1
// kind of item (hence no need for an item enum yet).

pub fn verify<'a>(items: &'a [ast::Item<'a>]) -> Vec<Error<'a>> {
    let (top_level, mut errors) = TopLevelScope::build(items);
    let more_errors = top_level.check_items(items);
    errors.extend(more_errors);
    errors
}

/// Represents a function. Currently, all we need for verification is the number of parameters.
/// This will likely grow to include type and proof information for each parameter along with the
/// return type.
#[derive(Debug, Clone)]
struct Func<'a> {
    /// the number of parameters, when types are introduced this will likely be replaced with a
    /// list of type information for each parameter.
    params: Vec<&'a ast::TypeExpr<'a>>,
    ret: &'a ast::TypeExpr<'a>,
}

/// Currently variables are all isize so no information is required!
#[derive(Debug, Clone)]
struct Variable<'a, 'b: 'a> {
    typ: &'b Type<'a>,
}

/// The top level scope consists of named items, currently just functions. Things will be
/// transitioned out of here as they can be placed in local scopes until everything is under
/// the `Scope` type. It exists now for simplicity.
#[derive(Debug, Clone)]
struct TopLevelScope<'a> {
    map: HashMap<&'a str, TopLevelItem<'a>>,
}

/// Represents an item in the top level scope. Currently this is always a function.
#[derive(Debug, Clone)]
struct TopLevelItem<'a> {
    func: Func<'a>,
    source: &'a ast::Item<'a>,
}

/// Represents a lexical scope. These usually contain ScopeItems which are named variables.
/// They may also have an optional parent which getting names can bubble up to.
/// All `Scopes` are within a `TopLevelScope` context to resolve global names such as functions.
#[derive(Debug, Clone)]
struct Scope<'a, 'b: 'a> {
    item: Option<ScopeItem<'a, 'b>>,
    parent: Option<&'a Scope<'a, 'b>>,
    top_level: &'a TopLevelScope<'b>,
}

#[derive(Debug, Clone)]
struct ScopeItem<'a, 'b: 'a> {
    name: &'a str,
    variable: Variable<'a, 'b>,
    source: Option<ast::Node<'a>>,
}

/*impl<'a> ast::Expr<'a> {
    fn type_check(&self, scope: &'a Scope<'a>) -> Vec<Error<'a>> {
        use ast::ExprKind::*;
        match &self.kind {
            // The following expression kinds cannot have type errors
            Empty | Named(_) | Num(_) => Vec::new(),

            // Hand the type checking down
            Bracket(block) => block.type_check(),

            FnCall(f, args) => {
                let mut errors = Vec::new();

                // First type check each argument.
                for arg in args {
                    errors.extend(arg.type_check(scope));
                }

                let f_name = match &f.kind {
                    Named(f_ident) => f_ident.name,
                    _ => return errors, // this error will be raised elsewhere
                };
                let f = match scope.get_fn(f_name) {
                    Some(f) => f,
                    None => return errors, // again, this has already been raised
                };

                if args.len() != f.params.len() {
                    return errors;
                }

                // Then, check that each argument has the correct type.
            },
        }
    }
    /// returns the Type which the expression evaluates to
    fn typ(&self, scope: &'a Scope<'a>) -> &'a Type<'a> {
        use ast::ExprKind::*;
        match &self.kind {
            Empty => &types::empty_struct,
            Named(ident) => &scope.get(ident.name).unwrap().variable.typ,
            BinOp(_, _, _) => &ast::TypeExprKind::Int,
            PrefixOp(_, _) => &ast::TypeExprKind::Int,
            Num(_) => &ast::TypeExprKind::Int,
            Bracket(block) => block.tail.type_kind(scope),
            FnCall(f, _) => match &f.kind {
                Named(f_name) => &scope.get_fn(f_name.name).unwrap().ret.typ,
                _ => panic!("can only call named expression"),
                // ^ this should have been checked already
            },
        }
    }
}*/

impl<'a, 'b: 'a> TopLevelScope<'b> {
    /// Takes a slice of top-level items and builds a `TopLevelScope` from them.
    /// It does not verify the items as this should be done after the scope is fully constructed.
    fn build(items: &'b [ast::Item<'b>]) -> (TopLevelScope<'a>, Vec<Error<'b>>) {
        let mut out = TopLevelScope {
            map: HashMap::with_capacity(items.len()),
        };
        let mut errors = Vec::new();

        for item in items {
            match &item.kind {
                ast::ItemKind::FnDecl {
                    name,
                    params,
                    ret,
                    body: _,
                } => {
                    if let Some(conflict) = out.map.insert(
                        name.name,
                        TopLevelItem {
                            func: Func {
                                params: params.iter().map(|param| &param.1).collect(),
                                ret,
                            },
                            source: item,
                        },
                    ) {
                        errors.push(Error {
                            kind: error::Kind::ItemConflict(conflict.source, item),
                            context: error::Context::TopLevel,
                            source: item.node(),
                        });
                    }
                }
            }
        }

        (out, errors)
    }

    fn check_item(&'a self, item: &'b ast::ItemKind<'b>) -> Vec<Error<'b>> {
        match item {
            ast::ItemKind::FnDecl {
                name: _,
                params,
                ret,
                body,
            } => self.check_fn(params, ret, body),
        }
    }

    fn check_items(&'a self, items: &'b [ast::Item<'b>]) -> Vec<Error<'b>> {
        let mut errors = Vec::new();
        for item in items {
            errors.extend(self.check_item(&item.kind));
        }
        errors
    }

    /// Given a TopLevelScope, check_fn checks the body of the function and returns any errors.
    fn check_fn(
        &'a self,
        params: &'b ast::FnParams<'b>,
        ret: &'b ast::TypeExpr<'b>,
        block: &'b ast::Block<'b>,
    ) -> Vec<Error<'b>> {
        // Create a scope containing all the function arguments.
        let check_block = if params.is_empty() {
            // If there aren't any, then this is just an empty scope.
            let empty = Scope {
                item: None,
                parent: None,
                top_level: self,
            };
            empty.check_block(block, 0)
        } else {
            // We'll now create a scope for each parameter.
            // Using the notation `parent <- child`, this will create the structure:
            //  Scope{ param0 } <- Scope{ param1 } <- Scope{ param2 } <- ...

            // First, we'll create each of the scopes without parents.
            // It's a shame we can't do this on the stack :(
            let scopes = params
                .iter()
                .map(|param| Scope {
                    item: Some(ScopeItem {
                        name: param.0.name,
                        variable: Variable { typ: &param.1.typ },
                        source: Some(param.0.node()),
                    }),
                    parent: None,
                    top_level: self,
                })
                .collect::<Vec<_>>();

            // Then, we'll link each scope to it's parent. So the scope for param n gets a parent
            // of the scope for param n-1.

            // This is down here rather than in the main loop to isolate the unsafe.
            // Using unsafe along with push seemed risky because although we know, when writing
            // this, that the vec won't need to exapand and reallocate, it seems risky since
            // someone could easily make a change that without thinking about this.
            for i in 1..scopes.len() {
                let parent = scopes.get(i - 1).map(|x| unsafe { &*(x as *const Scope) });
                scopes[i].parent = parent;
            }
            ///// !!!!!!!!!!!!!!! DO NOT CHANGE `scopes` AFTER THIS UNSAFE !!!!!!!!!!!!!!! /////

            scopes.last().unwrap().check_block(block, 0)
        };

        //let (mut errors, tail_type) = fn_scope.check_block(block, 0);
        let (mut errors, tail_type) = check_block;

        if *tail_type != ret.typ {
            errors.push(Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![ret.typ],
                    found: *tail_type,
                },
                context: error::Context::FnTail,
                source: block.tail.node(),
            })
        }

        errors
    }
}

impl<'a, 'b: 'a> Scope<'a, 'b> {
    /// Creates a new scope containing the given item with the given parent.
    /// The TopLevelScope is inherited from `parent`.
    fn new(item: ScopeItem<'a, 'b>, parent: &'a Scope<'a, 'b>) -> Scope<'a, 'b> {
        Scope {
            item: Some(item),
            parent: Some(parent),
            top_level: parent.top_level,
        }
    }
    /// Creates a new empty scope - with no item and no parent.
    fn empty(top_level: &'a TopLevelScope<'a>) -> Scope<'a, 'b> {
        Scope {
            item: None,
            parent: None,
            top_level,
        }
    }

    /// Creates a new scope, a child of `self`, containing `item`.
    fn child(&'a self, item: ScopeItem<'a, 'b>) -> Scope<'a, 'b> {
        Self::new(item, self)
    }

    /// Finds a scope item with the given name. This bubbles up to parent scopes.
    fn get(&self, name: &str) -> Option<&ScopeItem<'a, 'b>> {
        if let Some(item) = &self.item {
            if item.name == name {
                return Some(item);
            }
        }
        self.parent.and_then(|scope| scope.get(name))
    }

    /// Finds a function with the given name. This only checks the top level scope.
    fn get_fn(&self, name: &str) -> Option<&Func<'a>> {
        Some(&self.top_level.map.get(name)?.func)
    }

    fn same_type_check(
        left: &'a Type<'b>,
        left_source: ast::Node<'b>,
        right: &'a Type<'b>,
        right_source: ast::Node<'b>,
    ) -> Vec<Error<'b>> {
        if *right == *left {
            Vec::new()
        } else {
            vec![Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![*left],
                    found: *right,
                },
                context: error::Context::BinOpTypeCheck,
                source: right_source,
            }]
        }
    }

    fn integer_check(t: &'a Type<'b>, source: ast::Node<'b>) -> Vec<Error<'b>> {
        // The left operand must be an integer type
        if *t == Type::Int || *t == Type::Uint {
            Vec::new()
        } else {
            vec![Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![Type::Int, Type::Uint],
                    found: *t,
                },
                context: error::Context::BinOpTypeCheck,
                source: source,
            }]
        }
    }

    fn bool_check(t: &Type<'b>, source: ast::Node<'b>) -> Vec<Error<'b>> {
        match t {
            Type::Bool => Vec::new(),
            _ => vec![Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![Type::Bool],
                    found: *t,
                },
                context: error::Context::BinOpTypeCheck,
                source: source,
            }],
        }
    }
    /// Type check a binary operator expression and return it's final type.
    ///
    /// At the moment, this is very simple. It checks that the first operand has a compatable type,
    /// for example that the first operand to + is either an `int` or a `uint`.
    /// It then checks that the second operand is of the same type as the first operand. This is
    /// required of all binary operators at the moment.
    ///
    /// The type returned is dependent on the operator and the operands. For example, the type of
    /// `a == b` is always `Type::Bool` whereas the type of `a + b` is the type of `a`.
    fn bin_op_types(
        op: &'b ast::BinOp,
        left: &'a Type<'b>,
        left_source: ast::Node<'b>,
        right: &'a Type<'b>,
        right_source: ast::Node<'b>,
    ) -> (Vec<Error<'b>>, &'a Type<'b>) {
        use ast::BinOp::*;

        let mut errors: Vec<Error<'b>> = Vec::new();
        let output_type;

        match op {
            // Boolean to Boolean operators
            Or | And => {
                errors.extend(Scope::bool_check(left, left_source));
                output_type = &Type::Bool;
            }
            // T x T => Boolean type operators
            Eq => output_type = &Type::Bool,
            // Integer x Integer -> Integer operators
            Add | Sub | Mul | Div => {
                errors.extend(Scope::integer_check(left, left_source));
                output_type = left;
            }
            // Integer x Integer -> Boolean operators
            Lt | Le | Gt | Ge => {
                errors.extend(Scope::integer_check(left, left_source));
                output_type = &Type::Bool;
            }
        }

        // Check that the right operand has the same type as the left operand.
        errors.extend(Scope::same_type_check(
            left,
            left_source,
            right,
            right_source,
        ));

        (errors, output_type)
    }
    fn prefix_op_types(
        op: &'b ast::PrefixOp,
        t: &'a Type<'b>,
        source: ast::Node<'b>,
    ) -> (Vec<Error<'b>>, &'a Type<'b>) {
        use ast::PrefixOp::*;

        let mut errors = Vec::new();
        let output_type;

        match op {
            // Boolean -> Boolean operators
            Not => {
                errors.extend(Scope::bool_check(t, source));
                output_type = &Type::Bool;
            }
        }

        (errors, output_type)
    }

    /// Returns any errors and the type of the given expression when evaluated in this scope.
    fn check_expr(&'a self, expr: &'b ast::Expr<'b>) -> (Vec<Error<'b>>, &'a Type<'b>) {
        match &expr.kind {
            ast::ExprKind::BinOp(left, op, right) => {
                let (mut errors, left_type) = self.check_expr(left);
                let (right_errors, right_type) = self.check_expr(right);
                errors.extend(right_errors);
                let (op_errors, final_type) =
                    Self::bin_op_types(op, left_type, left.node(), right_type, right.node());
                errors.extend(op_errors);
                (errors, final_type)
            }
            ast::ExprKind::PrefixOp(op, inner_expr) => {
                let (mut errors, expr_type) = self.check_expr(inner_expr);
                let (op_errors, final_type) =
                    Self::prefix_op_types(op, expr_type, inner_expr.node());
                errors.extend(op_errors);
                (errors, final_type)
            }
            ast::ExprKind::Num(_) => (Vec::new(), &Type::Int), // Woo! No errors here!
            // (Overflows will be handled when the int is
            //  parsed? If the interpreter is going to parse
            //  from the AST then we can validate here for
            //  now.)
            ast::ExprKind::Bracket(block) => self.check_block(&block, 0),
            ast::ExprKind::Named(name) => match self.get(name.name) {
                Some(item) => (Vec::new(), item.variable.typ),
                None => (
                    vec![Error {
                        kind: error::Kind::VariableNotFound,
                        context: error::Context::Expr,
                        source: expr.node(),
                    }],
                    // TODO Maybe we add a special `Unknown` type which this generates.
                    // Then, when a type error occurs, it would not be raised since this error
                    // would have already happened.
                    &types::empty_struct,
                ),
            },
            ast::ExprKind::FnCall(fn_expr, args) => {
                let name = match &fn_expr.kind {
                    ast::ExprKind::Named(name) => name.name,
                    _ => {
                        return (
                            vec![Error {
                                kind: error::Kind::FunctionMustBeName,
                                context: error::Context::Expr,
                                source: fn_expr.node(),
                            }],
                            &types::empty_struct,
                        )
                    }
                };

                let func = match self.get_fn(name) {
                    Some(f) => f,
                    None => {
                        return (
                            vec![Error {
                                kind: error::Kind::FunctionNotFound,
                                context: error::Context::Expr,
                                source: fn_expr.node(),
                            }],
                            &types::empty_struct,
                        )
                    }
                };

                if func.params.len() != args.len() {
                    return (
                        vec![Error {
                            kind: error::Kind::IncorrectNumberOfArgs {
                                n_given: args.len(),
                                n_expected: func.params.len(),
                            },
                            context: error::Context::Expr,
                            source: ast::Node::Args(&args),
                        }],
                        &types::empty_struct,
                    );
                }

                let mut errors = Vec::new();
                for i in 0..args.len() {
                    let (arg_errors, arg_type) = self.check_expr(&args[i]);
                    errors.extend(arg_errors);
                    if *arg_type != func.params[i].typ {
                        errors.push(Error {
                            kind: error::Kind::TypeMismatch {
                                expected: vec![func.params[i].typ],
                                found: *arg_type,
                            },
                            context: error::Context::FnArg,
                            source: args[i].node(),
                        });
                    }
                }

                (errors, &func.ret.typ)
            }
            ast::ExprKind::Empty => (Vec::new(), &types::empty_struct),
        }
    }

    fn check_assign(
        &'a self,
        ident: &'b ast::Ident<'b>,
        expr: &'b ast::Expr<'b>,
    ) -> Vec<Error<'b>> {
        let mut errors = Vec::new();
        let (expr_errors, expr_type) = self.check_expr(&expr);
        errors.extend(expr_errors);
        match self.get(ident.name) {
            Some(item) => {
                if *item.variable.typ != *expr_type {
                    errors.push(Error {
                        kind: error::Kind::TypeMismatch {
                            expected: vec![*item.variable.typ],
                            found: *expr_type,
                        },
                        context: error::Context::Assign,
                        source: ident.node(),
                    })
                }
            }
            None => errors.push(Error {
                kind: error::Kind::VariableNotFound,
                context: error::Context::Assign,
                source: ident.node(),
            }),
        }
        errors
    }

    fn check_block(&self, block: &ast::Block<'b>, start: usize) -> (Vec<Error<'b>>, &Type<'b>) {
        let mut errors = Vec::new();

        // Check the statements from `start`
        for idx in start..block.body.len() {
            let stmt = &block.body[idx];
            match &stmt.kind {
                ast::StmtKind::Eval(expr) | ast::StmtKind::Print(expr) => {
                    let (expr_errors, _) = self.check_expr(&expr);
                    errors.extend(expr_errors);
                }

                ast::StmtKind::Assign(name, expr) => errors.extend(self.check_assign(name, expr)),

                ast::StmtKind::Let(name, expr) => {
                    let (expr_errors, typ) = self.check_expr(&expr);
                    errors.extend(expr_errors);

                    let new_scope = self.child(ScopeItem {
                        name: name.name,
                        variable: Variable { typ },
                        source: Some(stmt.node()),
                    });

                    // Check the remainder of this block with the new scope, then return.
                    let (other_errors, block_type) = new_scope.check_block(block, idx + 1);
                    errors.extend(other_errors);

                    return (errors, block_type);
                }
            }
        }

        let (tail_errors, tail_type) = self.check_expr(&block.tail);
        errors.extend(tail_errors);

        (errors, tail_type)
    }
}
