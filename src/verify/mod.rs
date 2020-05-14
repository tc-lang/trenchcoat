use std::collections::HashMap;

use crate::ast;
use crate::types::{self, Type};
pub mod error;
use error::Error;
use std::mem::transmute; // :)

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

pub struct TopLevelErrors<'a>(TopLevelScope<'a>);

pub fn verify<'a>(items: &'a [ast::Item<'a>]) -> TopLevelErrors<'a> {
    let mut top_level = TopLevelErrors(TopLevelScope::build(items));

    unsafe {
        let top_level: &mut TopLevelScope = transmute(&mut top_level.0);
        let items: &[ast::Item] = transmute(items);

        top_level.check_items(items);
    }

    top_level
}

impl<'a> std::ops::Deref for TopLevelErrors<'a> {
    type Target = Vec<Error<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0.errors
    }
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
struct Variable<'a> {
    typ: &'a Type<'a>,
}

/// The top level scope consists of named items, currently just functions. Things will be
/// transitioned out of here as they can be placed in local scopes until everything is under
/// the `Scope` type. It exists now for simplicity.
#[derive(Debug, Clone)]
struct TopLevelScope<'a> {
    items: HashMap<&'a str, TopLevelItem<'a>>,
    errors: Vec<Error<'a>>,
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
struct Scope<'a> {
    item: Option<ScopeItem<'a>>,
    parent: Option<&'a Scope<'a>>,
    top_level: &'a TopLevelScope<'a>,
}

#[derive(Debug, Clone)]
struct ScopeItem<'a> {
    name: &'a str,
    variable: Variable<'a>,
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

impl<'a> TopLevelScope<'a> {
    /// Takes a slice of top-level items and builds a `TopLevelScope` from them.
    /// It does not verify the items as this should be done after the scope is fully constructed.
    fn build(items: &'a [ast::Item]) -> Self {
        let mut top = TopLevelScope {
            items: HashMap::with_capacity(items.len()),
            errors: Vec::new(),
        };

        for item in items {
            match &item.kind {
                ast::ItemKind::FnDecl {
                    name,
                    params,
                    ret,
                    body: _,
                } => {
                    if let Some(conflict) = top.items.insert(
                        name.name,
                        TopLevelItem {
                            func: Func {
                                params: params.iter().map(|param| &param.1).collect(),
                                ret,
                            },
                            source: item,
                        },
                    ) {
                        top.errors.push(Error {
                            kind: error::Kind::ItemConflict(conflict.source, item),
                            context: error::Context::TopLevel,
                            source: item.node(),
                        });
                    }
                }
            }
        }

        top
    }

    /// Checks a single top-level item (currently just functions), and adds any errors to the
    /// internal set
    fn check_item(&'a mut self, item: &'a ast::ItemKind) {
        match item {
            ast::ItemKind::FnDecl {
                name: _,
                params,
                ret,
                body,
            } => self.check_fn(params, ret, body),
        }
    }

    fn check_items(&'a mut self, items: &'a [ast::Item]) {
        for item in items {
            let this: *mut TopLevelScope = self as *mut TopLevelScope;
            let this: &mut TopLevelScope = unsafe { &mut *this };

            this.check_item(&item.kind)
        }
    }

    /// Given a TopLevelScope, check_fn checks the body of the function and adds any errors to the
    /// internal set
    fn check_fn(
        &'a mut self,
        params: &'a ast::FnParams,
        ret: &'a ast::TypeExpr,
        block: &'a ast::Block,
    ) {
        // Create a scope containing all the function arguments.
        let empty;
        let mut scopes;
        let (mut errors, tail_type) = if params.is_empty() {
            // If there aren't any, then this is just an empty scope.
            empty = Scope {
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
            scopes = params
                .iter()
                .map(|param| Scope {
                    item: Some(ScopeItem {
                        name: param.0.name,
                        variable: Variable { typ: &param.1.typ },
                        source: Some(param.0.node()),
                    }),
                    parent: None,
                    top_level: unsafe { transmute(self as &Self) },
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

        if *tail_type != ret.typ {
            errors.push(Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![ret.typ.clone()],
                    found: tail_type.clone(),
                },
                context: error::Context::FnTail,
                source: block.tail.node(),
            })
        }

        // lifetime extension
        let errors: Vec<Error> = unsafe { transmute(errors) };
        self.errors.extend(errors)
    }
}

impl<'a> Scope<'a> {
    /// Creates a new scope containing the given item with the given parent.
    /// The TopLevelScope is inherited from `parent`.
    fn new(item: ScopeItem<'a>, parent: &'a Scope) -> Self {
        Scope {
            item: Some(item),
            parent: Some(parent),
            top_level: parent.top_level,
        }
    }
    /// Creates a new empty scope - with no item and no parent.
    fn empty(top_level: &'a TopLevelScope) -> Self {
        Scope {
            item: None,
            parent: None,
            top_level,
        }
    }

    /// Creates a new scope, a child of `self`, containing `item`.
    fn child(&self, item: ScopeItem<'a>) -> Scope {
        Scope::new(item, self)
    }

    /// Finds a scope item with the given name. This bubbles up to parent scopes.
    fn get(&self, name: &str) -> Option<&ScopeItem> {
        match &self.item {
            Some(item) if item.name == name => return Some(item),
            _ => self.parent.and_then(|scope| scope.get(name)),
        }
    }

    /// Finds a function with the given name. This only checks the top level scope.
    fn get_fn(&self, name: &str) -> Option<&Func> {
        Some(&self.top_level.items.get(name)?.func)
    }

    fn same_type_check(
        left: &'a Type,
        left_source: ast::Node,
        right: &'a Type,
        right_source: ast::Node<'a>,
    ) -> Vec<Error<'a>> {
        if *right == *left {
            Vec::new()
        } else {
            vec![Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![left.clone()],
                    found: right.clone(),
                },
                context: error::Context::BinOpTypeCheck,
                source: right_source,
            }]
        }
    }

    fn integer_check(t: &'a Type, source: ast::Node<'a>) -> Vec<Error<'a>> {
        // The left operand must be an integer type
        if *t == Type::Int || *t == Type::Uint {
            Vec::new()
        } else {
            vec![Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![Type::Int, Type::Uint],
                    found: t.clone(),
                },
                context: error::Context::BinOpTypeCheck,
                source: source,
            }]
        }
    }

    fn bool_check(t: &'a Type, source: ast::Node<'a>) -> Vec<Error<'a>> {
        match t {
            Type::Bool => Vec::new(),
            _ => vec![Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![Type::Bool],
                    found: t.clone(),
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
        op: &'a ast::BinOp,
        left: &'a Type,
        left_source: ast::Node<'a>,
        right: &'a Type,
        right_source: ast::Node<'a>,
    ) -> (Vec<Error<'a>>, &'a Type<'a>) {
        use ast::BinOp::*;

        let mut errors: Vec<Error> = Vec::new();
        let output_type;

        match op {
            // Boolean to Boolean operators
            Or | And => {
                errors.extend(Scope::bool_check(left, left_source.clone()));
                output_type = &Type::Bool;
            }
            // T x T => Boolean type operators
            Eq => output_type = &Type::Bool,
            // Integer x Integer -> Integer operators
            Add | Sub | Mul | Div => {
                errors.extend(Scope::integer_check(left, left_source.clone()));
                output_type = left;
            }
            // Integer x Integer -> Boolean operators
            Lt | Le | Gt | Ge => {
                errors.extend(Scope::integer_check(left, left_source.clone()));
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
        op: &'a ast::PrefixOp,
        t: &'a Type,
        source: ast::Node<'a>,
    ) -> (Vec<Error<'a>>, &'a Type<'a>) {
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
    fn check_expr(&'a self, expr: &'a ast::Expr) -> (Vec<Error<'a>>, &'a Type<'a>) {
        use ast::ExprKind::{
            BinOp, Bracket, Empty, FieldAccess, FnCall, Named, Num, PrefixOp, Struct,
        };

        match &expr.kind {
            BinOp(left, op, right) => {
                let (mut errors, left_type) = self.check_expr(left);
                let (right_errors, right_type) = self.check_expr(right);
                errors.extend(right_errors);
                let (op_errors, final_type) =
                    Self::bin_op_types(op, left_type, left.node(), right_type, right.node());
                errors.extend(op_errors);
                (errors, final_type)
            }
            PrefixOp(op, inner_expr) => {
                let (mut errors, expr_type) = self.check_expr(inner_expr);
                let (op_errors, final_type) =
                    Self::prefix_op_types(op, expr_type, inner_expr.node());
                errors.extend(op_errors);
                (errors, final_type)
            }
            Num(_) => (Vec::new(), &Type::Int), // Woo! No errors here!
            // (Overflows will be handled when the int is
            //  parsed? If the interpreter is going to parse
            //  from the AST then we can validate here for
            //  now.)
            Bracket(block) => self.check_block(&block, 0),
            Named(name) => match self.get(name.name) {
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
            FnCall(fn_expr, args) => {
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
                                expected: vec![func.params[i].typ.clone()],
                                found: arg_type.clone(),
                            },
                            context: error::Context::FnArg,
                            source: args[i].node(),
                        });
                    }
                }

                (errors, &func.ret.typ)
            }
            Empty => (Vec::new(), &types::empty_struct),
            FieldAccess(_, _) => todo!(),
            Struct(_) => todo!(),
        }
    }

    fn check_assign(&'a self, ident: &'a ast::Ident, expr: &'a ast::Expr) -> Vec<Error<'a>> {
        let mut errors = Vec::new();
        let (expr_errors, expr_type) = self.check_expr(&expr);
        errors.extend(expr_errors);
        match self.get(ident.name) {
            Some(item) => {
                if *item.variable.typ != *expr_type {
                    errors.push(Error {
                        kind: error::Kind::TypeMismatch {
                            expected: vec![item.variable.typ.clone()],
                            found: expr_type.clone(),
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

    fn check_block(&'a self, block: &'a ast::Block, start: usize) -> (Vec<Error<'a>>, &Type<'a>) {
        use ast::StmtKind::{Assign, Eval, Let, Print};

        let mut errors = Vec::new();

        // Check the statements from `start`
        for idx in start..block.body.len() {
            let stmt = &block.body[idx];
            match &stmt.kind {
                Eval(expr) | Print(expr) => {
                    let (expr_errors, _) = self.check_expr(&expr);
                    errors.extend(expr_errors);
                }

                Assign(name, expr) => errors.extend(self.check_assign(name, expr)),

                Let(name, expr) => {
                    let (expr_errors, typ) = self.check_expr(&expr);
                    errors.extend(expr_errors);

                    let new_scope = self.child(ScopeItem {
                        name: name.name,
                        variable: Variable { typ },
                        source: Some(stmt.node()),
                    });

                    // Check the remainder of this block with the new scope, then return.
                    let (mut other_errors, block_type) = new_scope.check_block(block, idx + 1);
                    // We reverse the errors here because otherwise there'd be a (erroneous)
                    // borrow-checker conflict on the final return in this function -- outside of
                    // this block -- because `errors` references `new_scope` only in this block.
                    other_errors.extend(errors);

                    unsafe {
                        return transmute((other_errors, block_type));
                    }
                }
            }
        }

        let (tail_errors, tail_type) = self.check_expr(&block.tail);
        errors.extend(tail_errors);

        (errors, tail_type)
    }
}
