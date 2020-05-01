use std::collections::HashMap;

use crate::ast;
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
struct Func {
    /// the number of parameters, when types are introduced this will likely be replaced with a
    /// list of type information for each parameter.
    n_params: usize,
}

/// Currently variables are all isize so no information is required!
#[derive(Debug, Clone)]
struct Variable {}

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
    func: Func,
    source: &'a ast::Item<'a>,
}

/// Represents a lexical scope. These usually contain ScopeItems which are named variabled.
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
    variable: Variable,
    source: Option<ast::Node<'a>>,
}

impl<'a, 'b: 'a> TopLevelScope<'a> {
    /// Takes a slice of top-level items and builds a `TopLevelScope` from them.
    /// It does not verify the items as this should be done after the scope is fully constructed.
    fn build(items: &'b [ast::Item<'b>]) -> (TopLevelScope<'a>, Vec<Error<'b>>) {
        let mut out = TopLevelScope {
            map: HashMap::with_capacity(items.len()),
        };
        let mut errors = Vec::new();

        for item in items {
            match &item.kind {
                ast::ItemKind::FnDecl { name, params, body: _ } => {
                    if let Some(conflict) = out.map.insert(
                        name.name,
                        TopLevelItem {
                            func: Func {
                                n_params: params.len(),
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
            ast::ItemKind::FnDecl { name: _, params, body } => Scope::check_fn(self, params, body),
        }
    }

    fn check_items(&'a self, items: &'b [ast::Item<'b>]) -> Vec<Error<'b>> {
        let mut errors = Vec::new();
        for item in items {
            errors.extend(self.check_item(&item.kind));
        }
        errors
    }
}

impl<'a, 'b: 'a> Scope<'a> {
    /// Creates a new scope containing the given item with the given parent.
    /// The TopLevelScope is inherited from `parent`.
    fn new(item: ScopeItem<'a>, parent: &'a Scope<'a>) -> Scope<'a> {
        Scope {
            item: Some(item),
            parent: Some(parent),
            top_level: parent.top_level,
        }
    }
    /// Creates a new empty scope - with no item and no parent.
    fn empty(top_level: &'a TopLevelScope<'a>) -> Scope<'a> {
        Scope {
            item: None,
            parent: None,
            top_level,
        }
    }

    /// Creates a new scope, a child of `self`, containing `item`.
    fn child(&'a self, item: ScopeItem<'a>) -> Scope<'a> {
        Self::new(item, self)
    }

    /// Given a TopLevelScope, check_fn checks the body of the function and returns any errors.
    fn check_fn(
        top_level: &'a TopLevelScope<'a>,
        params: &'b ast::FnParams<'b>,
        block: &'b ast::Block<'b>,
    ) -> Vec<Error<'b>> {
        // Storage for later
        let empty;
        let mut scopes;

        let fn_scope = if params.is_empty() {
            empty = Self::empty(top_level);
            &empty
        } else {
            // We'll now create a scope for each parameter.
            // It's a shame we can't do this on the stack :(
            scopes = Vec::with_capacity(params.len());
            for param in params {
                scopes.push(Scope {
                    item: Some(ScopeItem {
                        name: param.name,
                        variable: Variable {},
                        source: Some(param.node()),
                    }),
                    // parent will be filled in later
                    parent: None,
                    top_level,
                });
            }
            // This is down here rather than in the main loop to isolate the unsafe.
            // Using unsafe along with push seemed risky because although we know, when writing
            // this, that the vec won't need to exapand and reallocate, it seems risky since
            // someone could easily make a change that without thinking about this.
            for i in 1..scopes.len() {
                let parent = scopes.get(i-1)
                    .map(|x| unsafe { &*(x as *const Scope) });
                scopes[i].parent = parent;
            }
            ///// !!!!!!!!!!!!!!! DO NOT CHANGE `scopes` AFTER THIS UNSAFE !!!!!!!!!!!!!!! /////

            scopes.last().unwrap()
        };

        fn_scope.check_block(block, 0)
    }

    /// Finds a scope item with the given name. This bubbles up to parent scopes.
    fn get(&self, name: &str) -> Option<&ScopeItem<'a>> {
        if let Some(item) = &self.item {
            if item.name == name {
                return Some(item);
            }
        }
        self.parent.and_then(|scope| scope.get(name))
    }

    /// Returns any errors in the given expression when evaluated in this scope.
    fn check_expr(&'a self, expr: &'b ast::Expr<'b>) -> Vec<Error<'b>> {
        match &expr.kind {
            ast::ExprKind::BinOp(left, _, right) => {
                let mut errors = self.check_expr(&*left);
                errors.extend(self.check_expr(&*right));
                errors
            }
            ast::ExprKind::PrefixOp(_, inner_expr) => self.check_expr(&*inner_expr),
            ast::ExprKind::Num(_) => Vec::new(), // Woo! No errors here!
            // (Overflows will be handled when the int is
            //  parsed? If the interpreter is going to parse
            //  from the AST then we can validate here for
            //  now.)
            ast::ExprKind::Bracket(block) => self.check_block(&block, 0),
            ast::ExprKind::Named(name) => match self.get(name.name) {
                Some(_) => Vec::new(),
                None => vec![Error {
                    kind: error::Kind::VariableNotFound,
                    context: error::Context::Expr,
                    source: expr.node(),
                }],
            },
            ast::ExprKind::FnCall(fn_expr, args) => {
                let name = match &fn_expr.kind {
                    ast::ExprKind::Named(name) => name.name,
                    _ => {
                        return vec![Error {
                            kind: error::Kind::FunctionMustBeName,
                            context: error::Context::Expr,
                            source: fn_expr.node(),
                        }]
                    }
                };

                let func = match self.top_level.map.get(name) {
                    None => {
                        return vec![Error {
                            kind: error::Kind::FunctionNotFound,
                            context: error::Context::Expr,
                            source: fn_expr.node(),
                        }]
                    }
                    Some(item) => &item.func,
                };

                if func.n_params != args.len() {
                    vec![Error {
                        kind: error::Kind::IncorrectNumberOfArgs {
                            n_given: args.len(),
                            n_expected: func.n_params,
                        },
                        context: error::Context::Expr,
                        source: ast::Node::Args(&args),
                    }]
                } else {
                    Vec::new() // Nothing is wrong!!!
                }
            }
            ast::ExprKind::Empty => Vec::new(),
        }
    }

    fn check_assign(&'a self, ident: &'b ast::Ident<'b>, expr: &'b ast::Expr<'b>) -> Vec<Error<'b>> {
        let mut errors = Vec::new();
        if let None = self.get(ident.name) {
            errors.push(Error {
                kind: error::Kind::VariableNotFound,
                context: error::Context::Assign,
                source: ident.node(),
            });
        }
        errors.extend(self.check_expr(&expr));
        errors
    }

    fn check_block(&'a self, block: &'b ast::Block<'b>, start: usize) -> Vec<Error<'b>> {
        let mut errors = Vec::new();

        // Check the statements from `start`
        for idx in start..block.body.len() {
            let stmt = &block.body[idx];
            match &stmt.kind {
                ast::StmtKind::Eval(expr) | ast::StmtKind::Print(expr) => {
                    errors.extend(self.check_expr(&expr))
                }

                ast::StmtKind::Assign(name, expr) => errors.extend(self.check_assign(name, expr)),

                ast::StmtKind::Let(name, expr) => {
                    errors.extend(self.check_expr(&expr));

                    let new_scope = self.child(ScopeItem {
                        name: name.name,
                        variable: Variable {},
                        source: Some(stmt.node()),
                    });

                    // Check the remainder of this block with the new scope, then return.
                    errors.extend(new_scope.check_block(block, idx + 1));
                    return errors;
                }
            }
        }

        errors.extend(self.check_expr(&*block.tail));

        errors
    }
}
