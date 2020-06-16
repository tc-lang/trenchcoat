pub mod error;
mod prover;

use crate::ast::proof::Stmt as ProofStmt;
use crate::ast::{
    self, BinOp, Block, Expr, ExprKind, FnArgs, Ident, Item, ItemKind, PrefixOp,
    StmtKind, TypeExpr, IdentSource,
};
use crate::proof::{self, ProofResult, Requirement};
use crate::types::{self, Type};
use error::Error;
use prover::WrappedProver;
use std::collections::HashMap;
use std::mem::transmute; // :)
use crate::tokens::FAKE_TOKEN;

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

/// A wrapper around the top-level scope so that the errors can be safely referenced.
///
/// This is needed because the errors collected into the top-level scope *can* borrow data stored
/// within the top-level scope. It's more responsible for us to manage that drop order than to
/// expect the caller to do it properly.
pub struct TopLevelErrors<'a>(TopLevelScope<'a>);

pub fn verify<'a>(items: &'a [Item<'a>]) -> TopLevelErrors<'a> {
    let mut top_level = TopLevelErrors(TopLevelScope::build(items));

    unsafe {
        let top_level: &mut TopLevelScope = transmute(&mut top_level.0);
        top_level.check_items();
    }

    top_level
}

impl<'a> std::ops::Deref for TopLevelErrors<'a> {
    type Target = Vec<Error<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0.errors
    }
}

/// The representation of a single function from the top-level scope
///
/// This is for storing information about the function so that calls to this function can be
/// validated later. The name is not given here because the set of `Func`s is keyed by name.
#[derive(Debug, Clone)]
pub struct Func<'a> {
    /// The requirements on the function, all of which must be true
    ///
    /// This value will be `None` if the requirements were malformed (or there was otherwise an
    /// issue, e.g. referencing a variable not in scope).
    reqs: Option<Vec<Requirement<'a>>>,

    /// The 'contracts' given by a function. These are a set of statments asserting that - given
    /// some (optional) requirement on the input, the output requirement will be satisfied.
    ///
    /// These are checked whenever they are used in order to provide additional information about
    /// variables created by any callers of this function.
    ///
    /// Like `reqs`, `contracts` will be `None` if there was an error in validating them.
    contracts: Option<Vec<(Option<Requirement<'a>>, Requirement<'a>)>>,

    /// The types of each parameter, along with their names
    ///
    /// The names are used for substitution into the requirements on the function.
    params: Vec<(&'a Ident<'a>, &'a Type<'a>)>,

    /// The return type
    ret: &'a TypeExpr<'a>,

    /// The inner block of the function
    ///
    /// This is kept here so that verification can be done using only this type.
    block: &'a Block<'a>,

    /// The `Item` responsible for generating the associated data for this function
    source: &'a Item<'a>,
}

/// The top level scope consists of named items, currently just functions. Things will be
/// transitioned out of here as they can be placed in local scopes until everything is under
/// the `Scope` type. It exists now for simplicity.
struct TopLevelScope<'a> {
    items: HashMap<&'a str, Func<'a>>,
    errors: Vec<Error<'a>>,

    // A set of provers that's stored so that the errors can reference the strings stored in the
    // provers. This *must* be dropped after `errors`.
    provers: Vec<Option<WrappedProver<'a>>>,
}

impl<'a> Drop for TopLevelScope<'a> {
    fn drop(&mut self) {
        // Clear out all of the errors before the provers, because the errors might have borrowed
        // some of the content stored in the provers
        self.errors.drain(..).for_each(std::mem::drop);
        self.provers.drain(..).for_each(std::mem::drop);
    }
}

/// Represents a lexical scope. These usually contain ScopeItems which are named variables.
/// They may also have an optional parent which getting names can bubble up to.
///
/// All `Scope`s are given the items within the top-level scope as a map from names to functions.
/// The reason a `TopLevelScope` is not used for this instead is because of borrow conflicts that
/// would be acceptable if Rust had support for partial borrowing, but currently would require
/// `unsafe` blocks.
#[derive(Debug, Clone)]
struct Scope<'a> {
    item: Option<ScopeItem<'a>>,
    parent: Option<&'a Scope<'a>>,
    top_level: &'a HashMap<&'a str, Func<'a>>,
}

/// A single scope item; a variable and its type
#[derive(Debug, Clone)]
struct ScopeItem<'a> {
    name: &'a str,
    typ: Type<'a>,
    source: Option<ast::Node<'a>>,
}

impl<'a> TopLevelScope<'a> {
    /// Takes a slice of top-level items and builds a `TopLevelScope` from them.
    ///
    /// The only verification performed is on the proof statements given above functions - that
    /// they are (minimally) semantically valid.
    fn build(items: &'a [Item<'a>]) -> Self {
        let mut top = TopLevelScope {
            items: HashMap::with_capacity(items.len()),
            errors: Vec::new(),
            provers: Vec::with_capacity(items.len()),
        };

        for item in items {
            // Little bit of helpful deconstructing
            let ItemKind::FnDecl {
                proof_stmts,
                name,
                params,
                return_type,
                body,
            } = &item.kind;

            let params: Vec<_> = params.iter().map(|&(ref name, ref ty)| (name, ty)).collect();

            let res = TopLevelScope::check_proof_stmts(proof_stmts, &params, return_type, item);
            let (reqs, contracts) = match res {
                Err(errs) => {
                    top.errors.extend(errs);
                    (None, None)
                }
                Ok((rs, cs)) => (Some(rs), Some(cs)),
            };

            let func = Func {
                reqs,
                contracts,
                params,
                ret: return_type,
                block: body,
                source: item,
            };

            if let Some(conflict) = top.items.insert(name.name, func) {
                top.errors.push(Error {
                    kind: error::Kind::ItemConflict(conflict.source, item),
                    context: error::Context::TopLevel,
                    source: item.node(),
                })
            }
        }

        top
    }

    /// Attempts to semantically verify the proof statments on a function, returning the relevant
    /// fields on `Func` or any errors detected.
    ///
    /// This function performs a simple task; it essentially checks that all variables referenced
    /// are present in the parameter list - and that they are integers.
    ///
    /// Additionally, any post conditions *must* include the implicit return variable, `_`, and -
    /// if there are any contracts - the return type must be an integer.
    ///
    /// If successful, the lists of requirements and contracts (as given by the fields on `Func`)
    /// will be returned. If not, the list of errors will be instead.
    fn check_proof_stmts(
        stmts: &'a [ProofStmt<'a>],
        params: &[(&Ident<'a>, &Type<'a>)],
        ret_ty: &TypeExpr<'a>,
        source_item: &'a Item<'a>,
    ) -> Result<
        (
            Vec<Requirement<'a>>,
            Vec<(Option<Requirement<'a>>, Requirement<'a>)>,
        ),
        Vec<Error<'a>>,
    > {
        use crate::ast::proof::{
            Condition, ConditionKind, Expr as ProofExpr,
            ExprKind::{Compound, Literal, Malformed, Named},
            StmtKind::{self, Contract, Require},
        };

        fn check_expr<'b>(
            expr: &'b ProofExpr<'b>,
            allow_return_ident: bool,
            params: &[(&Ident<'b>, &Type<'b>)],
            required_return_int: &mut bool,
        ) -> Vec<Error<'b>> {
            match &expr.kind {
                Compound { lhs, rhs, .. } => {
                    // recurse on both sides
                    let mut lhs_errs =
                        check_expr(&lhs, allow_return_ident, params, required_return_int);
                    let rhs_errs =
                        check_expr(&rhs, allow_return_ident, params, required_return_int);
                    lhs_errs.extend(rhs_errs);
                    lhs_errs
                }
                // Nothing to do; integer literals are just fine
                Literal(_) => vec![],
                // ---
                Named(ident) => match ident.name {
                    // The implicit return identifier
                    "_" if allow_return_ident => {
                        *required_return_int = true;
                        Vec::new()
                    }
                    // If the return identifier isn't allowed in preconditions or requirements, so
                    // we'll catch that here
                    "_" => vec![Error {
                        kind: error::Kind::MisplacedReturnIdent,
                        context: error::Context::ProofStmt,
                        source: ident.node(),
                    }],
                    name => {
                        // We want to check two things: (1) the name is, in fact, a parameter; and
                        // (2) that parameter has an integer type (either `Int` or `UInt`)
                        match params.iter().find(|(id, _)| id.name == name) {
                            Some((_, ty)) => match ty {
                                &Type::Int | &Type::UInt => Vec::new(),
                                _ => vec![Error {
                                    kind: error::Kind::TypeMismatch {
                                        expected: vec![Type::Int, Type::UInt],
                                        found: <Type as Clone>::clone(ty),
                                    },
                                    context: error::Context::ProofStmt,
                                    source: ident.node(),
                                }],
                            },
                            None => vec![Error {
                                kind: error::Kind::VariableNotFound,
                                context: error::Context::ProofStmt,
                                source: ident.node(),
                            }],
                        }
                    }
                },
                Malformed => panic!("Unexpected malformed proof expression in `verify`"),
            }
        }

        fn check_condition<'b>(
            cond: &'b Condition<'b>,
            allowed_return_ident: bool,
            params: &[(&Ident<'b>, &Type<'b>)],
            required_return_int: &mut bool,
            source: ast::Node<'b>,
        ) -> Vec<Error<'b>> {
            match &cond.kind {
                ConditionKind::Compound { .. } => vec![Error {
                    kind: error::Kind::FeatureNotAllowed {
                        description:
                            "Logical operators are currently not allowed in proof statements",
                    },
                    context: error::Context::ProofStmt,
                    source,
                }],
                ConditionKind::Simple {
                    ref lhs, ref rhs, ..
                } => {
                    let mut lhs_errs =
                        check_expr(lhs, allowed_return_ident, params, required_return_int);
                    let rhs_errs =
                        check_expr(rhs, allowed_return_ident, params, required_return_int);

                    lhs_errs.extend(rhs_errs);
                    lhs_errs
                }
                ConditionKind::Malformed => {
                    panic!("Unexpected malformed proof condition in `verify`")
                }
            }
        }

        let mut required_return_int = false;
        let mut errors = Vec::new();

        let mut reqs = <Vec<Requirement>>::new();
        let mut contracts = <Vec<(Option<Requirement>, Requirement)>>::new();

        for stmt in stmts {
            match &stmt.kind {
                Require(ref cond) => {
                    errors.extend(check_condition(
                        cond,
                        false,
                        params,
                        &mut required_return_int,
                        stmt.node(),
                    ));
                    reqs.push(cond.into());
                }
                Contract { pre, ref post } => {
                    errors.extend(
                        pre.as_ref()
                            .map(|c| check_condition(c, false, params, &mut required_return_int, stmt.node()))
                            .unwrap_or(vec![]),
                    );
                    errors.extend(check_condition(
                        post,
                        true,
                        params,
                        &mut required_return_int,
                        stmt.node()
                    ));
                    contracts.push((pre.as_ref().map(Into::into), post.into()));
                }
                &StmtKind::Malformed => panic!("Unexpected malformed proof statment in `verify`"),
            }
        }

        // If we require that the return type is an integer, but it isn't, we'll add that to the
        // list of errors.
        if required_return_int && &ret_ty.typ != &Type::Int && &ret_ty.typ != &Type::UInt {
            errors.push(Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![Type::Int, Type::UInt],
                    found: ret_ty.typ.clone(),
                },
                context: error::Context::ProofStmt,
                source: ast::Node::Item(source_item),
            })
        }

        match errors.is_empty() {
            true => Ok((reqs, contracts)),
            false => Err(errors),
        }
    }

    /// Verify that each individual item (read: currently only functions) is valid.
    fn check_items(&'a mut self) {
        for func in self.items.values() {
            let (prover, errs) = TopLevelScope::check_fn(func, &self.items);
            self.errors.extend(errs);
            self.provers.push(prover);
        }
    }

    /// Given pieces of a `TopLevelScope`, this checks the body of the function and returns any
    /// errors found
    ///
    /// Note that the returned errors may reference the provers given. As such, it should be
    /// guaranteed by the caller that the errors are dropped first.
    fn check_fn(func: &'a Func<'a>, items: &'a HashMap<&'a str, Func<'a>>) -> (Option<WrappedProver<'a>>, Vec<Error<'a>>) {
        let mut base_prover = func.reqs.as_ref().cloned().map(WrappedProver::new);

        // Create a scope containing all the function arguments
        let empty;
        let mut scopes;
        let prover = base_prover.as_mut();

        let (mut errors, tail_type, _ret_ident, _stop_proof) = if func.params.is_empty() {
            // If there aren't any, then this is just an empty scope.
            empty = Scope {
                item: None,
                parent: None,
                top_level: items,
            };
            // Intentional lifetime shrinking so that the prover doesn't require the scope to have
            // a longer lifetime
            let prover = unsafe { transmute(prover) };

            empty.check_block(prover, func.block, 0)
        } else {
            // We'll now create a scope for each parameter.
            // Using the notation `parent <- child`, this will create the structure:
            //  Scope{ param0 } <- Scope{ param1 } <- Scope{ param2 } <- ...

            // First, we'll create each of the scopes without parents.
            // It's a shame we can't do this on the stack :(
            scopes = func
                .params
                .iter()
                .map(|(param, typ)| Scope {
                    item: Some(ScopeItem {
                        name: param.name,
                        typ: Type::clone(typ),
                        source: Some(param.node()),
                    }),
                    parent: None,
                    top_level: items,
                })
                .collect::<Vec<_>>();

            // Then, we'll link each scope to it's parent. So the scope for param n gets a parent
            // of the scope for param n-1.

            // This is down here rather than in the main loop to isolate the unsafe.
            // Using unsafe along with push seemed risky because although we know, when writing
            // this, that the vec won't need to expand and reallocate, it seems risky since someone
            // could easily make a change that without thinking about this.
            for i in 1..scopes.len() {
                let parent = scopes.get(i - 1).map(|x| unsafe { &*(x as *const Scope) });
                scopes[i].parent = parent;
            }
            ///// !!!!!!!!!!!!!!! DO NOT CHANGE `scopes` AFTER THIS UNSAFE !!!!!!!!!!!!!!! /////
            
            // Intentional lifetime shrinking so that the prover doesn't require the scope to have
            // a longer lifetime
            let prover = unsafe { transmute(prover) };

            scopes.last().unwrap().check_block(prover, func.block, 0)
        };

        drop(_ret_ident);

        // And now `scopes` shouldn't be borrowed anymore

        if tail_type != func.ret.typ {
            errors.push(Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![func.ret.typ.clone()],
                    found: tail_type.clone(),
                },
                context: error::Context::FnTail,
                source: func.block.tail.node(),
            })
        }

        // Lifetime extension. This cirucmvents what would be a reliance on borrowed data in
        // `scopes` and `empty`. The reason it's safe to extend the lifetime is because the
        // generated errors don't reference the data *owned* by the two values in this scope, but
        // the things *they* reference.
        unsafe { (base_prover, transmute(errors as Vec<Error>)) }
    }
}

/// This macro primarily exists for thoroughly disrespecting the borrow-checker
///
/// Throughout many of the functions below, we pass an `Option<&mut WrappedProver>` to allow proof
/// to take place. Unfortunately, the borrowing rules mean that any usage of this type would amount
/// to full consumption; there isn't any way to use it twice without unsafe blocks.
///
/// So that's what this macro provides: "aliased" mutable references. Typically that would be UB in
/// Rust -- it's one of the core assumptions that allows many optimizations. Here, it's expected
/// that the caller understand that the prover MUST be used (consumed) immediately.
///
/// This macro - in essence - provides two things: A variable `__raw_prover` that is instead as
/// type `Option<*mut WrappedProver>`, and a separate `prover!` macro that gives short-lived access
/// to that variable as a `Option<&mut WrappedProver>`, allowing callers to use it multiple times.
macro_rules! split_prover {
    ($prover:ident) => {
        let __raw_prover = $prover.map(|p| p as *mut WrappedProver<'a>);

        macro_rules! prover {
            () => {
                __raw_prover.map(|p| unsafe { &mut *p })
            }
        }
    }
}

impl<'a> Scope<'a> {
    /// Creates a new scope, a child of `self`, containing `item`.
    fn child(&'a self, item: ScopeItem<'a>) -> Scope<'a> {
        Scope {
            item: Some(item),
            parent: Some(self),
            top_level: self.top_level,
        }
    }

    /// Finds a scope item with the given name. This bubbles up to parent scopes.
    fn get(&'a self, name: &str) -> Option<&'a ScopeItem> {
        match &self.item {
            Some(item) if item.name == name => return Some(item),
            _ => self.parent.and_then(|scope| scope.get(name)),
        }
    }

    /// Finds a function with the given name. This only checks the top level scope.
    fn get_fn(&'a self, name: &str) -> Option<&'a Func<'a>> {
        self.top_level.get(name)
    }

    /// Checks that the given type is an integer type (either `Int` or `UInt`), and returns a
    /// `TypeMismatch` error with no context if not.
    fn integer_check(t: &Type<'a>, source: ast::Node<'a>) -> Option<Error<'a>> {
        if t == &Type::Int || t == &Type::UInt {
            return None;
        }

        Some(Error {
            kind: error::Kind::TypeMismatch {
                expected: vec![Type::Int, Type::UInt],
                found: t.clone(),
            },
            context: error::Context::NoContext,
            source: source,
        })
    }

    /// Checks that the given type is a boolean, returning a `TypeMismatch` error with no context
    /// if it is not.
    fn bool_check(t: &Type<'a>, source: ast::Node<'a>) -> Option<Error<'a>> {
        match t {
            Type::Bool => None,
            _ => Some(Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![Type::Bool],
                    found: t.clone(),
                },
                context: error::Context::NoContext,
                source: source,
            }),
        }
    }

    fn check_bin_op_expr(
        &'a self,
        prover: Option<&mut WrappedProver<'a>>,
        lhs: &'a Expr<'a>,
        op: BinOp,
        rhs: &'a Expr<'a>,
        enclosing_expr: &'a Expr<'a>
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, bool) {
        use BinOp::{Add, And, Div, Eq, Ge, Gt, Le, Lt, Mul, Or, Sub};

        split_prover!(prover);
    
        // The first thing we'll do is to check both sides of the expression

        let (mut errors, lhs_ty, lhs_tmp_var, lhs_stop) = self.check_expr(prover!(), lhs);
        let (rhs_errs, rhs_ty, rhs_tmp_var, rhs_stop) = self.check_expr(prover!(), rhs);
        errors.extend(rhs_errs);

        // And now we check the types, adding on any errors that we find
        let mut has_type_errs = false;
        let output_type = match op {
            // Boolean to Boolean operators
            Or | And => {
                if let Some(err) = Scope::bool_check(&lhs_ty, lhs.node()) {
                    has_type_errs = true;
                    errors.push(err.with_context(error::Context::BinOpTypeCheck));
                }
                Type::Bool
            }
            // T x T => Boolean type operators
            Eq => Type::Bool,
            // Integer x Integer -> Integer operators
            Add | Sub | Mul | Div => {
                if let Some(err) = Scope::integer_check(&lhs_ty, lhs.node().clone()) {
                    has_type_errs = true;
                    errors.push(err.with_context(error::Context::BinOpTypeCheck));
                }
                lhs_ty.clone()
            }
            // Integer x Integer -> Boolean operators
            Lt | Le | Gt | Ge => {
                if let Some(err) = Scope::integer_check(&lhs_ty, lhs.node().clone()) {
                    has_type_errs = true;
                    errors.push(err.with_context(error::Context::BinOpTypeCheck));
                }
                Type::Bool
            }
        };

        let same_type_err = match has_type_errs {
            true => None,
            // We only want to check that the right-hand side has the same type as the left if the
            // left's type is actually valid.
            false => match lhs_ty == rhs_ty {
                // Success! No type errors
                true => None,
                // The types weren't equal, so we'll say that we expected the left-hand side type.
                false => Some(Error {
                    kind: error::Kind::TypeMismatch {
                        expected: vec![lhs_ty.clone()],
                        found: rhs_ty.clone(),
                    },
                    context: error::Context::BinOpTypeCheck,
                    source: rhs.node(),
                }),
            },
        };
        has_type_errs = has_type_errs || same_type_err.is_some();
        errors.extend(same_type_err);

        let out_tmp = if !has_type_errs && output_type == Type::Int || output_type == Type::UInt {
            prover!().map(|p| unsafe { p.gen_new_tmp(enclosing_expr) })
        } else { None };

        // Finally, if the types and operator are compatible with doing so, we'll add definitions
        // into the prover in order to account for the basic arithmetic operations.
        if let (Some(p), Some(t), Some(lhs), Some(rhs)) = (prover!(), out_tmp.clone(), lhs_tmp_var, rhs_tmp_var) {
            use crate::proof::Expr::{Neg, Recip, Sum, Prod};

            match op {
                Add => {
                    let expr = Sum(vec![lhs.into(), rhs.into()]);
                    p.define(t, expr);
                }
                Sub => {
                    let expr = Sum(vec![lhs.into(), Neg(Box::new(rhs.into()))]);
                    p.define(t, expr);
                },
                Mul => {
                    let expr = Prod(vec![lhs.into(), rhs.into()]);
                    p.define(t, expr);
                },
                Div => {
                    // FIXME: @Jacob - Is the boolean value in `Recip` correct here?
                    let expr = Prod(vec![lhs.into(), Recip(Box::new(rhs.into()), false)]);
                    p.define(t, expr);
                },
                _ => (),
            }
        }

        (errors, output_type, out_tmp, lhs_stop || rhs_stop || has_type_errs)
    }

    fn check_prefix_op_expr(
        &'a self,
        prover: Option<&mut WrappedProver<'a>>,
        op: PrefixOp,
        rhs: &'a Expr<'a>,
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, bool) {
        use PrefixOp::Not;

        let (mut errors, typ, _tmp_var, stop_proof) = self.check_expr(prover, rhs);

        let output_type = match op {
            // Boolean -> Boolean operators
            Not => {
                if let Some(err) = Scope::bool_check(&typ, rhs.node()) {
                    errors.push(err.with_context(error::Context::PrefixOpTypeCheck));
                }
                Type::Bool
            }
        };

        (errors, output_type, None, stop_proof)
    }

    /// Checks that the given expression is valid when evaluated in this scope.
    ///
    /// Returns any errors, the type of the evaluated expression, the variable (either named by the
    /// user or temporary) corresponding to the expression, if it is available.
    fn check_expr(
        &'a self,
        prover: Option<&mut WrappedProver<'a>>,
        expr: &'a Expr<'a>,
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, bool) {
        use ExprKind::{
            BinOp, Bracket, Empty, FieldAccess, FnCall, Malformed, Named, Num, PrefixOp, Struct,
        };

        match &expr.kind {
            BinOp(lhs, op, rhs) => self.check_bin_op_expr(prover, lhs, *op, rhs, expr),
            FnCall(fn_expr, args) => self.check_fn_call_expr(prover, fn_expr, args, expr),
            Empty => (Vec::new(), types::empty_struct(), None, false),
            Malformed => (Vec::new(), Type::Unknown, None, false), // the error will have already been raised
            Bracket(block) => self.check_block(prover, &block, 0),
            // (Overflows will be handled when the int is
            //  parsed? If the interpreter is going to parse
            //  from the AST then we can validate here for
            //  now.)
            Num(n) => {
                use crate::proof::{int::{Int, Rational}, expr::{Expr, Atom}};

                let tmp = prover.map(|p| {
                    let t = unsafe { p.gen_new_tmp(expr) };
                    p.define(
                        t.clone(),
                        Expr::Atom(Atom::Literal(Rational {
                            numerator: (*n as i128).into(),
                            denominator: Int::ONE
                        }))
                    );
                    t
                });

                (Vec::new(), Type::Int, tmp, false) // Woo! No errors here!
            }
            PrefixOp(op, inner_expr) => self.check_prefix_op_expr(prover, *op, inner_expr),
            Named(name) => match self.get(name.name) {
                Some(item) => (Vec::new(), item.typ.clone(), Some(name.clone()), false),
                None => (
                    vec![Error {
                        kind: error::Kind::VariableNotFound,
                        context: error::Context::Expr,
                        source: expr.node(),
                    }],
                    Type::Unknown,
                    None,
                    true,
                )
            }
            // Note: Currently proof doesn't carry through struct fields
            Struct(fields) => {
                split_prover!(prover);
                
                let mut errors = Vec::new();
                let mut stop_proof = false;

                let field_types = fields.iter().map(|(name, expr)| {
                    let (expr_errors, typ, _tmp_ident, stop) = self.check_expr(prover!(), expr);
                    stop_proof = stop_proof || stop;
                    errors.extend(expr_errors);

                    types::StructField { name: name.clone(), typ }
                }).collect();

                (errors, Type::Struct(field_types), None, stop_proof)
            }
            FieldAccess(expr, field_ident) => {
                let (mut errors, expr_type, _tmp_ident, stop_proof) = self.check_expr(prover, expr);
                let fields = match &expr_type {
                    Type::Struct(fields) => fields,
                    _ => {
                        errors.push(Error {
                            kind: error::Kind::AccessFieldOnNotStruct,
                            context: error::Context::FieldAccess,
                            source: expr.node(),
                        });
                        return (errors, Type::Unknown, None, stop_proof);
                    }
                };
                let field_type = match types::field_type(fields, field_ident.name) {
                    Some(t) => t,
                    None => {
                        errors.push(Error {
                            kind: error::Kind::AccessFieldOnNotStruct,
                            context: error::Context::FieldAccess,
                            source: expr.node(),
                        });
                        Type::Unknown
                    }
                };
                (errors, field_type, None, stop_proof)
            }
        }
    }

    /// Checks that the given function-call is valid
    ///
    /// Returns a few things: (1) any errors, (2) the return type of the function, (3) the name of
    /// the temporary variable given to that return, if applicable, and (4) whether any errors were
    /// so significant as to warrant forgoing any further proof checking.
    #[rustfmt::skip]
    fn check_fn_call_expr(
        &'a self,
        prover: Option<&mut WrappedProver<'a>>,
        fn_expr: &'a Expr<'a>,
        args: &'a FnArgs<'a>,
        enclosing_expr: &'a Expr<'a>,
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, bool) {
        use error::Context::{Expr as ExprCtx, FnArg as FnArgCtx};
        use error::Kind::{FunctionMustBeName, FunctionNotFound, IncorrectNumberOfArgs, FailedProofs, TypeMismatch};

        // The source for the first few errors. This is here so that we can slightly reduce the
        // visual noise from error handling
        let source = fn_expr.node();

        // 1. Check that the function we're trying to call is a name
        let name = match &fn_expr.kind {
            ExprKind::Named(name) => name.name,
            _ => return (
                vec![Error { kind: FunctionMustBeName, context: ExprCtx, source }],
                Type::Unknown,
                None,
                true,
            )
        };

        // 2. Check that the the name is actually a function
        let func = match self.get_fn(name) {
            Some(f) => f,
            None => return (
                vec![Error { kind: FunctionNotFound, context: ExprCtx, source }],
                Type::Unknown,
                None,
                true,
            )
        };

        // 3. Check that we're using the right number of parameters
        if func.params.len() != args.len() {
            return (
                vec![Error {
                    kind: IncorrectNumberOfArgs {
                        n_given: args.len(),
                        n_expected: func.params.len(),
                    },
                    context: ExprCtx,
                    source: ast::Node::Args(&args),
                }],
                Type::Unknown,
                None,
                true,
            );
        }

        let mut errors = Vec::new();
        let mut stop_proof = false;
        split_prover!(prover);

        // 4. Produce a list of the current name + type for each argument, along with checking that
        //    they produce the correct types
        let cons_args: Vec<(Option<Ident>, Type)> = args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let (arg_errs, arg_type, tmp_ident, stop) = self.check_expr(prover!(), arg);
                errors.extend(arg_errs);
                stop_proof = stop_proof || stop;

                if &arg_type != func.params[i].1 {
                    // If there's a type error, we can't guarantee anything about proof beyond this
                    // point in the function
                    stop_proof = true;

                    errors.push(Error {
                        kind: TypeMismatch {
                            expected: vec![func.params[i].1.clone()],
                            found: arg_type.clone(),
                        },
                        context: error::Context::FnArg,
                        source: args[i].node(),
                    });
                }

                (tmp_ident, arg_type)
            })
            .collect();

        // 5. Generate a temp variable for later use, because we'll need to add it to `subs`
        //
        // We only generate an output variable if the return type is an integer
        let output_tmp_var = if let Some(p) = prover!() {
            match func.ret.typ {
                Type::Int | Type::UInt => Some(unsafe { p.gen_new_tmp(enclosing_expr) }),
                _ => None,
            }
        } else { None };

        // 6. If it still makes sense to, try to prove whatever requirements might exist.
        if func.reqs.is_none() {
            stop_proof = true;
        }

        let mut subs = func.params.iter().zip(cons_args.iter()).filter_map(|((x, _), (with, _))| {
            with.clone().map(|with| (Ident::clone(x), proof::Expr::from(with)))
        }).collect::<Vec<(Ident, proof::Expr)>>();

        if let Some(v) = output_tmp_var.clone() {
            // FIXME: This shouldn't just be a random string; it should be defined as a constant
            // somewhere.
            let x = Ident { name: "_", source: IdentSource::Token(&FAKE_TOKEN) };
            subs.push((x, proof::Expr::from(v)));
        };

        let subs = subs.iter().map(|(x, with)| (x, with)).collect::<Vec<_>>();

        let mut failed_reqs: Vec<(ProofResult, Requirement)> = Vec::new();
        if let (false, Some(p), Some(reqs)) = (stop_proof, prover!(), func.reqs.as_ref()) {
            // Try to prove all of the requirements
            for req in reqs {
                let req = req.substitute_all(&subs);
                let res = p.prove(&req);
                if res != ProofResult::True {
                    failed_reqs.push((res, req));
                }
            }
        }

        if !failed_reqs.is_empty() {
            errors.push(Error {
                kind: FailedProofs {
                    failed: failed_reqs,
                    fn_name: name,
                    func_info: func,
                },
                context: FnArgCtx,
                source: enclosing_expr.node(),
            })
        }

        // 6. Final steps:
        //   (a) Get our temp variable to use for the result of this function call
        //   (b) Check all contracts, and apply them if they are valid
        
        if func.contracts.is_none() {
            stop_proof = true;
        }

        if let (false, Some(p), Some(contracts)) = (stop_proof, prover!(), func.contracts.as_ref()) {
            let addition = contracts.iter().filter_map(|(pre, post)| {
                match pre {
                    // It's worth noting that the substitution of the return variable is included
                    // in `subs`, so the post-conditions are translated into the current set of
                    // temporary variables
                    Some(req) => match p.prove(&req.substitute_all(&subs)) {
                        ProofResult::True => Some(post.substitute_all(&subs)),
                        _ => None,
                    }
                    None => Some(post.substitute_all(&subs)),
                }
            }).collect::<Vec<_>>();

            p.add_reqs(addition);
        }

        // And we're done!

        (errors, func.ret.typ.clone(), output_tmp_var, stop_proof)
    }

    /// Checks an assignment operation, returning any errors encountered and whether any were so
    /// significant as to warrant forgoing further proof checking.
    fn check_assign(
        &'a self,
        prover: Option<&mut WrappedProver<'a>>,
        ident: &'a Ident<'a>,
        expr: &'a Expr<'a>,
    ) -> (Vec<Error<'a>>, bool) {
        split_prover!(prover);

        let (mut errors, expr_type, tmp_ident, expr_stop_proof) = self.check_expr(prover!(), expr);

        let stop_proof = match self.get(ident.name) {
            Some(item) if item.typ != expr_type => {
                errors.push(Error {
                    kind: error::Kind::TypeMismatch {
                        expected: vec![item.typ.clone()],
                        found: expr_type.clone(),
                    },
                    context: error::Context::Assign,
                    source: ident.node(),
                });
                true
            }
            Some(_) => match (prover!(), tmp_ident) {
                (Some(p), Some(id)) => {
                    p.define(ident.clone(), id.into());
                    false
                }
                // If we aren't given anything to reference due to the assignment, we want to be
                // sure that this value *is* properly overwritten, so we shadow it.
                (Some(p), None) => {
                    p.shadow(ident.clone());
                    false
                }
                _ => false,
            },
            None => {
                errors.push(Error {
                    kind: error::Kind::VariableNotFound,
                    context: error::Context::Assign,
                    source: ident.node(),
                });
                true
            }
        };

        (errors, expr_stop_proof || stop_proof)
    }

    /// Checks that the given block is valid within its scope
    fn check_block(
        &'a self,
        prover: Option<&mut WrappedProver<'a>>,
        block: &'a Block<'a>,
        start: usize,
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, bool) {
        use StmtKind::{Assign, Eval, Let, Print};

        split_prover!(prover);

        let mut errors: Vec<Error> = Vec::new();
        let mut stop_proof = false;

        // Check the statements from `start`
        for idx in start..block.body.len() {
            let stmt = &block.body[idx];

            let prover = move || match stop_proof {
                true => None,
                false => prover!(),
            };
            
            match &stmt.kind {
                Eval(expr) | Print(expr) => {
                    let (errs, _typ, _tmp_var, stop) = self.check_expr(prover(), expr);
                    errors.extend(errs);
                    stop_proof = stop || stop_proof;
                }
                Assign(name, expr) => {
                    let (errs, stop) = self.check_assign(prover(), name, expr);
                    errors.extend(errs);
                    stop_proof = stop || stop_proof;
                },

                Let(name, expr) => {
                    let (errs, typ, tmp_var, stop) = self.check_expr(prover(), expr);
                    errors.extend(errs);
                    stop_proof = stop || stop_proof;

                    if let (Some(p), false) = (prover(), stop_proof) {
                        if let (Some(t), true) = (tmp_var, typ == Type::Int || typ == Type::UInt) {
                            p.define(name.clone(), t.into());
                        } else {
                            p.shadow(name.clone());
                        };
                    };

                    let new_scope = self.child(ScopeItem {
                        name: name.name,
                        typ,
                        source: Some(stmt.node()),
                    });

                    // Check the remainder of this block with the new scope, then return.
                    let prover = match stop_proof {
                        true => None,
                        // The transmute here is in order to artifically reduce the lifetime of
                        // `prover`
                        false => unsafe { transmute(prover()) },
                    };

                    let (mut errs, end_type, end_tmp_var, stop) =
                        new_scope.check_block(prover, block, idx + 1);

                    // We reverse the errors here because otherwise there'd be an (erroneous)
                    // borrow-checker conflict on the final return in this function -- outside of
                    // this block -- because `errors` references `new_scope` only in this block.
                    errs.extend(errors);

                    let errs: Vec<Error<'a>> = unsafe { transmute(errs) };
                    let end_type: Type<'a> = unsafe { transmute(end_type) };
                    let end_tmp_var: Option<Ident<'a>> = unsafe { transmute(end_tmp_var) };
                    
                    return (errs, end_type, end_tmp_var, stop || stop_proof);
                }
            }
        }

        let (tail_errors, tail_type, tail_tmp_var, stop) = self.check_expr(prover!(), &block.tail);
        errors.extend(tail_errors);

        (errors, tail_type, tail_tmp_var, stop || stop_proof)
    }
}
