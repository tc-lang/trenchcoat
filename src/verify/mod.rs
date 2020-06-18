pub mod error;
mod prover;

use crate::ast::proof::Stmt as ProofStmt;
use crate::ast::{
    BinOp, Block, Expr, ExprKind, FnArgs, Ident, IdentSource, Item, ItemKind, Node, PrefixOp,
    StmtKind, TypeExpr,
};
use crate::proof::{self, ProofResult, Requirement};
use crate::tokens::FAKE_TOKEN;
use crate::types::{self, Type};
use error::Error;
use prover::{Mask, ProverSetItem, Provers};
use std::collections::HashMap;
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
    /// some (optional) set of requirements on the input, the output requirement will be satisfied.
    ///
    /// These are checked whenever they are used in order to provide additional information about
    /// variables created by any callers of this function.
    ///
    /// Like `reqs`, `contracts` will be `None` if there was an error in validating them.
    contracts: Option<Vec<Contract<'a>>>,

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

/// A helper type for `Func`, storing a single proof contract and some contextual information
///
/// The two `Node`s provide additional context to the pre- and post-conditions, respectively.
#[derive(Debug, Clone)]
struct Contract<'a> {
    pre: Vec<Requirement<'a>>,
    // If there aren't any preconditions, the source will be `None`.
    pre_source: Option<Node<'a>>,
    post: Vec<Requirement<'a>>,
    post_source: Node<'a>,
}

/// The top level scope consists of named items, currently just functions. Things will be
/// transitioned out of here as they can be placed in local scopes until everything is under
/// the `Scope` type. It exists now for simplicity.
struct TopLevelScope<'a> {
    // A map of function names to information about them
    //
    // The information about a function will be an `Err` if there are duplicate definitions. The
    // error case provides the source of the first definition of the function.
    items: HashMap<&'a str, Result<Func<'a>, &'a Item<'a>>>,
    errors: Vec<Error<'a>>,

    // A set of provers that's stored so that the errors can reference the strings stored in the
    // provers. This *must* be dropped after `errors`.
    provers: Vec<Provers<'a>>,
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
    top_level: &'a HashMap<&'a str, Result<Func<'a>, &'a Item<'a>>>,
}

/// A single scope item; a variable and its type
#[derive(Debug, Clone)]
struct ScopeItem<'a> {
    name: &'a str,
    typ: Type<'a>,
    source: Option<Node<'a>>,
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

            let params: Vec<_> = params
                .iter()
                .map(|&(ref name, ref ty)| (name, ty))
                .collect();

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

            if let Some(conflict) = top.items.insert(name.name, Ok(func)) {
                let fst_source = conflict.map(|c| c.source).unwrap_or_else(|source| source);
                top.items.insert(name.name, Err(fst_source));

                top.errors.push(Error {
                    kind: error::Kind::ItemConflict(fst_source, item),
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
    ) -> Result<(Vec<Requirement<'a>>, Vec<Contract<'a>>), Vec<Error<'a>>> {
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
        ) -> Vec<Error<'b>> {
            use crate::ast::proof::LogicOp::{And, Or};

            match &cond.kind {
                ConditionKind::Compound {
                    ref lhs,
                    op: And,
                    ref rhs,
                } => {
                    let mut lhs_errs =
                        check_condition(lhs, allowed_return_ident, params, required_return_int);
                    let rhs_errs =
                        check_condition(rhs, allowed_return_ident, params, required_return_int);
                    lhs_errs.extend(rhs_errs);
                    lhs_errs
                }
                ConditionKind::Compound { op: Or, .. } => vec![Error {
                    kind: error::Kind::FeatureNotAllowed {
                        description: "Logical OR is currently not allowed in proof statements",
                    },
                    context: error::Context::ProofStmt,
                    source: cond.node(),
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
        let mut contracts = <Vec<self::Contract>>::new();

        for stmt in stmts {
            match &stmt.kind {
                Require(ref cond) => {
                    errors.extend(check_condition(
                        cond,
                        false,
                        params,
                        &mut required_return_int,
                    ));
                    reqs.extend(Vec::from(cond));
                    // reqs.push(cond.into());
                }
                Contract { pre, ref post } => {
                    errors.extend(
                        pre.as_ref()
                            .map(|c| check_condition(c, false, params, &mut required_return_int))
                            .unwrap_or(vec![]),
                    );
                    errors.extend(check_condition(
                        post,
                        true,
                        params,
                        &mut required_return_int,
                    ));
                    contracts.push(self::Contract {
                        pre: pre.as_ref().map(Vec::from).unwrap_or_default(),
                        pre_source: pre.as_ref().map(|p| p.node()),
                        post: Vec::from(post),
                        post_source: post.node(),
                    });
                }
                &StmtKind::Malformed => panic!("Unexpected malformed proof statment in `verify`"),
            }
        }

        // If we require that the return type is an integer, but it isn't, we'll add that to the
        // list of errors.
        if required_return_int {
            match &ret_ty.typ {
                Type::Int | Type::UInt | Type::Poisoned => (),
                _ => errors.push(Error {
                    kind: error::Kind::TypeMismatch {
                        expected: vec![Type::Int, Type::UInt],
                        found: ret_ty.typ.clone(),
                    },
                    context: error::Context::ProofStmt,
                    source: Node::Item(source_item),
                }),
            }
        }

        match errors.is_empty() {
            true => Ok((reqs, contracts)),
            false => Err(errors),
        }
    }

    /// Verify that each individual item (read: currently only functions) is valid.
    fn check_items(&'a mut self) {
        for (name, func) in self.items.iter() {
            if let Ok(func) = func {
                let (provers, errs) = TopLevelScope::check_fn(name, func, &self.items);
                self.errors.extend(errs);
                self.provers.push(provers);
            }
        }
    }

    /// Given pieces of a `TopLevelScope`, this checks the body of the function and returns any
    /// errors found
    ///
    /// Note that the returned errors may reference the provers given. As such, it should be
    /// guaranteed by the caller that the errors are dropped first.
    fn check_fn(
        name: &'a str,
        func: &'a Func<'a>,
        items: &'a HashMap<&'a str, Result<Func<'a>, &'a Item<'a>>>,
    ) -> (Provers<'a>, Vec<Error<'a>>) {
        let mut prover_set = match (func.reqs.as_ref(), func.contracts.as_ref()) {
            (Some(reqs), Some(contracts)) => {
                // NOTE: This section could be optimized to group by precondition, which would
                // reduce the number of provers. The current version is probably *good enough* as
                // is, so this has been left to some future improvement.

                let mut provers = Vec::with_capacity(1 + contracts.len());
                // Add the base prover
                provers.push(ProverSetItem::new(reqs, &[], None, &[], None));

                // And now the provers for each contract
                for c in contracts {
                    provers.push(ProverSetItem::new(
                        reqs,
                        &c.pre,
                        c.pre_source,
                        &c.post,
                        Some(c.post_source),
                    ));
                }

                Provers::new(provers)
            }
            _ => {
                let mut ps = Provers::new(vec![ProverSetItem::new(&[], &[], None, &[], None)]);
                *ps.mask_mut() = Mask::all(ps.size());
                ps
            },
        };

        // Create a scope containing all the function arguments
        let empty;
        let mut scopes;
        let provers: &mut Provers = &mut prover_set;

        let (mut errors, tail_type, ret_ident, mut mask) = if func.params.is_empty() {
            // If there aren't any, then this is just an empty scope.
            empty = Scope {
                item: None,
                parent: None,
                top_level: items,
            };
            // Intentional lifetime shrinking so that the prover doesn't require the scope to have
            // a longer lifetime
            let provers: &mut Provers = unsafe { transmute(provers) };

            empty.check_block(provers, func.block, 0)
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
            let provers: &mut Provers = unsafe { transmute(provers) };

            scopes.last().unwrap().check_block(provers, func.block, 0)
        };

        if !tail_type.is_poisoned() && tail_type != func.ret.typ {
            errors.push(Error {
                kind: error::Kind::TypeMismatch {
                    expected: vec![func.ret.typ.clone()],
                    found: tail_type.clone(),
                },
                context: error::Context::FnTail,
                source: func.block.tail.node(),
            })
        }

        // Finally - assuming we didn't have any serious errors from before, we'll check that the
        // contracts are upheld.
        if let (Some(ret_ident), true) = (ret_ident, errors.is_empty()) {
            mask |= prover_set.get_mask();
            for (_, p) in prover_set.iter().enumerate().filter(|(i,_)| mask.allows(*i)) {
                let return_ident = Ident {
                    name: "_",
                    source: IdentSource::Token(&FAKE_TOKEN),
                };

                let failed_reqs = p.post.iter().filter_map(|req| {
                    let res = p.prove_return(req, ret_ident.clone());
                    if res == ProofResult::True {
                        return None;
                    }

                    Some((res, req.substitute(&return_ident, &ret_ident.clone().into())))
                }).collect::<Vec<_>>();

                if !failed_reqs.is_empty() {
                    errors.push(Error {
                        kind: error::Kind::FailedContract {
                            fn_name: name,
                            failed: failed_reqs,
                            pre_source: p.pre_source.clone(),
                            post_source: p.post_source.clone().unwrap(),
                            ret_ident: ret_ident.clone(),
                        },
                        context: error::Context::FnTail,
                        source: func.source.node(),
                    });
                }
            }
        }

        // Lifetime extension. This cirucmvents what would be a reliance on borrowed data in
        // `scopes` and `empty`. The reason it's safe to extend the lifetime is because the
        // generated errors don't reference the data *owned* by the two values in this scope, but
        // the things *they* reference.
        unsafe { (prover_set, transmute(errors as Vec<Error>)) }
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
    fn get_fn(&'a self, name: &str) -> Option<&'a Result<Func<'a>, &'a Item<'a>>> {
        self.top_level.get(name)
    }

    /// Checks that the given type is an integer type (either `Int` or `UInt`), and returns a
    /// `TypeMismatch` error with no context if not.
    fn integer_check(t: &Type<'a>, source: Node<'a>) -> Option<Error<'a>> {
        // If the type was already poisoned, we won't return any error here - that would distract
        // from the *actual* error.
        if t == &Type::Int || t == &Type::UInt || t == &Type::Poisoned {
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
    fn bool_check(t: &Type<'a>, source: Node<'a>) -> Option<Error<'a>> {
        // If the type was already poisoned, we won't return any error here - that would distract
        // from the *actual* error.
        match t {
            Type::Bool | Type::Poisoned => None,
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
        provers: &mut Provers<'a>,
        lhs: &'a Expr<'a>,
        op: BinOp,
        rhs: &'a Expr<'a>,
        enclosing_expr: &'a Expr<'a>,
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, Mask) {
        use BinOp::{Add, And, Div, Eq, Ge, Gt, Le, Lt, Mul, Or, Sub};

        // The first thing we'll do is to check both sides of the expression

        let (mut errors, lhs_ty, lhs_tmp_var, lhs_stop) = self.check_expr(provers, lhs);
        let (rhs_errs, rhs_ty, rhs_tmp_var, rhs_stop) = self.check_expr(provers, rhs);
        errors.extend(rhs_errs);

        // And now we check the types, adding on any errors that we find
        let mut has_type_errs = match (&lhs_ty, &rhs_ty) {
            (Type::Poisoned, _) | (_, Type::Poisoned) => true,
            _ => false,
        };

        let output_type = match has_type_errs {
            true => Type::Poisoned,
            false => match op {
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
            },
        };

        let same_type_err = match has_type_errs {
            true => None,
            // We only want to check that the right-hand side has the same type as the left if the
            // types are actually valid
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
            Some(unsafe { provers.gen_new_tmp(enclosing_expr) })
        } else {
            None
        };

        // Finally, if the types and operator are compatible with doing so, we'll add definitions
        // into the prover in order to account for the basic arithmetic operations.
        if let (Some(t), Some(lhs), Some(rhs)) =
            (out_tmp.clone(), lhs_tmp_var, rhs_tmp_var)
        {
            use crate::proof::Expr::{Neg, Prod, Recip, Sum};

            match op {
                Add => {
                    let expr = Sum(vec![lhs.into(), rhs.into()]);
                    provers.define(t, expr);
                }
                Sub => {
                    let expr = Sum(vec![lhs.into(), Neg(Box::new(rhs.into()))]);
                    provers.define(t, expr);
                }
                Mul => {
                    let expr = Prod(vec![lhs.into(), rhs.into()]);
                    provers.define(t, expr);
                }
                Div => {
                    // FIXME: @Jacob - Is the boolean value in `Recip` correct here?
                    let expr = Prod(vec![lhs.into(), Recip(Box::new(rhs.into()), false)]);
                    provers.define(t, expr);
                }
                _ => (),
            }
        }

        let type_errs_mask = match has_type_errs {
            true => Mask::all(provers.size()),
            false => Mask::none(provers.size()),
        };

        (
            errors,
            output_type,
            out_tmp,
            lhs_stop | rhs_stop | type_errs_mask,
        )
    }

    fn check_prefix_op_expr(
        &'a self,
        provers: &mut Provers<'a>,
        op: PrefixOp,
        rhs: &'a Expr<'a>,
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, Mask) {
        use PrefixOp::Not;

        let (mut errors, typ, _tmp_var, stop_proof) = self.check_expr(provers, rhs);

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
        provers: &mut Provers<'a>,
        expr: &'a Expr<'a>,
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, Mask) {
        use ExprKind::{
            BinOp, Bracket, Empty, FieldAccess, FnCall, Malformed, Named, Num, PrefixOp, Struct,
        };

        match &expr.kind {
            BinOp(lhs, op, rhs) => self.check_bin_op_expr(provers, lhs, *op, rhs, expr),
            FnCall(fn_expr, args) => self.check_fn_call_expr(provers, fn_expr, args, expr),
            Empty => (
                Vec::new(),
                types::empty_struct(),
                None,
                Mask::none(provers.size()),
            ),
            // the error will have already been raised
            Malformed => (Vec::new(), Type::Poisoned, None, Mask::all(provers.size())),
            Bracket(block) => self.check_block(provers, &block, 0),
            // (Overflows will be handled when the int is
            //  parsed? If the interpreter is going to parse
            //  from the AST then we can validate here for
            //  now.)
            Num(n) => {
                use crate::proof::{
                    expr::{Atom, Expr},
                    int::{Int, Rational},
                };

                let tmp = {
                    let t = unsafe { provers.gen_new_tmp(expr) };
                    provers.define(
                        t.clone(),
                        Expr::Atom(Atom::Literal(Rational {
                            numerator: (*n as i128).into(),
                            denominator: Int::ONE,
                        })),
                    );
                    t
                };

                (Vec::new(), Type::Int, Some(tmp), Mask::none(provers.size())) // Woo! No errors here!
            }
            PrefixOp(op, inner_expr) => self.check_prefix_op_expr(provers, *op, inner_expr),
            Named(name) => match self.get(name.name) {
                Some(item) => (
                    Vec::new(),
                    item.typ.clone(),
                    Some(name.clone()),
                    Mask::none(provers.size()),
                ),
                None => (
                    vec![Error {
                        kind: error::Kind::VariableNotFound,
                        context: error::Context::Expr,
                        source: expr.node(),
                    }],
                    Type::Poisoned,
                    None,
                    Mask::all(provers.size()),
                ),
            },
            // Note: Currently proof doesn't carry through struct fields
            Struct(fields) => {
                let mut errors = Vec::new();
                let mut mask = Mask::none(provers.size());

                let field_types = fields
                    .iter()
                    .map(|(name, expr)| {
                        let (expr_errors, typ, _tmp_ident, new_mask) =
                            self.check_expr(provers, expr);
                        mask |= new_mask;
                        errors.extend(expr_errors);

                        types::StructField {
                            name: name.clone(),
                            typ,
                        }
                    })
                    .collect();

                (errors, Type::Struct(field_types), None, mask)
            }
            FieldAccess(expr, field_ident) => {
                let (mut errors, expr_type, _tmp_ident, stop_proof) =
                    self.check_expr(provers, expr);
                let fields = match &expr_type {
                    Type::Struct(fields) => fields,
                    _ => {
                        errors.push(Error {
                            kind: error::Kind::AccessFieldOnNotStruct,
                            context: error::Context::FieldAccess,
                            source: expr.node(),
                        });
                        return (errors, Type::Poisoned, None, stop_proof);
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
                        Type::Poisoned
                    }
                };
                (errors, field_type, None, stop_proof)
            }
        }
    }

    /// Checks that the given function-call is valid
    ///
    /// Returns a few things: (1) any errors, (2) the return type of the function, (3) the name of
    /// the temporary variable given to that return, if applicable, and (4) a mask over the set of
    /// provers to stop them if there were any errors so significant as to warrant stopping proof
    #[rustfmt::skip]
    fn check_fn_call_expr(
        &'a self,
        provers: &mut Provers<'a>,
        fn_expr: &'a Expr<'a>,
        args: &'a FnArgs<'a>,
        enclosing_expr: &'a Expr<'a>,
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, Mask) {
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
                Type::Poisoned,
                None,
                Mask::all(provers.size()),
            )
        };

        // 2. Check that the the name is actually a function
        let func = match self.get_fn(name) {
            Some(Ok(f)) => f,
            // If there's a conflict, we'll simply return - we can't make meaningful errors here
            Some(Err(_)) => return (Vec::new(), Type::Poisoned, None, Mask::all(provers.size())),
            None => return (
                vec![Error { kind: FunctionNotFound { name }, context: ExprCtx, source }],
                Type::Poisoned,
                None,
                Mask::all(provers.size()),
            )
        };

        // 3. Check that we're using the right number of parameters
        if func.params.len() != args.len() {
            return (
                vec![Error {
                    kind: IncorrectNumberOfArgs {
                        given: args.len(),
                        func,
                    },
                    context: ExprCtx,
                    source: Node::Args(&args),
                }],
                Type::Poisoned,
                None,
                Mask::all(provers.size()),
            );
        }

        let mut errors = Vec::new();
        let mut mask = Mask::none(provers.size());

        // 4. Produce a list of the current name + type for each argument, along with checking that
        //    they produce the correct types
        //    
        //    If there are any type errors, we won't do any proof
        let cons_args: Vec<(Option<Ident>, Type)> = args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let (arg_errs, arg_type, tmp_ident, new_mask) = self.check_expr(provers, arg);
                errors.extend(arg_errs);
                mask |= new_mask;

                if arg_type.is_poisoned() {
                    // There's a type error in something that produced this expression, so there's
                    // no point in trying to do proof
                    mask = Mask::all(provers.size());
                } else if &arg_type != func.params[i].1 {
                    // If there's a type error, we can't guarantee anything about proof beyond this
                    // point in the function
                    mask = Mask::all(provers.size());

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
        let output_tmp_var = match func.ret.typ {
            Type::Int | Type::UInt => Some(unsafe { provers.gen_new_tmp(enclosing_expr) }),
            _ => None,
        };

        // 6. If it still makes sense to, try to prove whatever requirements might exist.
        if func.reqs.is_none() {
            mask = Mask::all(provers.size());
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

        // All/any of the proof statments that are strictly required to call this function.
        let mut failed_reqs: Vec<(ProofResult, Requirement)> = Vec::new();
        if let Some(reqs) = func.reqs.as_ref() {
            // The "base prover" -- the one with no assumptions - is given to be index 0, because
            // of how we originally construct it. We only actually want to prove that it's true
            // with this one, because (1) it'll then be true for all the others and (2) the others
            // will most likely just have duplicate error messages
            let base_prover = &provers[0];

            // Try to prove all of the requirements
            for req in reqs {
                let req = req.substitute_all(&subs);
                let res = base_prover.prove(&req);
                if res != ProofResult::True {
                    failed_reqs.push((res, req));
                }
            }
        }
        
        let did_fail = !failed_reqs.is_empty();

        if did_fail {
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
            mask = Mask::all(provers.size());
        }

        if let (false, Some(contracts)) = (did_fail, func.contracts.as_ref()) {
            let mut reqs = vec![Vec::new(); provers.size()];

            for c in contracts.iter() {
                let post = c.post.iter().map(|req| req.substitute_all(&subs)).collect::<Vec<_>>();
                let pre = c.pre.iter().map(|rs| rs.substitute_all(&subs)).collect::<Vec<_>>();

                provers.prove_all(&pre).into_iter().filter(|(_, passed)| *passed).for_each(|(i,_)| {
                    reqs[i].extend(post.clone());
                });
            }

            for (p, rs) in provers.iter_mut().zip(reqs) {
                p.add_reqs(rs);
            }
        }

        // And we're done!

        (errors, func.ret.typ.clone(), output_tmp_var, mask)
    }

    /// Checks an assignment operation, returning any errors encountered and whether any were so
    /// significant as to warrant forgoing further proof checking.
    fn check_assign(
        &'a self,
        provers: &mut Provers<'a>,
        ident: &'a Ident<'a>,
        expr: &'a Expr<'a>,
    ) -> (Vec<Error<'a>>, Mask) {
        let (mut errors, expr_type, tmp_ident, expr_mask) = self.check_expr(provers, expr);

        let mask = match self.get(ident.name) {
            Some(item) if item.typ != expr_type => {
                errors.push(Error {
                    kind: error::Kind::TypeMismatch {
                        expected: vec![item.typ.clone()],
                        found: expr_type.clone(),
                    },
                    context: error::Context::Assign,
                    source: ident.node(),
                });
                Mask::all(provers.size())
            }
            Some(_) => match tmp_ident {
                Some(id) => {
                    provers.define(ident.clone(), id.into());
                    Mask::none(provers.size())
                }
                // If we aren't given anything to reference due to the assignment, we want to be
                // sure that this value *is* properly overwritten, so we shadow it.
                None => {
                    provers.shadow(ident.clone());
                    Mask::none(provers.size())
                }
                _ => Mask::none(provers.size()),
            },
            None => {
                errors.push(Error {
                    kind: error::Kind::VariableNotFound,
                    context: error::Context::Assign,
                    source: ident.node(),
                });
                Mask::all(provers.size())
            }
        };

        (errors, expr_mask | mask)
    }

    /// Checks that the given block is valid within its scope
    fn check_block(
        &'a self,
        provers: &mut Provers<'a>,
        block: &'a Block<'a>,
        start: usize,
    ) -> (Vec<Error<'a>>, Type<'a>, Option<Ident<'a>>, Mask) {
        use StmtKind::{Assign, Eval, Let, Print};

        let original_mask = provers.get_mask();

        let mut errors: Vec<Error> = Vec::new();

        // Check the statements from `start`
        for idx in start..block.body.len() {
            let stmt = &block.body[idx];

            match &stmt.kind {
                Eval(expr) | Print(expr) => {
                    let (errs, _typ, _tmp_var, expr_mask) = self.check_expr(provers, expr);
                    errors.extend(errs);
                    *provers.mask_mut() |= expr_mask;
                }
                Assign(name, expr) => {
                    let (errs, ass_mask) = self.check_assign(provers, name, expr);
                    errors.extend(errs);
                    *provers.mask_mut() |= ass_mask;
                }

                Let(name, expr) => {
                    let (errs, typ, tmp_var, let_mask) = self.check_expr(provers, expr);
                    errors.extend(errs);
                    *provers.mask_mut() |= let_mask;

                    if let (Some(t), true) = (tmp_var, typ == Type::Int || typ == Type::UInt) {
                        provers.define(name.clone(), t.into());
                    } else {
                        provers.shadow(name.clone());
                    };

                    let new_scope = self.child(ScopeItem {
                        name: name.name,
                        typ,
                        source: Some(stmt.node()),
                    });

                    // Check the remainder of this block with the new scope, then return.
                    //
                    // The transmute here is in order to artifically reduce the lifetime of
                    // `provers`
                    let provers: &mut Provers = unsafe { transmute(provers) };

                    let (mut errs, end_type, end_tmp_var, end_mask) =
                        new_scope.check_block(provers, block, idx + 1);

                    // We reverse the errors here because otherwise there'd be an (erroneous)
                    // borrow-checker conflict on the final return in this function -- outside of
                    // this block -- because `errors` references `new_scope` only in this block.
                    errs.extend(errors);

                    // And now we extend the lifetimes of all of the return values past that of
                    // `new_scope`
                    let errs: Vec<Error<'a>> = unsafe { transmute(errs) };
                    let end_type: Type<'a> = unsafe { transmute(end_type) };
                    let end_tmp_var: Option<Ident<'a>> = unsafe { transmute(end_tmp_var) };

                    *provers.mask_mut() = original_mask;

                    return (errs, end_type, end_tmp_var, end_mask);
                }
            }
        }

        let (tail_errors, tail_type, tail_tmp_var, expr_mask) =
            self.check_expr(provers, &block.tail);
        errors.extend(tail_errors);

        let mask = provers.get_mask() | expr_mask;
        *provers.mask_mut() = original_mask;

        (errors, tail_type, tail_tmp_var, mask)
    }
}
