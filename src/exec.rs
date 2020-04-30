//! Handling of code execution; where interpreting actually happens
//!
//! This occurs in two parts: First, by generating the global scope with [`generate_global_scope`],
//! and then by calling [`GlobalScope::exec`] to actually run the code.
//!
//! [`generate_global_scope`]: fn.generate_global_scope.html
//! [`GlobalScope::exec`]: struct.GlobalScope.html#method.exec
// NOTE: Quick-fix implementation details that *will* be changed in the future
// are marked with "@QUICK-FIX". These should be removed in the process of
// polishing this initial version of the interpreter.

use crate::ast::{
    BinOp, Block, Expr, ExprKind, FnArgs, FnParams, Ident, Item, ItemKind, PrefixOp, Stmt, StmtKind,
};
use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

pub struct GlobalScope<'a> {
    funcs: HashMap<String, Func<'a>>,
}

struct LocalScope<'a> {
    parent: ParentScope<'a>,
    // Ideally these would be &'a str, but we run into borrowck issues if we try to do that.
    variables: HashMap<String, Value>,
}

struct Func<'a> {
    params: FnParams<'a>,
    body: Block<'a>,
}

type Value = usize;

enum ParentScope<'a> {
    Global(&'a GlobalScope<'a>),
    // Damn borrow checker :(
    Local(Rc<RefCell<LocalScope<'a>>>),
}

/// Generates the global scope of functions (with their attached bodies) from the list of items
pub fn generate_global_scope<'a>(items: Vec<Item<'a>>) -> GlobalScope<'a> {
    let mut global = GlobalScope {
        funcs: HashMap::new(),
    };

    for item in items.into_iter() {
        match item.kind {
            ItemKind::FnDecl { name, params, body } => {
                // If we've already added a function with this name ot the global scope, we'll
                // panic. We should have already validated that there aren't any name conflicts.
                if global.funcs.contains_key(name.name) {
                    panic!("function {:?} appears twice in the global scope", name);
                }

                global.funcs.insert(name.name.into(), Func { params, body });
            }
        }
    }

    global
}

impl<'a> LocalScope<'a> {
    /// Returns whether this scope or any of its parents have a variable with the given name
    fn has_var(&self, name: &str) -> bool {
        if self.variables.contains_key(name) {
            return true;
        } else if let ParentScope::Local(ref p) = &self.parent {
            return p.borrow().has_var(name);
        }

        false
    }

    /// Gets the variable associated with the given name, searching first in this scope and then in
    /// any parent scopes. If there is no such variable, this function will panic.
    fn get_var(&self, name: &str) -> Value {
        if let Some(&v) = self.variables.get(name) {
            return v;
        } else if let ParentScope::Local(ref p) = &self.parent {
            return p.borrow().get_var(name);
        }

        panic!("no variable {:?} in scope", name);
    }

    fn reassign(&mut self, name: &str, val: Value) {
        if let Some(v) = self.variables.get_mut(name) {
            *v = val;
        } else if let ParentScope::Local(ref p) = &mut self.parent {
            let mut p = p.borrow_mut();
            p.reassign(name, val);
        } else {
            panic!(
                "attempted to reassign to variable {:?}, which not in scope",
                name
            );
        }
    }

    // Notes on `RefCell` usage: this requires that none of the parent scopes are borrowed mutably.
    // This should be *okay* in most cases
    fn get_global(&self) -> *const GlobalScope<'a> {
        match &self.parent {
            &ParentScope::Global(g) => g as *const GlobalScope<'a>,
            ParentScope::Local(ref_cell) => ref_cell.borrow().get_global(),
        }
    }
}

impl<'a> GlobalScope<'a> {
    /// Returns whether the global scope contains a function with the given name
    pub fn contains(&self, fn_name: &str) -> bool {
        self.funcs.contains_key(fn_name)
    }

    /// Returns the number of arguments expected by the function in the global scope with the given
    /// name, if it exists.
    pub fn num_args(&self, fn_name: &str) -> Option<usize> {
        Some(self.funcs.get(fn_name)?.params.len())
    }

    /// Executes the function with the given name in the global scope, yielding the return value of
    /// the function, if present.
    ///
    /// This will panic if no function with the given name exists within the global scope or the
    /// number of arguments does not match the expected number for the function. These can be
    /// checked the [`contains`] and [`num_args`] methods, respectively.
    ///
    /// [`contains`]: #method.contains
    /// [`num_args`]: #method.num_args
    pub fn exec(&self, fn_name: &str, args: Vec<Value>) -> Option<Value> {
        let func = self.funcs.get(fn_name).unwrap_or_else(|| {
            panic!("no function {:?} in the global scope", fn_name);
        });

        if args.len() != func.params.len() {
            panic!(
                "wrong number of arguments to function {:?}; expected {} but found {}",
                fn_name,
                func.params.len(),
                args.len()
            );
        }

        // @QUICK-FIX: The above will need to type check as well.

        func.exec(self, args)
    }
}

impl<'a> Func<'a> {
    /// Executes the function with the given arguments, yielding the return value, if present.
    ///
    /// This will panic if the given number of arguments does not match what is expected
    fn exec(&self, global: &GlobalScope, args: Vec<Value>) -> Option<Value> {
        if args.len() != self.params.len() {
            panic!(
                "wrong number of arguments; expected {} but found {}",
                self.params.len(),
                args.len()
            );
        }

        // @QUICK-FIX: The above will need to type check as well.

        let mut local_scope = LocalScope {
            parent: ParentScope::Global(global),
            variables: HashMap::new(),
        };

        for (v, &Ident { name, .. }) in args.into_iter().zip(self.params.iter()) {
            if local_scope.variables.contains_key(name) {
                // This should have already been validated, but we'll double-check here
                panic!("duplicate argument {:?}", name);
            }

            local_scope.variables.insert(name.into(), v);
        }

        let local = Rc::new(RefCell::new(local_scope));
        exec_block(&self.body, local)
    }
}

/// Executes the block in a new scope (separate from the one it is given), and yields the final
/// value, if it exists.
fn exec_block(block: &Block, containing_scope: Rc<RefCell<LocalScope>>) -> Option<Value> {
    let vars = Rc::new(RefCell::new(LocalScope {
        parent: ParentScope::Local(containing_scope),
        variables: HashMap::new(),
    }));

    for stmt in block.body.iter() {
        exec_stmt(stmt, vars.clone());
    }

    // @QUICK-FIX: Currently we'll allow expressions that don't return values if they're the last
    // value in a block... this should be considered (probably fine) and the rest of the interpeter
    // should be checked that it aligns with that.

    block
        .tail
        .as_ref()
        .and_then(|expr| exec_expr(expr, vars.clone()))
}

fn exec_stmt<'a>(stmt: &Stmt, scope: Rc<RefCell<LocalScope>>) {
    use StmtKind::{Assign, Eval, Let, Print};

    match &stmt.kind {
        Let(Ident { name, .. }, expr) => {
            let val = exec_expr(expr, scope.clone()).unwrap_or_else(|| {
                panic!("expected value; expr yielded `None`");
            });
            scope.borrow_mut().variables.insert((*name).into(), val);
        }
        Assign(Ident { name, .. }, expr) => {
            if !scope.borrow().has_var(name) {
                panic!("assignment to unknown variable {:?}", name);
            }

            let val = exec_expr(expr, scope.clone()).unwrap_or_else(|| {
                panic!("expected value; expr yielded `None`");
            });
            scope.borrow_mut().reassign(name, val);
        }
        Print(expr) => print_value(exec_expr(expr, scope)),
        Eval(expr) => drop(exec_expr(expr, scope)),
    }
}

fn exec_expr(expr: &Expr, scope: Rc<RefCell<LocalScope>>) -> Option<Value> {
    use ExprKind::{BinOp, Bracket, Empty, FnCall, Named, Num, PrefixOp};

    match &expr.kind {
        Empty => None,
        FnCall(fn_expr, args) => exec_fn_call(fn_expr, args, scope),
        BinOp(lhs, op, rhs) => {
            let lhs = exec_expr(lhs, scope.clone()).unwrap_or_else(|| {
                panic!("expected value; expr yielded `None`");
            });

            let rhs = exec_expr(rhs, scope).unwrap_or_else(|| {
                panic!("expected value; expr yielded `None`");
            });

            Some(perform_bin_op(lhs, *op, rhs))
        }
        PrefixOp(op, rhs) => {
            let rhs = exec_expr(rhs, scope).unwrap_or_else(|| {
                panic!("expected value; expr yielded `None`");
            });

            Some(perform_prefix_op(*op, rhs))
        }
        Named(Ident { name, .. }) => Some(scope.borrow().get_var(name)),
        &Num(v) => Some(v),
        Bracket(stmts, expr) => exec_bracket(stmts, expr, scope),
    }
}

/// Executes the function-call expression. Currently this expects `fn_expr.kind` to be an
/// `ExprKind::Named`. It will panic otherwise
// @QUICK-FIX
fn exec_fn_call(fn_expr: &Expr, args: &FnArgs, scope: Rc<RefCell<LocalScope>>) -> Option<Value> {
    let fn_name = match &fn_expr.kind {
        ExprKind::Named(Ident { name, .. }) => name,
        _ => panic!("tried to call non-function expr"),
    };

    let args = args
        .iter()
        .map(|expr| {
            exec_expr(expr, scope.clone()).unwrap_or_else(|| {
                panic!("expected value; expr yielded `None`");
            })
        })
        .collect();

    let s = scope.borrow();
    let global_scope = unsafe { &*s.get_global() };
    global_scope.exec(fn_name, args)
}

fn perform_bin_op(lhs: Value, op: BinOp, rhs: Value) -> Value {
    use BinOp::{Add, And, Div, Eq, Ge, Gt, Le, Lt, Mul, Or, Sub};

    match op {
        Add => lhs + rhs,
        Sub => lhs - rhs,
        Mul => lhs * rhs,
        Div => lhs / rhs,

        // @QUICK-FIX: boolean operators are currently unimplemented
        Eq | Lt | Le | Gt | Ge | Or | And => {
            panic!("boolean operators are currently unimplemented")
        }
    }
}

fn perform_prefix_op(op: PrefixOp, rhs: Value) -> Value {
    use PrefixOp::Not;

    match op {
        // @QUICK-FIX: boolean operators are currently unimplemented
        Not => panic!("boolean operators are currently unimplemented"),
    }
}

fn exec_bracket(
    stmts: &[Stmt],
    expr: &Expr,
    containing_scope: Rc<RefCell<LocalScope>>,
) -> Option<Value> {
    // @QUICK-FIX: copied from `exec_block`
    let vars = Rc::new(RefCell::new(LocalScope {
        parent: ParentScope::Local(containing_scope),
        variables: HashMap::new(),
    }));

    for s in stmts.iter() {
        exec_stmt(s, vars.clone());
    }

    exec_expr(expr, vars.clone())
}

/// An isolated function for printing values so that we can easily change what it does
fn print_value(val: Option<Value>) {
    println!(">> {:?}", val);
}
