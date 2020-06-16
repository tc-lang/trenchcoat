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

/// The value of an expression
///
/// The necessary type information is encoded in the variables used. This type implements `Copy`
/// only so that when it is later removed, it will become clear where the semantics must be
/// changed. Eventually, it will not be possible to perform a bit-wise copy of a `Value` due to
/// adding arrays as types.
#[derive(Clone, Debug)]
pub enum Value {
    /// The unit type, `()`
    ///
    /// This is the implicit return type of functions without an explicit return or an implicitly
    /// returned expression. For example:
    /// ```
    /// fn foo() {
    ///     bar();
    /// }
    /// ```
    /// Here, `foo` has a return type of `()`
    Unit,

    /// A boolean value
    ///
    /// This can currently only be created by binary comparison operators.
    Bool(bool),

    /// An integer value
    ///
    /// These may be created by integer literals or basic arithmetic operators.
    Int(isize),

    /// A struct value. We use a hashmap here for nicer ergonomics of fetching values, given that
    /// performance is not a large concern for this interpreter.
    Struct { fields: HashMap<String, Value> },
}

enum ParentScope<'a> {
    Global(&'a GlobalScope<'a>),
    // Damn borrow checker :(
    Local(Rc<RefCell<LocalScope<'a>>>),
}

impl Value {
    /// Unwraps the `Value` into the inner value of the `Int` variant
    ///
    /// If the value is not of type `Int`, this will panic with the given message.
    fn expect_int(self, panic_msg: impl AsRef<str>) -> isize {
        match self {
            Value::Int(i) => i,
            _ => panic!("{}", panic_msg.as_ref()),
        }
    }

    /// Unwraps the `Value` into the inner value of the `Bool` variant
    ///
    /// If the value is not of type `Bool`, this will panic with the given message.
    fn expect_bool(self, panic_msg: impl AsRef<str>) -> bool {
        match self {
            Value::Bool(b) => b,
            _ => panic!("{}", panic_msg.as_ref()),
        }
    }
}

/// Generates the global scope of functions (with their attached bodies) from the list of items
pub fn generate_global_scope<'a>(items: Vec<Item<'a>>) -> GlobalScope<'a> {
    let mut global = GlobalScope {
        funcs: HashMap::new(),
    };

    for item in items.into_iter() {
        match item.kind {
            ItemKind::FnDecl {
                name, params, body, ..
            } => {
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
        if let Some(v) = self.variables.get(name).cloned() {
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
    /// Returns the number of arguments expected by the function in the global scope with the given
    /// name, if it exists.
    pub fn num_args(&self, fn_name: &str) -> Option<usize> {
        Some(self.funcs.get(fn_name)?.params.len())
    }

    /// Executes the function with the given name in the global scope, yielding the return value of
    /// the function. Functions with no return values give yield [`Value::Unit`]
    ///
    /// This will panic if no function with the given name exists within the global scope or the
    /// number of arguments does not match the expected number for the function. These can be
    /// checked the [`contains`] and [`num_args`] methods, respectively.
    ///
    /// [`Value::Unit`]: enum.Value.html#variant.Unit
    /// [`contains`]: #method.contains
    /// [`num_args`]: #method.num_args
    pub fn exec(&'a self, fn_name: &str, args: Vec<Value>) -> Value {
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
    /// Executes the function with the given arguments, yielding the return value. If there is no
    /// return value, [`Value::Unit`] will be returned.
    ///
    /// This will panic if the given number of arguments does not match what is expected
    ///
    /// [`Value::Unit`]: enum.Value.html#variant.Unit
    fn exec(&self, global: &'a GlobalScope<'a>, args: Vec<Value>) -> Value {
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

        for (v, &(Ident { name, .. }, _)) in args.into_iter().zip(self.params.iter()) {
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
/// value, if it exists. If there is no final expression, [`Value::Unit`] will be returned.
///
/// [`Value::Unit`]: enum.Value.html#variant.Unit
fn exec_block(block: &Block, containing_scope: Rc<RefCell<LocalScope>>) -> Value {
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

    exec_expr(&block.tail, vars.clone())
}

fn exec_stmt<'a>(stmt: &Stmt, scope: Rc<RefCell<LocalScope>>) {
    use StmtKind::{Assign, Eval, Let, Print};

    match &stmt.kind {
        Let(Ident { name, .. }, expr) => {
            let val = exec_expr(expr, scope.clone());
            scope.borrow_mut().variables.insert((*name).into(), val);
        }
        Assign(Ident { name, .. }, expr) => {
            if !scope.borrow().has_var(name) {
                panic!("assignment to unknown variable {:?}", name);
            }

            let val = exec_expr(expr, scope.clone());
            scope.borrow_mut().reassign(name, val);
        }
        Print(expr) => print_value(exec_expr(expr, scope)),
        Eval(expr) => drop(exec_expr(expr, scope)),
    }
}

fn exec_expr(expr: &Expr, scope: Rc<RefCell<LocalScope>>) -> Value {
    use ExprKind::{
        BinOp, Bracket, Empty, FieldAccess, FnCall, Malformed, Named, Num, PrefixOp, Struct,
    };

    match &expr.kind {
        Empty => Value::Unit,
        FnCall(fn_expr, args) => exec_fn_call(fn_expr, args, scope),
        BinOp(lhs, op, rhs) => {
            let lhs = exec_expr(lhs, scope.clone());
            let rhs = exec_expr(rhs, scope);
            perform_bin_op(lhs, *op, rhs)
        }
        PrefixOp(op, rhs) => {
            let rhs = exec_expr(rhs, scope);
            perform_prefix_op(*op, rhs)
        }
        Named(Ident { name, .. }) => scope.borrow().get_var(name),
        &Num(i) => Value::Int(i),
        Bracket(block) => exec_block(block, scope),
        FieldAccess(struct_expr, field) => match exec_expr(struct_expr, scope) {
            Value::Struct { fields } => match fields.get(field.name) {
                Some(v) => v.clone(),
                None => panic!(
                    "No field {:?} in struct value {:?}",
                    field.name,
                    Value::Struct { fields }
                ),
            },
            v => panic!("Expected struct value, found {:?}", v),
        },
        Struct(fields) => {
            let mut fields_map = HashMap::new();

            for (field, expr) in fields {
                fields_map.insert(field.name.into(), exec_expr(expr, scope.clone()));
            }

            Value::Struct { fields: fields_map }
        }
        Malformed => panic!("Malformed expression cannot be evaluated"),
    }
}

/// Executes the function-call expression. Currently this expects `fn_expr.kind` to be an
/// `ExprKind::Named`. It will panic otherwise
// @QUICK-FIX
fn exec_fn_call(fn_expr: &Expr, args: &FnArgs, scope: Rc<RefCell<LocalScope>>) -> Value {
    let fn_name = match &fn_expr.kind {
        ExprKind::Named(Ident { name, .. }) => name,
        _ => panic!("tried to call non-function expr"),
    };

    let args = args
        .iter()
        .map(|expr| exec_expr(expr, scope.clone()))
        .collect();

    let s = scope.borrow();
    let global_scope = unsafe { &*s.get_global() };
    global_scope.exec(fn_name, args)
}

// It should be noted that certain boolean operators that would be expected to short-circuit in
// other languages do not here.
fn perform_bin_op(lhs: Value, op: BinOp, rhs: Value) -> Value {
    use BinOp::{Add, And, Div, Eq, Ge, Gt, Le, Lt, Mul, Or, Sub};
    use Value::{Bool, Int};

    match op {
        // Boolean x Boolean
        Or | And => {
            let lhs = lhs.expect_bool("expected boolean-valued left-hand-side expression");
            let rhs = rhs.expect_bool("expected boolean-valued right-hand-side expression");

            match op {
                Or => Bool(lhs || rhs),
                And => Bool(lhs && rhs),
                _ => unreachable!(),
            }
        }

        // T x T
        Eq => todo!(),

        // Integer x Integer
        _ => {
            let lhs = lhs.expect_int("expected integer-valued left-hand-side expression");
            let rhs = rhs.expect_int("expected integer-valued right-hand-side expression");

            match op {
                Add => Int(lhs + rhs),
                Sub => Int(lhs - rhs),
                Mul => Int(lhs * rhs),
                Div => Int(lhs / rhs),
                Lt => Bool(lhs < rhs),
                Le => Bool(lhs <= rhs),
                Gt => Bool(lhs > rhs),
                Ge => Bool(lhs >= rhs),
                _ => unreachable!(),
            }
        }
    }
}

fn perform_prefix_op(op: PrefixOp, rhs: Value) -> Value {
    match op {
        PrefixOp::Not => {
            let rhs = rhs.expect_bool("expected boolean-valued right-hand-side expression");
            Value::Bool(!rhs)
        }
    }
}

/// An isolated function for printing values so that we can easily change what it does
fn print_value(val: Value) {
    println!(">> {:?}", val);
}
