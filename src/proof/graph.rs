//! The graph-based prover

use super::term::{Inequality, Term};
use super::{ProofResult, Requirement, ScopedSimpleProver, SimpleProver};
use std::mem;

pub type FullProver<'a> = ScopedSimpleProver<'a, Prover>;

#[derive(Clone, Debug)]
pub struct Prover {
    /// The set of expression nodes in the graph, each represented by a sum of terms and edges to
    /// the values they are less than.
    nodes: Vec<Node>,
}

/// A flag for whether the prover should try to split requirements apart if normal proof fails.
///
/// Splitting is extremely simplified. For example: In a case like `x+y+z <= 5`, we would split
/// this into independently determining the upper bounds on each of x, y, and z - in relation to
/// the constant.
///
/// For a more complex example, like `x+y-z <= 5+w`, we first convert this into `x+y-z-w <= 5` and
/// then find the upper bounds on each (including the signs).
///
/// This typically means that the average runtime of the failure case is multiplied by two, as we
/// would be running the standard algorithm once more, checking both whether the requirement is
/// true and whether is it provably false.
///
/// This additional method only really provides a benefit if there's more information given about
/// the variables, so it's recommended to at least enable `DOUBLE_NEGATE_REQS` and `LINK_MUL_COEFS`
/// alongside this flag.
const TRY_SPLITS: bool = true;

/// A flag for whether requirements should be doubled so that their negations are also added (so
/// that upper bounds on `x` provide lower bounds on `-x`)
///
/// This simply duplicates the nodes (and edges) being added to the graph so that we can feed more
/// information into the algorithm.
const DOUBLE_NEGATE_REQS: bool = true;

/// An exhaustive version of `DOUBLE_NEGATE_REQS`: If true, this will exhaustively produce all
/// combinations of terms on either side of the inequality in adding more nodes to the graph.
///
/// This - of course - introduces 2^n total edges for each inequality (where n is the number of
/// terms). In practice, n is exceptionally small, so this is likely not to be an issue.
///
/// This flag is available as an alternative to `DOUBLE_NEGATE_REQS` - if both are present this
/// flag will take priority.
//
// FIXME: There are some cases where only `DOUBLE_NEGATE_REQS` is able to prove something; not this
// flag. Those should be investigated.
const EXHAUSTIVE_REQ_SIDES: bool = false;

/// This feature is more difficult to explain in a single doc comment. For an in-depth explanation,
/// please refer to the writeup.
const LINK_MUL_COEFS: bool = true;

#[derive(Copy, Clone, Debug)]
struct NodeId(usize);

#[derive(Clone, Debug)]
struct Node {
    expr: Vec<Term>,
    // expr <= [NodeId].expr + edge
    less_than: Vec<(Edge, NodeId)>,
}

/// An edge represents the relation between two nodes in the graph
///
/// For two nodes, A and B (each representing a list of terms), an edge from A to B indicates that
/// the following relation holds:
/// `A ≤ B*num/denom + offset`
///
/// Note that `num` and `denom` are both unsigned, meaning that nodes of opposite signs cannot be
/// compared.
#[derive(Copy, Clone, Debug)]
struct Edge {
    offset: i128,
    num: u128,
    denom: u128,
}

impl Prover {
    /// An identical function to `super::Prover::prove`, except this is a helper for the recursion,
    /// which we use to manage attempting to prove the contrapositive.
    fn prove(&self, req: Inequality, recurse: bool) -> ProofResult {
        // Attempts to prove the requirement by finding the path the shortest length from req.lhs
        // to req.rhs
        //
        // This is equivalent to finding the smallest value of C where lhs <= rhs + C still holds.
        // Only if C <= req.constant can we infer that the requirement is satisfied
        // (i.e. lhs <= rhs + constant).
        //
        // Of course, both the left- and right-hand side expressions need to be present in the
        // graph; if they aren't, we'll return that the statement is undetermined.

        // find the starting and ending points of the path through the graph
        let start_node_idx = match self.nodes.iter().position(|n| n.expr == req.lhs) {
            Some(i) => i,
            None if TRY_SPLITS => return self.prove_splits(req.clone(), true),
            None => return ProofResult::Undetermined,
        };

        let end_node_idx = match self.nodes.iter().position(|n| n.expr == req.rhs) {
            Some(i) => i,
            None if TRY_SPLITS => return self.prove_splits(req.clone(), true),
            None => return ProofResult::Undetermined,
        };

        // Generate the distances according to the Bellman-Ford algorithm to compute the shortest
        // path between start_node and end_node.
        let distances = self.gen_distances(NodeId(start_node_idx));

        if distances[end_node_idx] <= req.constant {
            return ProofResult::True;
        }

        if TRY_SPLITS {
            let split_res = self.prove_splits(req.clone(), false);
            if split_res != ProofResult::Undetermined {
                return split_res;
            }
        }

        if !recurse {
            return ProofResult::Undetermined;
        }

        // Otherwise, we'll check to see if we can prove that it's false by inverting the
        // requirement

        let contra_req = Inequality {
            // swap the sides
            lhs: req.rhs.clone(),
            rhs: req.lhs.clone(),
            // reverse the constant and subtract one. This is because:
            //   x > y + C  =>  x ≥ y + C+1  =>  -x ≤ -y - C-1
            // given that we are operating only on integers
            constant: (-req.constant) - 1,
        };

        let contra_res = self.prove(contra_req, false);
        match contra_res {
            ProofResult::True => ProofResult::False,
            ProofResult::Undetermined => ProofResult::Undetermined,
            // We never get a false proof statement from recursing because we tell *it* not to
            // recurse - `False` can only be generated by recursion
            ProofResult::False => panic!("unexpected false result from proof recursion"),
        }
    }

    /// A dedicated function for attempting to prove via the "split" method
    ///
    /// This is detailed above, in the doc comment for `TRY_SPLITS`.
    fn prove_splits(&self, req: Inequality, recurse: bool) -> ProofResult {
        // We require that the requirement has all terms on the right-hand side in order to properly
        // break it apart to find the upper bound - that way we can simply start from 0 and find
        // the upper bound on the negation, just as we would in `prove`.
        //
        // It *is* possible for requirements to have terms with the same variables on both sides,
        // so we'll need to account for that as well.

        // This snippet is largely duplicated from `Term::simplify_to_lists`
        let mut rhs = req.rhs.clone();
        for mut term in req.lhs.clone() {
            term.coef *= -1;
            match rhs.binary_search_by_key(&&term.vars, |t| &t.vars) {
                Ok(i) => {
                    rhs[i].coef += term.coef;
                    if rhs[i].coef == 0 {
                        rhs.remove(i);
                    }
                }
                Err(i) => rhs.insert(i, term),
            }
        }

        // Like the main `prove` method, this uses the Bellman-Ford algorithm to calculate the
        // distance between nodes. That being said, there's a critical optimization that we make
        // here: instead finding the distance from each term to a constant, we go the other way
        // around, finding the distance from a constant to all of the terms.
        //
        // In order to accomplish this, we need to search in reverse, so we run the algorithm
        // starting at the index of the empty coefficient (if it exists; otherwise we can't do
        // anything), and find the distance to each term (provided they also exist).

        // This section could be (fairly simply) improved to run in linear time but it doesn't
        // really matter.
        let empty_idx = match self.nodes.iter().position(|n| n.expr == &[]) {
            Some(i) => i,
            None => return ProofResult::Undetermined,
        };

        struct Info {
            idx: usize,
            num: i128,
            denom: i128,
        }

        let mut infos: Vec<Vec<Info>> = Vec::with_capacity(rhs.len());
        for i in 0..rhs.len() {
            let term = &rhs[i..i + 1];

            let same_vars = |n: &Node| {
                if n.expr.len() != 1 {
                    return false;
                }
                let t = &term[0];
                let n = &n.expr[0];
                t.vars == n.vars && t.coef.signum() == n.coef.signum()
            };

            let info = self
                .nodes
                .iter()
                .enumerate()
                .filter(|(_, n)| same_vars(n))
                .map(|(idx, _)| Info {
                    idx,
                    num: term[0].coef,
                    denom: self.nodes[idx].expr[0].coef,
                })
                .collect::<Vec<_>>();

            if info.len() == 0 {
                return ProofResult::Undetermined;
            }

            infos.push(info);
        }

        // And now we execute the algorithm, just as in `Prover::prove`.
        let distances = self.gen_distances(NodeId(empty_idx));

        // Now, we find the sum of the distances to get the total distance
        let opt_sum = infos
            .into_iter()
            .map(|set| {
                set.into_iter()
                    .map(|info| {
                        distances[info.idx]
                            .checked_mul(info.num)
                            .map(|x| x / info.denom)
                    })
                    .min()
                    .unwrap()
            })
            .fold(Some(0_i128), |acc, d| acc.and_then(|a| a.checked_add(d?)));

        if !opt_sum.is_none() || !recurse {
            return match opt_sum {
                None => ProofResult::Undetermined,
                Some(d) if d <= req.constant => ProofResult::True,
                Some(_) /* d > req.constant */ => ProofResult::Undetermined,
            };
        }

        // We'll recurse by checking the contrapositive, just as we did in `prove`
        let contra_req = Inequality {
            lhs: rhs,
            rhs: Vec::new(),
            constant: (-req.constant) - 1,
        };

        let contra_res = self.prove_splits(contra_req, false);
        match contra_res {
            ProofResult::True => ProofResult::False,
            ProofResult::Undetermined => ProofResult::Undetermined,
            ProofResult::False => panic!("unexpected false result from proof recursion"),
        }
    }

    fn add_req(&mut self, req: Inequality) {
        let reqs = if EXHAUSTIVE_REQ_SIDES {
            // group all of the terms onto the left-hand side
            let mut lhs = req.lhs;
            for mut term in req.rhs {
                term.coef *= -1;
                match lhs.binary_search_by_key(&&term.vars, |t| &t.vars) {
                    Ok(i) => {
                        lhs[i].coef += term.coef;
                        if lhs[i].coef == 0 {
                            lhs.remove(i);
                        }
                    }
                    Err(i) => lhs.insert(i, term),
                }
            }

            let constant = req.constant;
            let max_state = 1_i128 << lhs.len();
            (0..max_state)
                .map(|state| {
                    let mut new_lhs = Vec::new();
                    let mut new_rhs = Vec::new();
                    for (idx, mut term) in lhs.iter().cloned().enumerate() {
                        match state & (1 << idx as i128) {
                            0 => new_lhs.push(term),
                            _ => {
                                term.coef *= -1;
                                new_rhs.push(term);
                            }
                        }
                    }

                    Inequality {
                        lhs: new_lhs,
                        rhs: new_rhs,
                        constant,
                    }
                })
                .collect()
        } else if DOUBLE_NEGATE_REQS {
            // One way we can expand the capabilities of the solver is to provide equal connections for
            // the inverses of all requirements, for example:
            //   x ≤ y + 3  =>       -x ≥ -y + -3
            //              =>  -y + -3 ≤ -x
            //              =>  -y      ≤ -x + 3
            //  -y ≤ -x + 3

            let negate = |mut term: Term| {
                term.coef *= -1;
                term
            };

            let lhs = req.rhs.iter().cloned().map(negate).collect();
            let rhs = req.lhs.iter().cloned().map(negate).collect();

            let new_req = Inequality {
                lhs,
                rhs,
                constant: req.constant,
            };

            vec![req, new_req]
        } else {
            vec![req]
        };

        for req in reqs.iter() {
            // These create nodes corresponding to the lists of terms, if they do not already
            // exist. Otherwise, `create_node_idx` returns the index of a node `n` satisfying
            // `n.expr == req.lhs` (or rhs).
            let lhs_idx = self.create_node_idx(&req.lhs);
            let rhs_idx = self.create_node_idx(&req.rhs);

            let edge = Edge {
                offset: req.constant,
                num: 1,
                denom: 1,
            };

            self.nodes[lhs_idx].less_than.push((edge, NodeId(rhs_idx)));
        }

        if LINK_MUL_COEFS {
            for req in reqs {
                // If we can factor these out so that we have:
                //   d*A ≤ n*B + C
                // we then have:
                //   A ≤ B*n/d + C/d
                // which is nearly identical to the inequality given in the doc-comment for edges.

                let (lhs, lhs_gcd) = Term::div_gcd(req.lhs);
                let (rhs, rhs_gcd) = Term::div_gcd(req.rhs);

                if rhs_gcd == 1 && lhs_gcd == 1 {
                    continue;
                }

                let edge = Edge {
                    offset: req.constant / (lhs_gcd as i128),
                    num: rhs_gcd,
                    denom: lhs_gcd,
                };

                let lhs_idx = self.create_node_idx(&lhs);
                let rhs_idx = self.create_node_idx(&rhs);

                self.nodes[lhs_idx].less_than.push((edge, NodeId(rhs_idx)));
            }
        }
    }

    /// Generates the distances from the given starting node to all others, as given by the
    /// Bellman-Ford algorithm
    ///
    /// More details are given periodically within the body of the function itself.
    fn gen_distances(&self, start_node: NodeId) -> Vec<i128> {
        // The code is largely replicated from the excellent wikipedia pseudocode for the
        // algorithm, available here:
        //   https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm#Algorithm

        let NodeId(start_node_idx) = start_node;

        // Initialize the distances. We don't track predecessors here because we don't actually
        // care about the path itself, just the distance.
        //
        // i128::MAX serves as our value of "infinity"
        let mut distances = vec![i128::MAX; self.nodes.len()];
        distances[start_node_idx] = 0_i128;

        for _loop_iter in 0..self.nodes.len() {
            // We end early if there's no changes (this is very likely to happen)
            let mut changed = false;

            for (u, node) in self.nodes.iter().enumerate() {
                // We'll filter out all source nodes that have distances of infinity (i128::MAX),
                // because those haven't been reached yet.
                if distances[u] == i128::MAX {
                    continue;
                }

                // When we calculate an update distance, there are only two cases where we can
                // guarantee that everything is comparable:
                //  1. The muliplier (num / denom) is equal to one; or
                //  2. The starting node is a constant (i.e. start_node.expr == [])
                //
                // If neither of these are true, we can't compare, so we must skip that edge.

                let valid = |&&(Edge { num, denom, .. }, _): &&(_, NodeId)| {
                    num == denom || &self.nodes[start_node_idx].expr == &[]
                };

                for &(edge, NodeId(v)) in node.less_than.iter().filter(valid) {
                    let updated =
                        distances[u] * (edge.num as i128) / (edge.denom as i128) + edge.offset;
                    if updated < distances[v] {
                        changed = true;
                        distances[v] = updated;
                    }
                }
            }

            // We don't actually check for negative-weight cycles right now, because that's a
            // contradiction, and (1) contradictions can imply anything and (2) that will probably
            // be checked at creation later.
            // if loop_iter == self.nodes.len() - 1 && changed {
            //    // negative-weight cycle
            // }

            if !changed {
                break;
            }
        }

        distances
    }

    fn create_node_idx(&mut self, matching_expr: &[Term]) -> usize {
        if let Some(i) = self.nodes.iter().position(|n| n.expr == matching_expr) {
            return i;
        }

        self.nodes.push(Node {
            expr: Vec::from(matching_expr),
            less_than: Vec::new(),
        });
        self.nodes.len() - 1
    }

    // A helper function for use in `<Prover as super::Prover>::new`
    fn establish_stack(&self, stack: &mut Vec<Inequality>, negated: &mut bool) -> bool {
        while let Some(stack_ineq) = stack.pop() {
            let local_ineq = || match negated {
                true => stack_ineq.clone().negate(),
                false => stack_ineq.clone(),
            };

            // All successful match arms here will use other control flow - namely `continue`.
            //
            // The code following this match only executes in the case where we cannot
            // determine whether the inequality holds.
            match self.prove(local_ineq(), true) {
                // True? Great! We'll keep going.
                ProofResult::True => continue,
                // False? That's fine, too! This means it's < 0, so we'll negate everything.
                ProofResult::False => {
                    *negated = !*negated;
                    continue;
                }

                // Undetermined? It's tricky, but we still have one more shot! Instead of trying
                // to solve for `terms >= 0`, we'll try `terms <= 0` - maybe that single value
                // will make a difference.
                ProofResult::Undetermined => {
                    // Terms <= 0  =>  Terms < 1
                    //             => ¬(Terms >= 1)
                    let mut ineq = local_ineq();
                    ineq.constant += 1;
                    match self.prove(ineq, true) {
                        // Equivalent to False from above
                        ProofResult::True => {
                            *negated = !*negated;
                            continue;
                        }
                        // Equivalent to True from above
                        ProofResult::False => continue,

                        // Yield control to above, as it handles the *truly* undetermined case
                        // - everything else that's successful just `continues`
                        ProofResult::Undetermined => (),
                    }
                }
            }

            // If we can't prove it, add it back and indicate that we failed this time
            stack.push(stack_ineq);
            return false;
        }

        true
    }
}

impl<'a> SimpleProver<'a> for Prover {
    fn new(reqs: &[Requirement<'a>]) -> Self {
        let mut prover = Prover {
            // We add a single node for the empty value in order to ensure that we can still prove
            // trivial things, like `3 <= 4`, for example. Without this, we can have cases where
            // there aren't any proof statments given in a function, but there's still proof
            // required, through definitions.
            nodes: vec![Node {
                expr: Vec::new(),
                less_than: Vec::new(),
            }],
        };

        // All of the inequalities we would like to have added, but where we need to determine the
        // sign of a certain expression *first*, before we do so.
        //
        // More information below: (see: "There's something rather annoying...")
        let mut tabled: Vec<(Inequality, Vec<Inequality>, bool)> = vec![];
        //                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        // The values in the tuple serve to capture the state of the inner loop below. The first
        // element is the requirement we'd like to add; the second is `stack`, and the third is
        // `negated`.

        for req in reqs {
            // There's something rather annoying that we need to deal with here.
            //
            // When simplifying the original expression into an `Inequality`, we might have needed
            // to multiply both sides by an expression. If this expression was negative, we need to
            // REVERSE the inequality! So when `from_req` gives `Some(_)` for the expression both
            // sides were multiplied by, we actually need to determine whether it is positive or
            // not.
            //
            // Most simple cases (like a constant) will be trivial; these don't require any
            // previous requirements, and also don't expand multiple times.
            //
            // There are worse cases, however. In attempting to establish whether `agg >= 0`, we
            // may end up with *yet another* expression that is multiplied out, so we then need to
            // repeat the process anew. This will (thankfully) be finite, but it means that there's
            // extra handling required still. Every time we produce another expression, we add the
            // previous one to a stack in order to run this in a loop.
            //
            // ---
            //
            // If we can't establish the sign of the expression with the current set of requirements
            // already added to the prover, we'll delay adding it until later in the hopes that
            // some more requirements will come along and help (we push it to `tabled` above).

            let (ineq, mut stack) = Inequality::make_stack(req.clone());
            let mut negated = false;

            // try to establish all of the inequalities in the stack
            if !prover.establish_stack(&mut stack, &mut negated) {
                // Failed to establish stack; we'll table it until later
                tabled.push((ineq, stack, negated));
                // continue on to attempting to add the next requirement
                continue;
            }

            // If we made it here, we're all set to add the requirement to the prover!
            match negated {
                true => prover.add_req(ineq.negate()),
                false => prover.add_req(ineq),
            }
        }

        // We might have still failed to
        while !tabled.is_empty() {
            let mut changed = false;

            for (ineq, mut stack, mut negated) in mem::replace(&mut tabled, vec![]) {
                if !prover.establish_stack(&mut stack, &mut negated) {
                    // Failed to establish stack; we'll table it until later
                    tabled.push((ineq, stack, negated));
                    // continue on to attempting to add the next requirement
                    continue;
                }

                // If we made it here, we're all set to add the requirement to the prover!
                match negated {
                    true => prover.add_req(ineq.negate()),
                    false => prover.add_req(ineq),
                }

                changed = true;
            }

            if !changed {
                panic!("Failed establish the signs of initial requirements");
            }
        }

        prover
    }

    fn prove(&self, req: &Requirement) -> ProofResult {
        let (ineq, mut stack) = Inequality::make_stack(req.clone());
        let mut negated = false;

        // try to establish all of the inequalities in the stack
        if !self.establish_stack(&mut stack, &mut negated) {
            return ProofResult::Undetermined;
        }

        // If we made it here, we're all set to add the requirement to the prover!
        match negated {
            true => self.prove(ineq.negate(), true),
            false => self.prove(ineq, true),
        }
    }

    fn add_requirements(&mut self, reqs: &[Requirement<'a>]) {
        // The process here is virtually identical to that of `new`, so the comments have not been
        // duplicated. For an in-depth explanation, see the internals of that function.

        let mut tabled: Vec<(Inequality, Vec<Inequality>, bool)> = vec![];

        for req in reqs {
            let (ineq, mut stack) = Inequality::make_stack(req.clone());
            let mut negated = false;

            if !self.establish_stack(&mut stack, &mut negated) {
                tabled.push((ineq, stack, negated));
                continue;
            }

            match negated {
                true => self.add_req(ineq.negate()),
                false => self.add_req(ineq),
            }
        }

        while !tabled.is_empty() {
            let mut changed = false;

            for (ineq, mut stack, mut negated) in mem::replace(&mut tabled, vec![]) {
                if !self.establish_stack(&mut stack, &mut negated) {
                    tabled.push((ineq, stack, negated));
                    continue;
                }

                match negated {
                    true => self.add_req(ineq.negate()),
                    false => self.add_req(ineq),
                }

                changed = true;
            }

            if !changed {
                panic!("Failed establish the signs of initial requirements");
            }
        }
    }
}
