//! The graph-based prover

use super::expr::Expr;
use super::{ProofResult, Requirement, Term};
use crate::ast::Ident;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct Prover {
    /// The set of expression nodes in the graph, each represented by a sum of terms and edges to
    /// the values they are less than.
    nodes: Vec<Node>,

    /// A flag for attempting a different method of proof when we can't find both sides of the
    /// requirement in the graph.
    ///
    /// For example: In a case like `x+y+z <= 5`, we might split this into independently determining
    /// the upper bounds on each of x, y, and z.
    ///
    /// A more complex example could be: `x+y-z <= 5 + w`, which we'd convert into `x+y-z-w <= 5`
    /// before finding the upper bounds.
    try_splits: bool,
}

/// A flag for whether the prover should - by defualt - try to split requirements apart if they are
/// not present in the graph.
const DEFAULT_TRY_SPLITS: bool = true;

/// A flag for whether requirements should be doubled so that their negations are also added (so
/// that upper bounds on `x` provide lower bounds on `-x`)
///
/// Note that this should be enabled if DEFAULT_TRY_SPLITS is enabled.
const DOUBLE_NEGATE_REQS: bool = false;

const EXHAUSTIVE_REQ_SIDES: bool = true;

#[derive(Copy, Clone, Debug)]
struct NodeId(usize);

#[derive(Clone, Debug)]
struct Node {
    expr: Vec<Term>,
    // expr <= [NodeId].expr + edge
    less_than: Vec<(Edge, NodeId)>,
}

#[derive(Copy, Clone, Debug)]
struct Edge(i128);

impl Prover {
    /// An identical function to `super::Prover::prove`, except this is a helper for the recursion,
    /// which we use to manage attempting to prove the contrapositive.
    fn prove(&self, req: &Requirement, recurse: bool) -> ProofResult {
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
            None if self.try_splits => return self.prove_splits(req.clone(), true),
            None => return ProofResult::Undetermined,
        };

        let end_node_idx = match self.nodes.iter().position(|n| n.expr == req.rhs) {
            Some(i) => i,
            None if self.try_splits => return self.prove_splits(req.clone(), true),
            None => return ProofResult::Undetermined,
        };

        // We're going to perform the Bellman-Ford algorithm to compute the shortest path between
        // start_node and end_node.
        //
        // This is largely replicated from the excellent wikipedia pseudocode for the algorithm,
        // available here: https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm#Algorithm

        // initialize distances. We don't track predecesssors here because we don't actually care
        // about the path itself, just the distance
        let mut distances = vec![i128::MAX; self.nodes.len()];
        distances[start_node_idx] = 0_i128;

        for _loop_iter in 0..self.nodes.len() {
            let mut changed = false;

            for (u, node) in self.nodes.iter().enumerate() {
                for &(Edge(weight), NodeId(v)) in node.less_than.iter() {
                    if distances[u] != i128::MAX && distances[u] + weight < distances[v] {
                        changed = true;
                        distances[v] = distances[u] + weight;
                    }
                }
            }

            // We don't actually check for negative-weight cycles right now, because that's a
            // contradiction, and (1) contradictions can imply anything, and (2) that will probably
            // be checked at creation later.
            // if loop_iter == self.nodes.len() - 1 && changed {
            //    // negative-weight cycle
            // }

            if !changed {
                break;
            }
        }

        if distances[end_node_idx] <= req.constant {
            return ProofResult::True;
        }

        if self.try_splits {
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

        let contra_req = Requirement {
            // swap the sides
            lhs: req.rhs.clone(),
            rhs: req.lhs.clone(),
            // reverse the constant and subtract one. This is because:
            //   x > y + C  =>  x ≥ y + C+1  =>  -x ≤ -y - C-1
            // given that we are operating only on integers
            constant: (-req.constant) - 1,
            _marker: PhantomData,
        };

        let contra_res = self.prove(&contra_req, false);
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
    /// This is detailed above, in the doc comment for `Prover.try_splits`.
    fn prove_splits(&self, req: Requirement, recurse: bool) -> ProofResult {
        // We require that the requirement has all terms on the right-hand side in order to properly
        // break it apart to find the upper bound - that way we can simply start from 0 and find
        // the upper bound on the negation, just as we would in `prove`.
        //
        // It *is* possible for requirements to have terms with the same variables on both sides,
        // so we'll need to account for that as well.

        // This snippet is largely duplicated from `Term::simplify_to_lists`
        let mut rhs = req.rhs;
        for mut term in req.lhs {
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

        let mut term_idxs = vec![0; rhs.len()];
        for i in 0..rhs.len() {
            let term = &rhs[i..i + 1];
            term_idxs[i] = match self.nodes.iter().position(|n| n.expr == term) {
                Some(idx) => idx,
                None => return ProofResult::Undetermined,
            };
        }

        // And now we execute the algorithm, just as in `Prover::prove`.
        //
        // This is directly copied from above - it could be made into a separate function, but
        // it'll work for now.
        // ^ FIXME

        let mut distances = vec![i128::MAX; self.nodes.len()];
        distances[empty_idx] = 0_i128;

        for _loop_iter in 0..self.nodes.len() {
            let mut changed = false;

            for (u, node) in self.nodes.iter().enumerate() {
                for &(Edge(weight), NodeId(v)) in node.less_than.iter() {
                    if distances[u] != i128::MAX && distances[u] + weight < distances[v] {
                        changed = true;
                        distances[v] = distances[u] + weight;
                    }
                }
            }

            // We don't actually check for negative-weight cycles right now, because that's a
            // contradiction, and (1) contradictions can imply anything, and (2) that will probably
            // be checked at creation later.
            // if loop_iter == self.nodes.len() - 1 && changed {
            //    // negative-weight cycle
            // }

            if !changed {
                break;
            }
        }

        // Now, we find the sum of the distances to get the total distance
        let opt_sum = term_idxs
            .into_iter()
            .map(|i| distances[i])
            .fold(Some(0_i128), |acc, d| acc.and_then(|a| a.checked_add(d)));

        if !opt_sum.is_none() || !recurse {
            return match opt_sum {
                None => ProofResult::Undetermined,
                Some(d) if d <= req.constant => ProofResult::True,
                Some(_) /* d > req.constant */ => ProofResult::Undetermined,
            };
        }

        // We'll recurse by checking the contrapositive, just as we did in `prove`
        let contra_req = Requirement {
            lhs: rhs,
            rhs: Vec::new(),
            constant: (-req.constant) - 1,
            _marker: PhantomData,
        };

        let contra_res = self.prove_splits(contra_req, false);
        match contra_res {
            ProofResult::True => ProofResult::False,
            ProofResult::Undetermined => ProofResult::Undetermined,
            ProofResult::False => panic!("unexpected false result from proof recursion"),
        }
    }
}

impl<'a> super::Prover<'a> for Prover {
    fn new(mut reqs: Vec<Requirement<'a>>) -> Self {
        if EXHAUSTIVE_REQ_SIDES {
            fn expand(req: Requirement) -> Vec<Requirement> {
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

                        Requirement {
                            lhs: new_lhs,
                            rhs: new_rhs,
                            constant,
                            _marker: PhantomData,
                        }
                    })
                    .collect()
            }

            reqs = reqs.into_iter().map(expand).flatten().collect();
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

            let inverse_reqs = reqs
                .iter()
                .map(|req| {
                    // swap lhs and rhs, and reverse both
                    let lhs = req.rhs.iter().cloned().map(negate).collect();
                    let rhs = req.lhs.iter().cloned().map(negate).collect();

                    // the coefficient stays the same, as detailed above
                    Requirement {
                        lhs,
                        rhs,
                        constant: req.constant,
                        _marker: PhantomData,
                    }
                })
                .collect::<Vec<_>>();

            reqs.extend(inverse_reqs);
        }

        let mut nodes: Vec<Node> = Vec::new();
        for req in reqs {
            let lhs_idx = match nodes.iter().position(|n| n.expr == req.lhs) {
                Some(i) => i,
                None => {
                    nodes.push(Node {
                        expr: req.lhs.clone(),
                        less_than: Vec::new(),
                    });
                    nodes.len() - 1
                }
            };

            let rhs_idx = match nodes.iter().position(|n| n.expr == req.rhs) {
                Some(i) => i,
                None => {
                    nodes.push(Node {
                        expr: req.rhs.clone(),
                        less_than: Vec::new(),
                    });
                    nodes.len() - 1
                }
            };

            nodes[lhs_idx]
                .less_than
                .push((Edge(req.constant), NodeId(rhs_idx)));
        }

        Prover {
            nodes,
            try_splits: DEFAULT_TRY_SPLITS,
        }
    }

    fn prove(&self, req: &Requirement) -> ProofResult {
        self.prove(req, true)
    }

    fn define(&'a self, x: Ident<'a>, expr: &'a Expr<'a>) -> Self {
        todo!()
    }

    fn shadow(&self, x: Ident<'a>) -> Self {
        todo!()
    }
}
