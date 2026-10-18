//! Exact, hash-consed finite languages of terminal words and endpoint marks.
//! A node has at most one edge per terminal. Union merges child *languages*,
//! rather than treating an arbitrary nondeterministic DAG shape as canonical.

use super::{limit, TraceBudget};
use crate::AnalysisError;
use rustc_hash::FxHashMap;
use std::sync::Arc;

pub(super) const EMPTY: u32 = 0;
pub(super) const END: u32 = 1;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Node {
    pub end: bool,
    /// (terminal ID, endpoint coordinate). Coordinate is 1 in mask mode and a
    /// residual-state class plus one in residual mode. Zero denotes no endpoint.
    pub pending: Vec<(u32, u32)>,
    pub edges: Vec<(u32, u32)>,
}

impl Node {
    pub fn empty() -> Self {
        Self {
            end: false,
            pending: Vec::new(),
            edges: Vec::new(),
        }
    }
}

pub(super) struct Languages {
    nodes: Vec<Arc<Node>>,
    ids: FxHashMap<Arc<Node>, u32>,
    unions: FxHashMap<(u32, u32), u32>,
    budget: TraceBudget,
    pub union_work: usize,
    cells: usize,
}

impl Languages {
    pub fn new(budget: TraceBudget) -> Result<Self, AnalysisError> {
        limit("trace language nodes", 2, budget.max_language_nodes)?;
        let empty = Arc::new(Node::empty());
        let end = Arc::new(Node {
            end: true,
            ..Node::empty()
        });
        let mut ids = FxHashMap::default();
        ids.insert(empty.clone(), EMPTY);
        ids.insert(end.clone(), END);
        Ok(Self {
            nodes: vec![empty, end],
            ids,
            unions: FxHashMap::default(),
            budget,
            union_work: 0,
            cells: 0,
        })
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    pub fn union_count(&self) -> usize {
        self.unions.len()
    }
    pub fn cells(&self) -> usize {
        self.cells
    }
    pub fn node(&self, id: u32) -> &Node {
        &self.nodes[id as usize]
    }

    pub fn intern(&mut self, node: Node) -> Result<u32, AnalysisError> {
        debug_assert!(node.edges.windows(2).all(|w| w[0].0 < w[1].0));
        debug_assert!(node.pending.windows(2).all(|w| w[0] < w[1]));
        debug_assert!(node.edges.iter().all(|&(_, child)| child != EMPTY));
        if let Some(&id) = self.ids.get(&node) {
            return Ok(id);
        }
        limit(
            "trace language nodes",
            self.nodes.len() + 1,
            self.budget.max_language_nodes.min(u32::MAX as usize),
        )?;
        let cells = self
            .cells
            .saturating_add(node.edges.len())
            .saturating_add(node.pending.len());
        limit(
            "trace language edge and endpoint cells",
            cells,
            self.budget.max_cells,
        )?;
        self.cells = cells;
        let id = self.nodes.len() as u32;
        let node = Arc::new(node);
        self.nodes.push(node.clone());
        self.ids.insert(node, id);
        Ok(id)
    }

    fn simple_union(&self, a: u32, b: u32) -> Option<u32> {
        if a == b || b == EMPTY {
            Some(a)
        } else if a == EMPTY {
            Some(b)
        } else {
            self.unions.get(&ordered(a, b)).copied()
        }
    }

    /// Iterative postorder avoids a native recursion limit for long tokens.
    pub fn union(&mut self, a: u32, b: u32) -> Result<u32, AnalysisError> {
        if let Some(id) = self.simple_union(a, b) {
            return Ok(id);
        }
        let root = ordered(a, b);
        let mut stack = vec![(root.0, root.1, false)];
        while let Some((left, right, expanded)) = stack.pop() {
            if self.simple_union(left, right).is_some() {
                continue;
            }
            self.union_work = self
                .union_work
                .checked_add(1)
                .ok_or_else(|| AnalysisError::InvalidInput("trace union work overflow".into()))?;
            limit(
                "trace union work",
                self.union_work,
                self.budget.max_union_pairs.saturating_mul(32),
            )?;
            let l = self.nodes[left as usize].clone();
            let r = self.nodes[right as usize].clone();
            if !expanded {
                stack.push((left, right, true));
                let (mut i, mut j) = (0, 0);
                while i < l.edges.len() && j < r.edges.len() {
                    let (lt, lc) = l.edges[i];
                    let (rt, rc) = r.edges[j];
                    if lt < rt {
                        i += 1;
                    } else if rt < lt {
                        j += 1;
                    } else {
                        if self.simple_union(lc, rc).is_none() {
                            let (a, b) = ordered(lc, rc);
                            stack.push((a, b, false));
                        }
                        i += 1;
                        j += 1;
                    }
                }
                limit(
                    "trace union work stack",
                    stack.len(),
                    self.budget.max_union_pairs,
                )?;
                continue;
            }
            let mut pending = l.pending.clone();
            pending.extend_from_slice(&r.pending);
            pending.sort_unstable();
            pending.dedup();
            let mut edges = Vec::with_capacity(l.edges.len() + r.edges.len());
            let (mut i, mut j) = (0, 0);
            while i < l.edges.len() || j < r.edges.len() {
                if j == r.edges.len() || (i < l.edges.len() && l.edges[i].0 < r.edges[j].0) {
                    edges.push(l.edges[i]);
                    i += 1;
                } else if i == l.edges.len() || r.edges[j].0 < l.edges[i].0 {
                    edges.push(r.edges[j]);
                    j += 1;
                } else {
                    let child = self
                        .simple_union(l.edges[i].1, r.edges[j].1)
                        .ok_or_else(|| {
                            AnalysisError::Kernel("unfinished trace-union dependency".into())
                        })?;
                    edges.push((l.edges[i].0, child));
                    i += 1;
                    j += 1;
                }
            }
            let id = self.intern(Node {
                end: l.end || r.end,
                pending,
                edges,
            })?;
            limit(
                "trace union pairs",
                self.unions.len() + 1,
                self.budget.max_union_pairs,
            )?;
            self.unions.insert((left, right), id);
        }
        self.simple_union(root.0, root.1)
            .ok_or_else(|| AnalysisError::Kernel("missing completed trace union".into()))
    }
}

fn ordered(a: u32, b: u32) -> (u32, u32) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn union_is_canonical_commutative_associative_and_idempotent() {
        let mut p = Languages::new(TraceBudget::default()).unwrap();
        let a = p
            .intern(Node {
                edges: vec![(2, END)],
                ..Node::empty()
            })
            .unwrap();
        let b = p
            .intern(Node {
                edges: vec![(3, END)],
                ..Node::empty()
            })
            .unwrap();
        let c = p
            .intern(Node {
                pending: vec![(4, 9)],
                ..Node::empty()
            })
            .unwrap();
        assert_eq!(p.union(a, a).unwrap(), a);
        assert_eq!(p.union(a, b).unwrap(), p.union(b, a).unwrap());
        let ab = p.union(a, b).unwrap();
        let bc = p.union(b, c).unwrap();
        assert_eq!(p.union(ab, c).unwrap(), p.union(a, bc).unwrap());
        let x = p
            .intern(Node {
                edges: vec![(1, a)],
                ..Node::empty()
            })
            .unwrap();
        let y = p
            .intern(Node {
                edges: vec![(1, b)],
                ..Node::empty()
            })
            .unwrap();
        let z = p
            .intern(Node {
                edges: vec![(1, ab)],
                ..Node::empty()
            })
            .unwrap();
        assert_eq!(p.union(x, y).unwrap(), z);
    }

    #[test]
    fn union_keeps_pending_residuals_and_terminal_order() {
        let mut p = Languages::new(TraceBudget::default()).unwrap();
        let a = p
            .intern(Node {
                pending: vec![(2, 3)],
                ..Node::empty()
            })
            .unwrap();
        let b = p
            .intern(Node {
                pending: vec![(2, 4)],
                ..Node::empty()
            })
            .unwrap();
        let u = p.union(a, b).unwrap();
        assert_eq!(p.node(u).pending, vec![(2, 3), (2, 4)]);
        let ab = p
            .intern(Node {
                edges: vec![(1, a)],
                ..Node::empty()
            })
            .unwrap();
        let ba = p
            .intern(Node {
                edges: vec![(2, b)],
                ..Node::empty()
            })
            .unwrap();
        assert_ne!(ab, ba);
    }
}
