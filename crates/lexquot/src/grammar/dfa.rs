//! Bounded, exact regular-language operations used by the grammar-aware frontend.
//! Every returned DFA is reachable from its declared root; incomplete edges reject.
use super::{Budget, guard, spend};
use crate::{AnalysisError, trace::TraceDfa};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Dfa {
    pub start: u32,
    pub accepting: Vec<bool>,
    pub transitions: Vec<Vec<(u8, u32)>>,
}
impl From<&TraceDfa> for Dfa {
    fn from(value: &TraceDfa) -> Self {
        Self {
            start: value.start(),
            accepting: value.accepting().to_vec(),
            transitions: value.transitions().to_vec(),
        }
    }
}
impl Dfa {
    pub fn new(start: u32, accepting: Vec<bool>, transitions: Vec<Vec<(u8, u32)>>) -> Self {
        Self {
            start,
            accepting,
            transitions,
        }
    }
    pub fn state_count(&self) -> usize {
        self.accepting.len()
    }
    pub fn nullable(&self) -> bool {
        self.accepting
            .get(self.start as usize)
            .copied()
            .unwrap_or(false)
    }
    pub fn is_empty(&self) -> bool {
        !self.accepting.iter().any(|&x| x)
    }
    pub(super) fn epsilon() -> Self {
        Self::new(0, vec![true], vec![vec![]])
    }
    pub(super) fn empty() -> Self {
        Self::new(0, vec![false], vec![vec![]])
    }
    pub fn accepts(&self, word: &[u8]) -> bool {
        let mut s = self.start;
        for &byte in word {
            let Some(row) = self.transitions.get(s as usize) else {
                return false;
            };
            let Some(&(_, t)) = row.iter().find(|(b, _)| *b == byte) else {
                return false;
            };
            s = t;
        }
        self.accepting.get(s as usize).copied().unwrap_or(false)
    }
    pub(super) fn validate(&mut self, budget: &Budget) -> Result<(), AnalysisError> {
        let n = self.state_count();
        if n == 0 || n != self.transitions.len() || self.start as usize >= n {
            return Err(AnalysisError::InvalidInput(
                "invalid grammar-terminal DFA dimensions or start".into(),
            ));
        }
        guard(
            "grammar input DFA states",
            n,
            budget.max_input_states.min(u32::MAX as usize),
        )?;
        for row in &mut self.transitions {
            row.sort_unstable();
            if row.windows(2).any(|p| p[0].0 == p[1].0) || row.iter().any(|&(_, s)| s as usize >= n)
            {
                return Err(AnalysisError::InvalidInput(
                    "duplicate byte or out-of-range grammar-terminal transition".into(),
                ));
            }
        }
        Ok(())
    }
    /// Remove epsilon without deleting positive words that return to the start.
    pub(super) fn positive(&self) -> Self {
        let mut out = self.clone();
        if out.nullable() {
            let row = out.transitions[out.start as usize].clone();
            out.start = out.state_count() as u32;
            out.accepting.push(false);
            out.transitions.push(row);
        }
        out
    }
    pub(super) fn trace_positive(
        &self,
        budget: &Budget,
        work: &mut usize,
    ) -> Result<Option<TraceDfa>, AnalysisError> {
        let positive = self.positive().minimize(budget, work)?;
        if positive.is_empty() {
            return Ok(None);
        }
        TraceDfa::new(positive.start, positive.accepting, positive.transitions).map(Some)
    }
    /// Complete-match minimization, followed by deterministic BFS numbering.
    /// Empty-language sink is implicit. This drops unreachable states, which is
    /// correct for a grammar terminal, not the older arbitrary-residual API.
    pub(super) fn minimize(
        &self,
        budget: &Budget,
        work: &mut usize,
    ) -> Result<Self, AnalysisError> {
        let dense = Dense::new(self, budget, work)?;
        let n = dense.accepting.len();
        let a = dense.bytes.len();
        let mut classes = dense
            .accepting
            .iter()
            .map(|&x| u32::from(x))
            .collect::<Vec<_>>();
        loop {
            spend(work, n.saturating_mul(a), budget.max_work)?;
            let mut ids = FxHashMap::<(bool, Vec<u32>), u32>::default();
            let next = (0..n)
                .map(|s| {
                    let key = (
                        dense.accepting[s],
                        dense.delta[s * a..(s + 1) * a]
                            .iter()
                            .map(|&t| classes[t as usize])
                            .collect(),
                    );
                    let new = ids.len() as u32;
                    *ids.entry(key).or_insert(new)
                })
                .collect::<Vec<_>>();
            if next == classes {
                break;
            }
            classes = next;
        }
        let dead = classes[0];
        let root = classes[dense.start as usize];
        if root == dead {
            return Ok(Self::empty());
        }
        let k = classes.iter().copied().max().unwrap_or(0) as usize + 1;
        let mut reps = vec![usize::MAX; k];
        for (s, &c) in classes.iter().enumerate() {
            if reps[c as usize] == usize::MAX {
                reps[c as usize] = s;
            }
        }
        let mut map = vec![u32::MAX; k];
        map[root as usize] = 0;
        let mut queue = VecDeque::from([root]);
        let mut f = Vec::new();
        let mut rows = Vec::new();
        let mut num = 1;
        while let Some(c) = queue.pop_front() {
            let s = reps[c as usize];
            f.push(dense.accepting[s]);
            let mut row = Vec::new();
            for byte in 0..256 {
                let target = classes[dense.delta[s * a + dense.class[byte] as usize] as usize];
                if target == dead {
                    continue;
                }
                if map[target as usize] == u32::MAX {
                    map[target as usize] = num;
                    num += 1;
                    queue.push_back(target);
                }
                row.push((byte as u8, map[target as usize]));
            }
            rows.push(row);
        }
        Ok(Self::new(0, f, rows))
    }
}

/// Dense, byte-classed, reachable DFA with an explicit rejecting state zero.
#[derive(Clone, Debug)]
pub(super) struct Dense {
    pub start: u32,
    pub accepting: Vec<bool>,
    pub delta: Vec<u32>,
    pub class: [u16; 256],
    pub bytes: Vec<u8>,
}
impl Dense {
    pub fn new(dfa: &Dfa, budget: &Budget, work: &mut usize) -> Result<Self, AnalysisError> {
        let n = dfa.state_count();
        guard(
            "grammar dense source cells",
            (n + 1).saturating_mul(256),
            budget.max_cells,
        )?;
        let mut seen = vec![false; n];
        let mut order = vec![dfa.start as usize];
        seen[dfa.start as usize] = true;
        let mut i = 0;
        while i < order.len() {
            for &(_, t) in &dfa.transitions[order[i]] {
                if !seen[t as usize] {
                    seen[t as usize] = true;
                    order.push(t as usize);
                }
            }
            i += 1;
        }
        let mut map = vec![0u32; n];
        for (i, &s) in order.iter().enumerate() {
            map[s] = i as u32 + 1;
        }
        let mut full = vec![[0u32; 256]; order.len() + 1];
        let mut finals = vec![false];
        for (i, &s) in order.iter().enumerate() {
            finals.push(dfa.accepting[s]);
            for &(b, t) in &dfa.transitions[s] {
                full[i + 1][b as usize] = map[t as usize];
            }
        }
        spend(work, full.len().saturating_mul(256), budget.max_work)?;
        let mut keys = FxHashMap::<Vec<u32>, u16>::default();
        let mut class = [0u16; 256];
        let mut bytes = Vec::new();
        for b in 0..256 {
            let col = full.iter().map(|r| r[b]).collect::<Vec<_>>();
            let next = keys.len() as u16;
            let c = *keys.entry(col).or_insert(next);
            if c == next {
                bytes.push(b as u8);
            }
            class[b] = c;
        }
        let delta = full
            .iter()
            .flat_map(|r| bytes.iter().map(|&b| r[b as usize]))
            .collect();
        Ok(Self {
            start: 1,
            accepting: finals,
            delta,
            class,
            bytes,
        })
    }
}

pub(super) struct Nfa {
    rows: Vec<Vec<(u8, u32)>>,
    eps: Vec<Vec<u32>>,
}
impl Nfa {
    pub fn new() -> Self {
        Self {
            rows: Vec::new(),
            eps: Vec::new(),
        }
    }
    pub fn state(&mut self, budget: &Budget) -> Result<u32, AnalysisError> {
        guard(
            "grammar folding NFA states",
            self.rows.len() + 1,
            budget.max_nfa_states.min(u32::MAX as usize),
        )?;
        let id = self.rows.len() as u32;
        self.rows.push(Vec::new());
        self.eps.push(Vec::new());
        Ok(id)
    }
    pub fn epsilon(&mut self, source: u32, target: u32) {
        self.eps[source as usize].push(target);
    }
    pub fn append(
        &mut self,
        source: u32,
        target: u32,
        dfa: &Dfa,
        budget: &Budget,
        work: &mut usize,
    ) -> Result<(), AnalysisError> {
        guard(
            "grammar folding NFA states",
            self.rows.len().saturating_add(dfa.state_count()),
            budget.max_nfa_states,
        )?;
        let base = self.rows.len() as u32;
        for _ in &dfa.accepting {
            self.state(budget)?;
        }
        self.epsilon(source, base + dfa.start);
        for (s, row) in dfa.transitions.iter().enumerate() {
            spend(work, row.len() + 1, budget.max_work)?;
            self.rows[base as usize + s].extend(row.iter().map(|&(b, t)| (b, base + t)));
            if dfa.accepting[s] {
                self.epsilon(base + s as u32, target);
            }
        }
        Ok(())
    }
    pub fn determinize(
        &self,
        start: u32,
        final_state: u32,
        budget: &Budget,
        work: &mut usize,
    ) -> Result<Dfa, AnalysisError> {
        let mut marks = vec![0u32; self.rows.len()];
        let mut generation = 0u32;
        let mut closure = |seed: &[u32], work: &mut usize| -> Result<Vec<u32>, AnalysisError> {
            generation = generation.wrapping_add(1);
            if generation == 0 {
                marks.fill(0);
                generation = 1;
            }
            let mut output = Vec::new();
            for &s in seed {
                if marks[s as usize] != generation {
                    marks[s as usize] = generation;
                    output.push(s);
                }
            }
            let mut j = 0;
            while j < output.len() {
                let row = &self.eps[output[j] as usize];
                spend(work, row.len() + 1, budget.max_work)?;
                for &t in row {
                    if marks[t as usize] != generation {
                        marks[t as usize] = generation;
                        output.push(t);
                    }
                }
                j += 1;
            }
            output.sort_unstable();
            Ok(output)
        };
        let first = closure(&[start], work)?;
        let mut keys = FxHashMap::<Vec<u32>, u32>::default();
        keys.insert(first.clone(), 0);
        let mut subsets = vec![first];
        let mut subset_cells = subsets[0].len();
        let mut f = Vec::new();
        let mut rows = Vec::new();
        let mut i = 0;
        while i < subsets.len() {
            guard(
                "grammar folding DFA states",
                subsets.len(),
                budget.max_dfa_states,
            )?;
            guard("grammar subset cells", subset_cells, budget.max_cells)?;
            f.push(subsets[i].binary_search(&final_state).is_ok());
            let mut targets: [Vec<u32>; 256] = std::array::from_fn(|_| Vec::new());
            for &s in &subsets[i] {
                spend(work, self.rows[s as usize].len() + 1, budget.max_work)?;
                for &(b, t) in &self.rows[s as usize] {
                    targets[b as usize].push(t);
                }
            }
            let mut seen_seeds = FxHashMap::<Vec<u32>, u32>::default();
            let mut row = Vec::new();
            for (b, seeds) in targets.iter_mut().enumerate() {
                if seeds.is_empty() {
                    continue;
                }
                seeds.sort_unstable();
                seeds.dedup();
                let id = if let Some(&id) = seen_seeds.get(seeds) {
                    id
                } else {
                    let set = closure(seeds, work)?;
                    let id = if let Some(&id) = keys.get(&set) {
                        id
                    } else {
                        guard(
                            "grammar folding DFA states",
                            subsets.len() + 1,
                            budget.max_dfa_states,
                        )?;
                        subset_cells = subset_cells.saturating_add(set.len());
                        guard("grammar subset cells", subset_cells, budget.max_cells)?;
                        let id = subsets.len() as u32;
                        keys.insert(set.clone(), id);
                        subsets.push(set);
                        id
                    };
                    seen_seeds.insert(seeds.clone(), id);
                    id
                };
                row.push((b as u8, id));
            }
            rows.push(row);
            i += 1;
        }
        Dfa::new(0, f, rows).minimize(budget, work)
    }
}
