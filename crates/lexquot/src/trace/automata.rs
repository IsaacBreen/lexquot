//! Boolean residual sharing and the deliberately separate product-root baseline.

use super::{limit, PreparationStats, PrepareOptions, TraceBudget, TraceRequest};
use crate::{AnalysisError, Expr};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use std::sync::Arc;
use std::time::Instant;

/// A deterministic byte automaton for one nonempty, non-nullable terminal
/// language. Construction removes only states with empty right language; it
/// does not prune live states from a single reset root.
#[derive(Debug, Clone)]
pub struct TraceDfa {
    start: u32,
    accepting: Vec<bool>,
    transitions: Vec<Vec<(u8, u32)>>,
}

impl TraceDfa {
    pub fn new(
        start: u32,
        accepting: Vec<bool>,
        mut transitions: Vec<Vec<(u8, u32)>>,
    ) -> Result<Self, AnalysisError> {
        let n = accepting.len();
        if n == 0 || n != transitions.len() || start as usize >= n || n >= u32::MAX as usize {
            return Err(AnalysisError::InvalidInput(
                "invalid terminal DFA dimensions or reset root".into(),
            ));
        }
        if accepting[start as usize] {
            return Err(AnalysisError::InvalidInput(
                "trace terminals must not accept the empty string".into(),
            ));
        }
        let mut reverse = vec![Vec::new(); n];
        for (s, row) in transitions.iter_mut().enumerate() {
            row.sort_unstable();
            if row.windows(2).any(|w| w[0].0 == w[1].0) || row.iter().any(|&(_, t)| t as usize >= n)
            {
                return Err(AnalysisError::InvalidInput(
                    "invalid or duplicate terminal DFA transition".into(),
                ));
            }
            for &(_, t) in row.iter() {
                reverse[t as usize].push(s);
            }
        }
        let mut live = accepting.clone();
        let mut pending = accepting
            .iter()
            .enumerate()
            .filter_map(|(s, &f)| f.then_some(s))
            .collect::<Vec<_>>();
        while let Some(t) = pending.pop() {
            for &s in &reverse[t] {
                if !live[s] {
                    live[s] = true;
                    pending.push(s);
                }
            }
        }
        if !live[start as usize] {
            return Err(AnalysisError::InvalidInput(
                "trace terminal has empty language".into(),
            ));
        }
        let mut next = 0u32;
        let map = live
            .iter()
            .map(|&keep| {
                if keep {
                    let id = next;
                    next += 1;
                    Some(id)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let out_accepting = accepting
            .iter()
            .enumerate()
            .filter_map(|(s, &f)| live[s].then_some(f))
            .collect();
        let out_transitions = transitions
            .iter()
            .enumerate()
            .filter_map(|(s, row)| {
                live[s].then(|| {
                    row.iter()
                        .filter_map(|&(b, t)| map[t as usize].map(|t| (b, t)))
                        .collect()
                })
            })
            .collect();
        Ok(Self {
            start: map[start as usize].unwrap(),
            accepting: out_accepting,
            transitions: out_transitions,
        })
    }

    /// Uses the existing expression frontend independently for each terminal.
    /// Frontend resource usage is outside [`TraceBudget`]; supply prepared DFAs
    /// or impose process-level limits for hostile or exceptionally large regexes.
    pub fn from_expression(expression: &Expr) -> Result<Self, AnalysisError> {
        let dfa = crate::error::catch_internal_invariant(|| {
            crate::automata::lexer::compile::compile_terminal_expr_dfa(expression)
        })
        .map_err(|e| AnalysisError::Kernel(e.to_string()))?;
        if dfa.has_epsilon_transitions() {
            return Err(AnalysisError::InvalidInput(
                "determinize terminal epsilon transitions before trace analysis".into(),
            ));
        }
        let accepting = (0..dfa.num_states() as u32)
            .map(|s| dfa.finalizers(s).contains(0))
            .collect();
        let transitions = (0..dfa.num_states() as u32)
            .map(|s| dfa.transitions(s).collect())
            .collect();
        Self::new(0, accepting, transitions)
    }

    pub fn state_count(&self) -> usize {
        self.accepting.len()
    }
    pub fn start(&self) -> u32 {
        self.start
    }
    pub fn accepting(&self) -> &[bool] {
        &self.accepting
    }
    pub fn transitions(&self) -> &[Vec<(u8, u32)>] {
        &self.transitions
    }
}

/// Reusable union of Boolean terminal residuals. State zero is the implicit dead
/// sink; all remaining states are admitted first-match roots. `roots[t]` keeps
/// the reset coordinate of terminal t even if its residual structure is shared.
#[derive(Debug, Clone)]
pub struct PreparedTrace {
    pub(super) accepting: Vec<bool>,
    pub(super) future: Vec<bool>,
    pub(super) endpoint_classes: Vec<u32>,
    pub(super) table: Vec<u32>,
    pub(super) byte_class: [u16; 256],
    pub(super) class_bytes: Vec<u8>,
    pub(super) roots: Vec<u32>,
    pub(super) root_destinations: Vec<Vec<(u32, u32)>>,
    stats: PreparationStats,
}

impl PreparedTrace {
    pub fn new(terminals: &[TraceDfa], options: PrepareOptions) -> Result<Self, AnalysisError> {
        let started = Instant::now();
        if terminals.is_empty() || terminals.len() >= u32::MAX as usize {
            return Err(AnalysisError::InvalidInput(
                "provide a nonempty finite terminal family".into(),
            ));
        }
        let source_states = terminals
            .iter()
            .try_fold(0usize, |n, t| n.checked_add(t.state_count()))
            .ok_or_else(|| {
                AnalysisError::InvalidInput("terminal residual union size overflow".into())
            })?;
        limit(
            "trace source states",
            source_states + 1,
            options.budget.max_states.min(u32::MAX as usize),
        )?;
        let mut rows = vec![Vec::new()];
        let mut accepting = vec![false];
        let mut groups = vec![0u32];
        let mut roots = Vec::with_capacity(terminals.len());
        for (t, dfa) in terminals.iter().enumerate() {
            let base = rows.len() as u32;
            roots.push(base + dfa.start);
            accepting.extend_from_slice(&dfa.accepting);
            groups.extend(std::iter::repeat_n(
                if options.share_across_terminals {
                    0
                } else {
                    t as u32 + 1
                },
                dfa.state_count(),
            ));
            rows.extend(
                dfa.transitions
                    .iter()
                    .map(|r| r.iter().map(|&(b, s)| (b, s + base)).collect::<Vec<_>>()),
            );
        }
        let (byte_class, class_bytes, mut table) = compact_bytes(&rows, options.budget)?;
        let alphabet = class_bytes.len();
        let minimizing = Instant::now();
        // Endpoint labels always denote exact Boolean right languages, including
        // in representation ablations. Otherwise disabling sharing would change
        // the residual observation as well as its implementation.
        let canonical_outputs = accepting.iter().map(|&f| (f, 0)).collect::<Vec<_>>();
        let canonical = minimize(&table, alphabet, &canonical_outputs);
        let mut endpoint_classes = canonical.clone();
        if options.minimize {
            let outputs = accepting
                .iter()
                .zip(&groups)
                .map(|(&f, &g)| (f, g))
                .collect::<Vec<_>>();
            let map = if options.share_across_terminals {
                canonical.clone()
            } else {
                minimize(&table, alphabet, &outputs)
            };
            let classes = map.iter().copied().max().unwrap_or(0) as usize + 1;
            let mut representatives = vec![usize::MAX; classes];
            for (s, &c) in map.iter().enumerate() {
                if representatives[c as usize] == usize::MAX {
                    representatives[c as usize] = s;
                }
            }
            let new_table = representatives
                .iter()
                .flat_map(|&s| {
                    table[s * alphabet..(s + 1) * alphabet]
                        .iter()
                        .map(|&t| map[t as usize])
                })
                .collect();
            accepting = representatives.iter().map(|&s| accepting[s]).collect();
            endpoint_classes = representatives.iter().map(|&s| canonical[s]).collect();
            for r in &mut roots {
                *r = map[*r as usize];
            }
            table = new_table;
        }
        let minimization_ms = minimizing.elapsed().as_secs_f64() * 1000.0;
        if roots.iter().any(|&r| r == 0 || accepting[r as usize]) {
            return Err(AnalysisError::Kernel(
                "terminal-root invariant failed after minimization".into(),
            ));
        }
        let future = table
            .chunks_exact(alphabet)
            .map(|row| row.iter().any(|&s| s != 0))
            .collect::<Vec<_>>();
        let root_destinations = (0..alphabet)
            .map(|b| {
                roots
                    .iter()
                    .enumerate()
                    .filter_map(|(t, &r)| {
                        let s = table[r as usize * alphabet + b];
                        (s != 0).then_some((t as u32, s))
                    })
                    .collect()
            })
            .collect();
        let stats = PreparationStats {
            terminal_count: terminals.len(),
            source_states,
            projected_states: accepting.len() - 1,
            byte_classes: alphabet,
            preparation_ms: started.elapsed().as_secs_f64() * 1000.0,
            minimization_ms,
        };
        Ok(Self {
            accepting,
            future,
            endpoint_classes,
            table,
            byte_class,
            class_bytes,
            roots,
            root_destinations,
            stats,
        })
    }

    pub fn stats(&self) -> &PreparationStats {
        &self.stats
    }
    /// Includes the dead state at coordinate zero.
    pub fn state_count(&self) -> usize {
        self.accepting.len()
    }
    pub fn terminal_roots(&self) -> &[u32] {
        &self.roots
    }
    pub fn is_accepting(&self, state: u32) -> Option<bool> {
        self.accepting.get(state as usize).copied()
    }
    pub fn can_continue(&self, state: u32) -> Option<bool> {
        self.future.get(state as usize).copied()
    }
    pub fn endpoint_class(&self, state: u32) -> Option<u32> {
        self.endpoint_classes.get(state as usize).copied()
    }
    pub fn transition(&self, state: u32, byte: u8) -> Option<u32> {
        self.table
            .get(state as usize * self.class_bytes.len() + self.byte_class[byte as usize] as usize)
            .copied()
    }
    pub fn request<'a>(&'a self, vocab: &'a crate::Vocab) -> TraceRequest<'a> {
        TraceRequest::new(self, vocab)
    }
}

fn compact_bytes(
    rows: &[Vec<(u8, u32)>],
    budget: TraceBudget,
) -> Result<([u16; 256], Vec<u8>, Vec<u32>), AnalysisError> {
    let mut ids = FxHashMap::<Arc<[u32]>, u16>::default();
    let mut columns = Vec::<Arc<[u32]>>::new();
    let mut byte_class = [0u16; 256];
    let mut class_bytes = Vec::new();
    for b in 0..256 {
        let column = rows
            .iter()
            .map(|r| {
                r.binary_search_by_key(&(b as u8), |&(byte, _)| byte)
                    .map(|i| r[i].1)
                    .unwrap_or(0)
            })
            .collect::<Vec<_>>();
        let id = if let Some(&id) = ids.get(column.as_slice()) {
            id
        } else {
            limit(
                "trace transition cells",
                rows.len().saturating_mul(columns.len() + 1),
                budget.max_cells,
            )?;
            let id = columns.len() as u16;
            let column: Arc<[u32]> = column.into();
            columns.push(column.clone());
            ids.insert(column, id);
            class_bytes.push(b as u8);
            id
        };
        byte_class[b] = id;
    }
    let mut table = Vec::with_capacity(rows.len() * columns.len());
    for s in 0..rows.len() {
        table.extend(columns.iter().map(|col| col[s]));
    }
    Ok((byte_class, class_bytes, table))
}

/// Hopcroft refinement of a total DFA, retaining all supplied roots. Initial
/// output colors may additionally prohibit cross-terminal sharing for ablation.
fn minimize(table: &[u32], alphabet: usize, outputs: &[(bool, u32)]) -> Vec<u32> {
    let n = outputs.len();
    let mut output_ids = FxHashMap::default();
    let mut blocks = Vec::<Vec<u32>>::new();
    let mut block_of = vec![0usize; n];
    for (s, &output) in outputs.iter().enumerate() {
        let next = blocks.len();
        let block = *output_ids.entry(output).or_insert_with(|| {
            blocks.push(Vec::new());
            next
        });
        block_of[s] = block;
        blocks[block].push(s as u32);
    }
    struct Predecessors {
        offsets: Vec<usize>,
        sources: Vec<u32>,
    }
    let pred = (0..alphabet)
        .map(|b| {
            let mut offsets = vec![0usize; n + 1];
            for s in 0..n {
                offsets[table[s * alphabet + b] as usize + 1] += 1;
            }
            for i in 1..=n {
                offsets[i] += offsets[i - 1];
            }
            let mut cursor = offsets[..n].to_vec();
            let mut sources = vec![0u32; n];
            for s in 0..n {
                let t = table[s * alphabet + b] as usize;
                sources[cursor[t]] = s as u32;
                cursor[t] += 1;
            }
            Predecessors { offsets, sources }
        })
        .collect::<Vec<_>>();
    let mut queue = VecDeque::new();
    let mut queued = FxHashSet::default();
    for block in 0..blocks.len() {
        for b in 0..alphabet {
            queue.push_back((block, b));
            queued.insert((block, b));
        }
    }
    let mut marked = vec![false; n];
    while let Some((splitter, b)) = queue.pop_front() {
        queued.remove(&(splitter, b));
        let p = &pred[b];
        let mut affected = FxHashMap::<usize, Vec<u32>>::default();
        for &target in &blocks[splitter] {
            for &s in &p.sources[p.offsets[target as usize]..p.offsets[target as usize + 1]] {
                affected.entry(block_of[s as usize]).or_default().push(s);
            }
        }
        // Order is deterministic for reproducible coordinates; correctness does
        // not depend on the arbitrary numeric block IDs.
        let mut affected = affected.into_iter().collect::<Vec<_>>();
        affected.sort_unstable_by_key(|&(block, _)| block);
        for (old, subset) in affected {
            if subset.len() == blocks[old].len() {
                continue;
            }
            for &s in &subset {
                marked[s as usize] = true;
            }
            let members = std::mem::take(&mut blocks[old]);
            let new = blocks.len();
            let mut inside = Vec::with_capacity(subset.len());
            let mut outside = Vec::with_capacity(members.len() - subset.len());
            for s in members {
                if marked[s as usize] {
                    inside.push(s);
                    block_of[s as usize] = new;
                } else {
                    outside.push(s);
                }
            }
            for &s in &subset {
                marked[s as usize] = false;
            }
            blocks[old] = outside;
            blocks.push(inside);
            for c in 0..alphabet {
                let add = if queued.contains(&(old, c)) || blocks[new].len() < blocks[old].len() {
                    new
                } else {
                    old
                };
                if queued.insert((add, c)) {
                    queue.push_back((add, c));
                }
            }
        }
    }
    let mut remap = FxHashMap::default();
    block_of
        .into_iter()
        .map(|block| {
            let next = remap.len() as u32;
            *remap.entry(block).or_insert(next)
        })
        .collect()
}

pub(super) struct Product {
    /// Empty vector (dead) is state zero. Reset is state one.
    pub rows: Vec<Arc<[(u32, u32)]>>,
    pub table: Vec<u32>,
    pub finals: Vec<Vec<u32>>,
}

impl Product {
    pub fn build(p: &PreparedTrace, budget: TraceBudget) -> Result<Self, AnalysisError> {
        let alphabet = p.class_bytes.len();
        limit("trace product states", 2, budget.max_states)?;
        limit(
            "trace product transition cells",
            2usize.saturating_mul(alphabet),
            budget.max_cells,
        )?;
        let dead: Arc<[(u32, u32)]> = Arc::from([]);
        let reset: Arc<[(u32, u32)]> = p
            .roots
            .iter()
            .enumerate()
            .map(|(t, &s)| (t as u32, s))
            .collect::<Vec<_>>()
            .into();
        let mut rows = vec![dead.clone(), reset.clone()];
        let mut ids = FxHashMap::default();
        ids.insert(dead, 0u32);
        ids.insert(reset, 1u32);
        let mut table = Vec::new();
        let mut memberships = p.roots.len();
        let mut source = 0;
        while source < rows.len() {
            let row = rows[source].clone();
            for b in 0..alphabet {
                let target = row
                    .iter()
                    .filter_map(|&(t, s)| {
                        let next = p.table[s as usize * alphabet + b];
                        (next != 0).then_some((t, next))
                    })
                    .collect::<Vec<_>>();
                let next = if let Some(&id) = ids.get(target.as_slice()) {
                    id
                } else {
                    limit(
                        "trace product states",
                        rows.len() + 1,
                        budget.max_states.min(u32::MAX as usize),
                    )?;
                    limit(
                        "trace product transition cells",
                        (rows.len() + 1).saturating_mul(alphabet),
                        budget.max_cells,
                    )?;
                    memberships = memberships.saturating_add(target.len());
                    limit(
                        "trace product root memberships",
                        memberships,
                        budget.max_cells,
                    )?;
                    let id = rows.len() as u32;
                    let target: Arc<[(u32, u32)]> = target.into();
                    rows.push(target.clone());
                    ids.insert(target, id);
                    id
                };
                table.push(next);
            }
            source += 1;
        }
        let mut covered = vec![false; p.state_count()];
        covered[0] = true;
        for row in &rows {
            for &(_, s) in row.iter() {
                covered[s as usize] = true;
            }
        }
        if covered.iter().any(|&c| !c) {
            return Err(AnalysisError::InvalidInput("reachable product roots do not cover every declared projected residual; product comparison would change the observation domain".into()));
        }
        let finals = rows
            .iter()
            .map(|row| {
                row.iter()
                    .filter_map(|&(t, s)| p.accepting[s as usize].then_some(t))
                    .collect()
            })
            .collect();
        Ok(Self {
            rows,
            table,
            finals,
        })
    }
}
