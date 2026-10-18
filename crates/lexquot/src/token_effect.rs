//! Collision-free vocabulary analysis for grammars over regular terminals.
//!
//! Unlike L1 live-prefix observations, these keys retain every terminal
//! completion and the complete right-language residual at the token endpoint.
//! Terminals must be nonnullable. Lexing is nondeterministic segmentation, not
//! an implicit longest-match or priority policy. A returned class is a safe
//! token-substitution refinement for every CFG over the supplied terminals.
//! It need not be the coarsest grammar-specific syntactic congruence.
//!
//! Initial observations use a Boolean residual union; terminal identities are
//! restored by the caller's terminal/root membership. Subsequent completions
//! use a lazily determinized, terminal-labelled reset lexer. All interning is
//! structural. Digests used in cross-partition stitching are only filters:
//! matching candidates are compared structurally before they can be merged.

use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};
use std::time::Instant;

use serde::{Deserialize, Serialize};

const UNKNOWN: u32 = u32::MAX;
type Map<K, V> = HashMap<K, V, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;

#[derive(Debug, thiserror::Error)]
pub enum EffectError {
    #[error("invalid token-effect input: {0}")]
    Invalid(String),
    #[error("token-effect budget exceeded for {0}")]
    Budget(&'static str),
}

/// A complete-match Boolean DFA. Missing edges reject; state IDs are local.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TerminalAutomaton {
    pub start: u32,
    pub accepting: Vec<bool>,
    pub transitions: Vec<Vec<(u8, u32)>>,
}

impl TerminalAutomaton {
    pub fn new(
        start: u32,
        accepting: Vec<bool>,
        mut transitions: Vec<Vec<(u8, u32)>>,
    ) -> Result<Self, EffectError> {
        let n = accepting.len();
        if n == 0 || n != transitions.len() || start as usize >= n {
            return Err(EffectError::Invalid(
                "malformed terminal DFA dimensions".into(),
            ));
        }
        if accepting[start as usize] {
            return Err(EffectError::Invalid(
                "nullable lexical terminal: lift optionality into the grammar".into(),
            ));
        }
        for row in &mut transitions {
            row.sort_unstable();
            if row.windows(2).any(|w| w[0].0 == w[1].0) || row.iter().any(|e| e.1 as usize >= n) {
                return Err(EffectError::Invalid(
                    "duplicate byte or invalid transition target".into(),
                ));
            }
        }
        Ok(Self {
            start,
            accepting,
            transitions,
        })
    }

    /// Import the ordinary single-expression lexer compiler, whose root is 0.
    /// Frontend allocation occurs before analysis budgets and must be bounded
    /// separately by a caller handling untrusted regular expressions.
    pub fn from_expr(expr: &crate::Expr) -> Result<Self, EffectError> {
        let dfa = crate::automata::lexer::compile::compile_terminal_expr_dfa(expr);
        if dfa.has_epsilon_transitions() {
            return Err(EffectError::Invalid(
                "terminal DFA must be deterministic and epsilon-free".into(),
            ));
        }
        Self::new(
            0,
            (0..dfa.num_states())
                .map(|s| dfa.finalizers(s as u32).contains(0))
                .collect(),
            (0..dfa.num_states())
                .map(|s| dfa.transitions(s as u32).collect())
                .collect(),
        )
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct EffectOptions {
    /// Compare against materializing initial multi-terminal product states.
    pub combined_initial: bool,
    pub partition_first_byte: bool,
    pub cache_suffixes: bool,
    pub stitch_partitions: bool,
    /// Disabling minimization retains raw endpoint identities and may return
    /// a finer relation. It is not a same-observation speed ablation.
    pub minimize_residuals: bool,
    pub max_states: usize,
    pub max_nodes: usize,
    pub max_steps: u64,
    pub max_token_bytes: usize,
    pub max_table_cells: usize,
    /// Diagnostic regression switch: exact comparison must resolve collisions.
    #[doc(hidden)]
    pub constant_stitch_digest: bool,
}

impl Default for EffectOptions {
    fn default() -> Self {
        Self {
            combined_initial: false,
            partition_first_byte: true,
            cache_suffixes: true,
            stitch_partitions: true,
            minimize_residuals: true,
            max_states: 200_000,
            max_nodes: 4_000_000,
            max_steps: 2_000_000_000,
            max_token_bytes: 4096,
            max_table_cells: 64_000_000,
            constant_stitch_digest: false,
        }
    }
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct EffectStats {
    pub source_states: usize,
    pub residual_states: usize,
    pub byte_classes: usize,
    pub initial_states: usize,
    pub reset_states: usize,
    pub trace_nodes: usize,
    pub suffix_strings: usize,
    pub suffix_cache_hits: usize,
    pub partitions: usize,
    pub initial_row_groups: usize,
    pub local_classes: usize,
    pub token_classes: usize,
    pub stitching_comparisons: usize,
    pub scan_steps: u64,
    pub prepare_ms: f64,
    pub suffix_ms: f64,
    pub refine_ms: f64,
    pub stitch_ms: f64,
    pub total_ms: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct EffectAnalysis {
    /// Original IDs, sorted independently of their (possibly sparse) values.
    pub token_ids: Vec<u32>,
    /// Class for the token at the corresponding position of `token_ids`.
    pub classes: Vec<u32>,
    pub representatives: Vec<u32>,
    pub stats: EffectStats,
}

/// A symbolic single-terminal byte run `alphabet{min,max}`. This specialization
/// never materializes counter states, even when the bound is billions.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SymbolicByteRun {
    pub alphabet: Vec<u8>,
    pub min: u64,
    pub max: Option<u64>,
}

impl SymbolicByteRun {
    /// For one nonempty bounded byte-class terminal, contextual equivalence
    /// over ALL grammars on that terminal is exactly (invalid byte, or length).
    /// Same-length strings have identical byte-class actions. Distinct lengths
    /// are distinguished by a context ending at a grammar production's maximum
    /// length (finite max), or starting at its minimum length (positive min).
    /// This is NOT a general bounded-regex clipping rule. With min=0,max=None,
    /// length classes remain safe but deliberately finer than necessary.
    pub fn analyze(&self, tokens: &[(u32, Vec<u8>)]) -> Result<EffectAnalysis, EffectError> {
        let started = Instant::now();
        if self.max.is_some_and(|m| m < self.min) {
            return Err(EffectError::Invalid(
                "run upper bound below lower bound".into(),
            ));
        }
        let mut allowed = [false; 256];
        for &b in &self.alphabet {
            allowed[b as usize] = true;
        }
        let mut sorted = tokens.iter().collect::<Vec<_>>();
        sorted.sort_by_key(|t| t.0);
        if sorted.windows(2).any(|w| w[0].0 == w[1].0) {
            return Err(EffectError::Invalid("duplicate original token ID".into()));
        }
        let mut keys = Map::<Option<usize>, u32>::default();
        let mut classes = Vec::new();
        let mut representatives = Vec::<usize>::new();
        let mut scan_steps = 0u64;
        for (i, (_, bytes)) in sorted.iter().enumerate() {
            if bytes.is_empty() {
                return Err(EffectError::Invalid(
                    "empty/control token supplied as ordinary bytes".into(),
                ));
            }
            let key = (self.max != Some(0)
                && bytes.iter().all(|&b| {
                    scan_steps += 1;
                    allowed[b as usize]
                }))
            .then_some(bytes.len());
            let before = keys.len();
            let c = intern(&mut keys, key);
            classes.push(c);
            if keys.len() != before {
                representatives.push(i);
            } else {
                let j = representatives[c as usize];
                if (bytes.len(), sorted[i].0) < (sorted[j].1.len(), sorted[j].0) {
                    representatives[c as usize] = i;
                }
            }
        }
        Ok(EffectAnalysis {
            token_ids: sorted.iter().map(|t| t.0).collect(),
            classes,
            representatives: representatives.into_iter().map(|i| sorted[i].0).collect(),
            stats: EffectStats {
                token_classes: keys.len(),
                scan_steps,
                total_ms: elapsed_ms(started),
                ..Default::default()
            },
        })
    }
}

/// Terminal-local complete-match residuals, with all supplied roots retained.
pub struct PreparedTokenEffects {
    delta: Vec<Vec<u32>>,
    accepting: Vec<bool>,
    terminal_starts: Vec<u32>,
    byte_class: [u8; 256],
    options: EffectOptions,
    stats: EffectStats,
}

fn elapsed_ms(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
}

fn intern<K: Eq + Hash + Clone>(map: &mut Map<K, u32>, key: K) -> u32 {
    let next = map.len() as u32;
    *map.entry(key).or_insert(next)
}

impl PreparedTokenEffects {
    pub fn new(
        terminals: &[TerminalAutomaton],
        options: EffectOptions,
    ) -> Result<Self, EffectError> {
        let started = Instant::now();
        if terminals.is_empty() {
            return Err(EffectError::Invalid("no lexical terminals".into()));
        }
        let n = terminals
            .iter()
            .try_fold(1usize, |s, d| s.checked_add(d.accepting.len()))
            .ok_or(EffectError::Budget("residual state count overflow"))?;
        if n > options.max_states || n >= u32::MAX as usize {
            return Err(EffectError::Budget("source residual states"));
        }
        if n.saturating_mul(256) > options.max_table_cells {
            return Err(EffectError::Budget("source transition cells"));
        }
        let mut dense = vec![[0u32; 256]; n];
        let mut finals = vec![false; n];
        let mut starts = Vec::new();
        let mut offset = 1usize;
        for terminal in terminals {
            // Public data can have been constructed without `new`: validate it.
            let checked = TerminalAutomaton::new(
                terminal.start,
                terminal.accepting.clone(),
                terminal.transitions.clone(),
            )?;
            starts.push(offset as u32 + checked.start);
            for (s, row) in checked.transitions.iter().enumerate() {
                finals[offset + s] = checked.accepting[s];
                for &(b, t) in row {
                    dense[offset + s][b as usize] = offset as u32 + t;
                }
            }
            offset += checked.accepting.len();
        }
        // Restricting the alphabet here is exact column equality on ALL states,
        // not discarding future-language observations outside a partition.
        let mut alphabet = Map::<Vec<u32>, u32>::default();
        let mut byte_class = [0u8; 256];
        let mut bytes = Vec::new();
        for b in 0..256 {
            let col = dense.iter().map(|row| row[b]).collect::<Vec<_>>();
            let before = alphabet.len();
            let c = intern(&mut alphabet, col);
            if alphabet.len() != before {
                bytes.push(b);
            }
            byte_class[b] = c as u8;
        }
        let delta = dense
            .iter()
            .map(|row| bytes.iter().map(|&b| row[b]).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        drop(dense);
        let mut classes = if options.minimize_residuals {
            finals.iter().map(|&a| u32::from(a)).collect::<Vec<_>>()
        } else {
            (0..n as u32).collect()
        };
        if options.minimize_residuals {
            let mut work = 0u64;
            loop {
                work = work.saturating_add((n * bytes.len()) as u64);
                if work > options.max_steps {
                    return Err(EffectError::Budget("residual minimization work"));
                }
                let mut keys = Map::<(bool, Vec<u32>), u32>::default();
                let next = delta
                    .iter()
                    .enumerate()
                    .map(|(s, row)| {
                        intern(
                            &mut keys,
                            (
                                finals[s],
                                row.iter().map(|&t| classes[t as usize]).collect(),
                            ),
                        )
                    })
                    .collect::<Vec<_>>();
                if next == classes {
                    break;
                }
                classes = next;
            }
        }
        // State zero is the implicit dead state's class, by canonical insertion
        // order. Finality remains a completed-match predicate, NOT live-prefix.
        let k = classes.iter().copied().max().unwrap_or(0) as usize + 1;
        let mut new_delta = vec![Vec::new(); k];
        let mut new_finals = vec![false; k];
        for s in 0..n {
            let c = classes[s] as usize;
            if new_delta[c].is_empty() {
                new_delta[c] = delta[s].iter().map(|&t| classes[t as usize]).collect();
                new_finals[c] = finals[s];
            }
        }
        let stats = EffectStats {
            source_states: n - 1,
            residual_states: k - 1,
            byte_classes: bytes.len(),
            prepare_ms: elapsed_ms(started),
            ..Default::default()
        };
        Ok(Self {
            delta: new_delta,
            accepting: new_finals,
            terminal_starts: starts.into_iter().map(|s| classes[s as usize]).collect(),
            byte_class,
            options,
            stats,
        })
    }

    pub fn stats(&self) -> &EffectStats {
        &self.stats
    }

    /// Analyze only ordinary, nonempty byte tokens. No EOS/control token is
    /// silently reinterpreted as an empty string. Duplicate spellings survive.
    pub fn analyze(&self, tokens: &[(u32, Vec<u8>)]) -> Result<EffectAnalysis, EffectError> {
        let started = Instant::now();
        let mut sorted = tokens.iter().collect::<Vec<_>>();
        sorted.sort_by_key(|t| t.0);
        if sorted.windows(2).any(|w| w[0].0 == w[1].0) {
            return Err(EffectError::Invalid("duplicate original token ID".into()));
        }
        for (_, bytes) in &sorted {
            if bytes.is_empty() {
                return Err(EffectError::Invalid(
                    "empty/control token supplied as ordinary bytes".into(),
                ));
            }
            if bytes.len() > self.options.max_token_bytes {
                return Err(EffectError::Budget("token byte length"));
            }
        }
        if sorted.len() >= u32::MAX as usize {
            return Err(EffectError::Budget("vocabulary size"));
        }
        let token_ids = sorted.iter().map(|t| t.0).collect::<Vec<_>>();
        let bytes = sorted.iter().map(|t| t.1.as_slice()).collect::<Vec<_>>();
        let mut run = Run::new(self)?;
        let suffix_started = Instant::now();
        let suffixes = bytes
            .iter()
            .map(|b| run.suffixes(b))
            .collect::<Result<Vec<_>, _>>()?;
        run.stats.suffix_ms = elapsed_ms(suffix_started);
        let initial_count = if self.options.combined_initial {
            run.complete_product()?;
            run.combined.len()
        } else {
            self.delta.len()
        };
        run.stats.initial_states = initial_count.saturating_sub(1);
        let mut parts = BTreeMap::<u16, Vec<usize>>::new();
        for (i, token) in bytes.iter().enumerate() {
            let p = if self.options.partition_first_byte {
                self.byte_class[token[0] as usize] as u16
            } else {
                256
            };
            parts.entry(p).or_default().push(i);
        }
        run.stats.partitions = parts.len();
        let refine_started = Instant::now();
        let mut local_of_token = vec![0u32; bytes.len()];
        let mut local_reps = Vec::<usize>::new();
        for (partition, members) in parts {
            let mut local = vec![0u32; members.len()];
            let mut count = usize::from(!members.is_empty());
            let mut row_groups = Map::<(u32, Vec<u32>), u32>::default();
            for root in 1..initial_count as u32 {
                if partition != 256 {
                    let c = partition as u8;
                    let (target, labels) = if self.options.combined_initial {
                        let labels = run.finals(root);
                        let target = run.step(root, c)?;
                        (target, labels)
                    } else {
                        (
                            self.delta[root as usize][c as usize],
                            vec![u32::from(self.accepting[root as usize])],
                        )
                    };
                    // No completion before the first byte and a dead first
                    // transition make the entire row constant on this shard.
                    if target == 0
                        && if self.options.combined_initial {
                            labels.is_empty()
                        } else {
                            !self.accepting[root as usize]
                        }
                    {
                        continue;
                    }
                    let before = row_groups.len();
                    intern(&mut row_groups, (target, labels));
                    if row_groups.len() == before {
                        continue;
                    }
                }
                run.stats.initial_row_groups += 1;
                let mut keys = Map::<(u32, Observation), u32>::default();
                for (j, &i) in members.iter().enumerate() {
                    let obs = run.observe(root, bytes[i], &suffixes[i])?;
                    local[j] = intern(&mut keys, (local[j], obs));
                }
                count = keys.len();
                if count == members.len() {
                    break;
                }
            }
            let base = local_reps.len() as u32;
            local_reps.resize(local_reps.len() + count, usize::MAX);
            for (j, &i) in members.iter().enumerate() {
                let c = base + local[j];
                local_of_token[i] = c;
                let old = &mut local_reps[c as usize];
                if *old == usize::MAX
                    || (bytes[i].len(), token_ids[i]) < (bytes[*old].len(), token_ids[*old])
                {
                    *old = i;
                }
            }
        }
        run.stats.refine_ms = elapsed_ms(refine_started);
        run.stats.local_classes = local_reps.len();
        let stitch_started = Instant::now();
        let mut global_reps = Vec::<usize>::new();
        let mut local_to_global = Vec::new();
        let mut digest_buckets = Map::<u64, Vec<u32>>::default();
        for &i in &local_reps {
            let mut digest = rustc_hash::FxHasher::default();
            if self.options.stitch_partitions {
                for r in 1..initial_count as u32 {
                    run.observe(r, bytes[i], &suffixes[i])?.hash(&mut digest);
                }
            }
            let hash = if self.options.constant_stitch_digest {
                0
            } else {
                digest.finish()
            };
            let candidates = digest_buckets.get(&hash).cloned().unwrap_or_default();
            let mut equal = None;
            if self.options.stitch_partitions {
                'candidate: for c in candidates {
                    run.stats.stitching_comparisons += 1;
                    let j = global_reps[c as usize];
                    for r in 1..initial_count as u32 {
                        if run.observe(r, bytes[i], &suffixes[i])?
                            != run.observe(r, bytes[j], &suffixes[j])?
                        {
                            continue 'candidate;
                        }
                    }
                    equal = Some(c);
                    break;
                }
            }
            let c = if let Some(c) = equal {
                c
            } else {
                let c = global_reps.len() as u32;
                global_reps.push(i);
                digest_buckets.entry(hash).or_default().push(c);
                c
            };
            if (bytes[i].len(), token_ids[i])
                < (
                    bytes[global_reps[c as usize]].len(),
                    token_ids[global_reps[c as usize]],
                )
            {
                global_reps[c as usize] = i;
            }
            local_to_global.push(c);
        }
        let classes = local_of_token
            .iter()
            .map(|&c| local_to_global[c as usize])
            .collect::<Vec<_>>();
        run.stats.stitch_ms = elapsed_ms(stitch_started);
        run.stats.token_classes = global_reps.len();
        run.stats.reset_states = run.combined.len();
        run.stats.trace_nodes = run.nodes.len();
        run.stats.total_ms = elapsed_ms(started);
        Ok(EffectAnalysis {
            token_ids,
            classes,
            representatives: global_reps.into_iter().map(|i| sorted[i].0).collect(),
            stats: run.stats,
        })
    }
}

/// A node describes a finite terminal-trace graph with exact pending residuals.
/// Multiple equal-labelled edges are a set of alternatives, not an unchecked
/// sum/hash. This structural representation can refine semantic trace equality.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Observation {
    endpoint: u32,
    edges: Vec<(u32, u32)>,
}

struct Run<'a> {
    prep: &'a PreparedTokenEffects,
    combined: Vec<Vec<(u32, u32)>>,
    combined_ids: Map<Vec<(u32, u32)>, u32>,
    transitions: Vec<Vec<u32>>,
    reset: u32,
    nodes: Map<Observation, u32>,
    suffix_cache: Map<Vec<u8>, u32>,
    stats: EffectStats,
}

impl<'a> Run<'a> {
    fn new(prep: &'a PreparedTokenEffects) -> Result<Self, EffectError> {
        if prep.options.max_nodes < 2 {
            return Err(EffectError::Budget("terminal trace nodes"));
        }
        let mut out = Self {
            prep,
            combined: Vec::new(),
            combined_ids: Map::default(),
            transitions: Vec::new(),
            reset: 0,
            nodes: Map::default(),
            suffix_cache: Map::default(),
            stats: prep.stats.clone(),
        };
        out.add_combined(Vec::new())?; // dead state zero
        out.reset = out.add_combined(
            prep.terminal_starts
                .iter()
                .enumerate()
                .filter(|(_, r)| **r != 0)
                .map(|(t, &r)| (t as u32, r))
                .collect(),
        )?;
        // Node 0 rejects every nonempty continuation; node 1 is boundary epsilon.
        out.nodes.insert(
            Observation {
                endpoint: 0,
                edges: Vec::new(),
            },
            0,
        );
        out.nodes.insert(
            Observation {
                endpoint: UNKNOWN,
                edges: Vec::new(),
            },
            1,
        );
        Ok(out)
    }
    fn spend(&mut self, amount: u64) -> Result<(), EffectError> {
        self.stats.scan_steps = self.stats.scan_steps.saturating_add(amount);
        if self.stats.scan_steps > self.prep.options.max_steps {
            Err(EffectError::Budget("token scan work"))
        } else {
            Ok(())
        }
    }
    fn add_combined(&mut self, key: Vec<(u32, u32)>) -> Result<u32, EffectError> {
        if let Some(&id) = self.combined_ids.get(&key) {
            return Ok(id);
        }
        let id = self.combined.len() as u32;
        if self.combined.len() >= self.prep.options.max_states
            || self
                .combined
                .len()
                .saturating_mul(self.prep.stats.byte_classes)
                >= self.prep.options.max_table_cells
        {
            return Err(EffectError::Budget("multi-terminal reset states"));
        }
        self.combined_ids.insert(key.clone(), id);
        self.combined.push(key);
        self.transitions
            .push(vec![UNKNOWN; self.prep.stats.byte_classes]);
        Ok(id)
    }
    fn step(&mut self, state: u32, byte_class: u8) -> Result<u32, EffectError> {
        let known = self.transitions[state as usize][byte_class as usize];
        if known != UNKNOWN {
            return Ok(known);
        }
        let key = self.combined[state as usize]
            .iter()
            .filter_map(|&(t, r)| {
                let next = self.prep.delta[r as usize][byte_class as usize];
                (next != 0).then_some((t, next))
            })
            .collect::<Vec<_>>();
        let id = self.add_combined(key)?;
        self.transitions[state as usize][byte_class as usize] = id;
        Ok(id)
    }
    fn finals(&self, state: u32) -> Vec<u32> {
        self.combined[state as usize]
            .iter()
            .filter(|(_, r)| self.prep.accepting[*r as usize])
            .map(|&(t, _)| t)
            .collect()
    }
    fn complete_product(&mut self) -> Result<(), EffectError> {
        let mut s = 0;
        while s < self.combined.len() {
            for b in 0..self.prep.stats.byte_classes {
                self.spend(1)?;
                self.step(s as u32, b as u8)?;
            }
            s += 1;
        }
        Ok(())
    }
    fn suffixes(&mut self, token: &[u8]) -> Result<Vec<u32>, EffectError> {
        let mut suffix = vec![0; token.len() + 1];
        suffix[token.len()] = 1;
        for i in (0..token.len()).rev() {
            if self.prep.options.cache_suffixes {
                if let Some(&node) = self.suffix_cache.get(&token[i..]) {
                    suffix[i] = node;
                    self.stats.suffix_cache_hits += 1;
                    continue;
                }
            }
            self.stats.suffix_strings += 1;
            let mut state = self.reset;
            let mut edges = Vec::new();
            for j in i..token.len() {
                self.spend(1)?;
                state = self.step(state, self.prep.byte_class[token[j] as usize])?;
                if state == 0 {
                    break;
                }
                if suffix[j + 1] != 0 {
                    edges.extend(self.finals(state).into_iter().map(|t| (t, suffix[j + 1])));
                }
            }
            edges.sort_unstable();
            edges.dedup();
            let key = Observation {
                endpoint: state,
                edges,
            };
            if self.nodes.len() >= self.prep.options.max_nodes {
                return Err(EffectError::Budget("terminal trace nodes"));
            }
            let node = intern(&mut self.nodes, key);
            suffix[i] = node;
            if self.prep.options.cache_suffixes {
                self.suffix_cache.insert(token[i..].to_vec(), node);
            }
        }
        Ok(suffix)
    }
    fn observe(
        &mut self,
        root: u32,
        token: &[u8],
        suffix: &[u32],
    ) -> Result<Observation, EffectError> {
        let mut state = root;
        let mut edges = Vec::new();
        if suffix[0] != 0 {
            if self.prep.options.combined_initial {
                edges.extend(self.finals(state).into_iter().map(|t| (t, suffix[0])));
            } else if self.prep.accepting[state as usize] {
                edges.push((0, suffix[0]));
            }
        }
        for (j, &byte) in token.iter().enumerate() {
            self.spend(1)?;
            let b = self.prep.byte_class[byte as usize];
            state = if self.prep.options.combined_initial {
                self.step(state, b)?
            } else {
                self.prep.delta[state as usize][b as usize]
            };
            if state == 0 {
                break;
            }
            if suffix[j + 1] != 0 {
                if self.prep.options.combined_initial {
                    edges.extend(self.finals(state).into_iter().map(|t| (t, suffix[j + 1])));
                } else if self.prep.accepting[state as usize] {
                    edges.push((0, suffix[j + 1]));
                }
            }
        }
        edges.sort_unstable();
        edges.dedup();
        Ok(Observation {
            endpoint: state,
            edges,
        })
    }
}
