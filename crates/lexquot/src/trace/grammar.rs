//! Grammar-scoped, collision-free vocabulary equivalence.
//!
//! Restores the grammar-derived follow scope used by GLRMask's L1/L2P path,
//! while retaining the exact all-completion/right-residual contract of `trace`.
//! This does not construct a parser, a terminal DWA, or a runtime constraint.
//! Equality preserves substitution in the supplied CFG (and grammars using only its live terminals and a
//! subset of the derived adjacent-terminal pairs), not all CFGs on its labels.
//!
//! Terminals are positive/nonnullable byte languages. Represent nullable
//! terminals by explicit CFG epsilon alternatives before supplying the grammar.
//! Lexical priorities, maximal munch and external predicates are NOT implicit.

use super::engine::Columns;
use super::language::{EMPTY, END, Languages, Node};
use super::{
    EndpointPolicy, PrepareOptions, PreparedTrace, TraceAlgorithm, TraceAnalysis, TraceBudget,
    TraceDfa, TraceStats, limit, work,
};
use crate::{AnalysisError, Vocab};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeSet, VecDeque};
use std::time::Instant;

/// Indices refer to the supplied terminal list and the declared nonterminal count.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Symbol {
    Terminal(u32),
    Nonterminal(u32),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Production {
    pub lhs: u32,
    pub rhs: Vec<Symbol>,
}

/// Unordered CFG rules. An empty right hand side denotes epsilon.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GrammarSpec {
    pub start: u32,
    pub nonterminals: usize,
    pub productions: Vec<Production>,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct GrammarPreparationStats {
    pub supplied_terminals: usize,
    pub reachable_productive_terminals: usize,
    pub supplied_productions: usize,
    pub retained_productions: usize,
    pub allowed_adjacent_pairs: usize,
    pub distinct_follow_scopes: usize,
    pub scoped_residual_coordinates: usize,
    pub projected_boolean_states: usize,
    pub preparation_ms: f64,
    pub grammar_work: u64,
}

/// Metadata makes the grammar-conditioned contract explicit in every result.
#[derive(Debug, Clone, Serialize)]
pub struct GrammarAnalysis {
    pub partition: TraceAnalysis,
    pub grammar: GrammarPreparationStats,
    pub contract: &'static str,
}

/// Productive and reachable grammar structure plus exact nullable/FIRST/LAST
/// summaries. The adjacency relation is derived, never guessed from token text.
#[derive(Debug, Clone)]
pub struct GrammarScope {
    pub live_terminals: Vec<bool>,
    pub allowed_follows: Vec<Vec<u32>>,
    pub retained_productions: Vec<Production>,
    pub nullable_nonterminals: Vec<bool>,
    pub start: u32,
    pub nonterminals: usize,
    pub work: u64,
}

impl GrammarScope {
    pub fn derive(
        g: &GrammarSpec,
        terminals: usize,
        budget: TraceBudget,
    ) -> Result<Self, AnalysisError> {
        if g.nonterminals == 0 || g.start as usize >= g.nonterminals {
            return Err(AnalysisError::InvalidInput(
                "invalid grammar start/nonterminal count".into(),
            ));
        }
        limit("grammar nonterminals", g.nonterminals, budget.max_states)?;
        limit("grammar terminals", terminals, budget.max_states)?;
        limit("grammar productions", g.productions.len(), budget.max_cells)?;
        limit(
            "grammar analysis cells",
            g.nonterminals.saturating_mul(terminals.max(1)),
            budget.max_cells,
        )?;
        let mut spent = 0;
        let mut rhs_cells = 0usize;
        for p in &g.productions {
            if p.lhs as usize >= g.nonterminals {
                return Err(AnalysisError::InvalidInput(
                    "production lhs outside grammar".into(),
                ));
            }
            rhs_cells = rhs_cells
                .checked_add(p.rhs.len())
                .ok_or_else(|| AnalysisError::InvalidInput("grammar size overflow".into()))?;
            limit("grammar rhs cells", rhs_cells, budget.max_cells)?;
            for &sym in &p.rhs {
                let valid = match sym {
                    Symbol::Terminal(t) => (t as usize) < terminals,
                    Symbol::Nonterminal(n) => (n as usize) < g.nonterminals,
                };
                if !valid {
                    return Err(AnalysisError::InvalidInput(
                        "production symbol outside grammar".into(),
                    ));
                }
            }
        }
        let mut productive = vec![false; g.nonterminals];
        loop {
            let mut changed = false;
            for p in &g.productions {
                work(&mut spent, p.rhs.len() + 1, budget.max_work)?;
                if !productive[p.lhs as usize]
                    && p.rhs.iter().all(|s| match s {
                        Symbol::Terminal(_) => true,
                        Symbol::Nonterminal(n) => productive[*n as usize],
                    })
                {
                    productive[p.lhs as usize] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        if !productive[g.start as usize] {
            return Err(AnalysisError::InvalidInput(
                "grammar has empty start language".into(),
            ));
        }
        let productive_rules = g
            .productions
            .iter()
            .filter(|p| {
                p.rhs.iter().all(|s| match s {
                    Symbol::Terminal(_) => true,
                    Symbol::Nonterminal(n) => productive[*n as usize],
                })
            })
            .cloned()
            .collect::<Vec<_>>();
        let mut by_lhs = vec![Vec::new(); g.nonterminals];
        for (i, p) in productive_rules.iter().enumerate() {
            by_lhs[p.lhs as usize].push(i);
        }
        let mut reached = vec![false; g.nonterminals];
        let mut live = vec![false; terminals];
        let mut q = VecDeque::from([g.start]);
        while let Some(n) = q.pop_front() {
            if reached[n as usize] {
                continue;
            }
            reached[n as usize] = true;
            for &i in &by_lhs[n as usize] {
                for s in &productive_rules[i].rhs {
                    work(&mut spent, 1, budget.max_work)?;
                    match s {
                        Symbol::Terminal(t) => live[*t as usize] = true,
                        Symbol::Nonterminal(m) => {
                            if !reached[*m as usize] {
                                q.push_back(*m)
                            }
                        }
                    }
                }
            }
        }
        let rules = productive_rules
            .into_iter()
            .filter(|p| reached[p.lhs as usize])
            .collect::<Vec<_>>();
        let mut nullable = vec![false; g.nonterminals];
        loop {
            let mut changed = false;
            for p in &rules {
                work(&mut spent, p.rhs.len() + 1, budget.max_work)?;
                if !nullable[p.lhs as usize]
                    && p.rhs
                        .iter()
                        .all(|s| matches!(s, Symbol::Nonterminal(n) if nullable[*n as usize]))
                {
                    nullable[p.lhs as usize] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut first = vec![BTreeSet::<u32>::new(); g.nonterminals];
        let mut last = first.clone();
        loop {
            let mut changed = false;
            for p in &rules {
                for backwards in [false, true] {
                    let current = if backwards { &mut last } else { &mut first };
                    let iter: Box<dyn Iterator<Item = &Symbol>> = if backwards {
                        Box::new(p.rhs.iter().rev())
                    } else {
                        Box::new(p.rhs.iter())
                    };
                    let mut add = BTreeSet::new();
                    for sym in iter {
                        match *sym {
                            Symbol::Terminal(t) => {
                                add.insert(t);
                                work(&mut spent, 1, budget.max_work)?;
                                break;
                            }
                            Symbol::Nonterminal(n) => {
                                work(&mut spent, current[n as usize].len() + 1, budget.max_work)?;
                                add.extend(current[n as usize].iter().copied());
                                if !nullable[n as usize] {
                                    break;
                                }
                            }
                        }
                    }
                    let prior = current[p.lhs as usize].len();
                    current[p.lhs as usize].extend(add);
                    changed |= prior != current[p.lhs as usize].len();
                }
            }
            if !changed {
                break;
            }
        }
        let mut follows = vec![BTreeSet::<u32>::new(); terminals];
        let mut pair_count = 0usize;
        for p in &rules {
            let mut left = BTreeSet::new();
            for sym in &p.rhs {
                let (starts, ends, empty) = match *sym {
                    Symbol::Terminal(t) => (BTreeSet::from([t]), BTreeSet::from([t]), false),
                    Symbol::Nonterminal(n) => (
                        first[n as usize].clone(),
                        last[n as usize].clone(),
                        nullable[n as usize],
                    ),
                };
                work(
                    &mut spent,
                    left.len()
                        .saturating_mul(starts.len())
                        .saturating_add(ends.len() + 1),
                    budget.max_work,
                )?;
                for &a in &left {
                    let before = follows[a as usize].len();
                    follows[a as usize].extend(starts.iter().copied());
                    pair_count += follows[a as usize].len() - before;
                    limit("grammar adjacent pairs", pair_count, budget.max_cells)?;
                }
                if !empty {
                    left.clear();
                }
                left.extend(ends);
            }
        }
        limit(
            "grammar adjacent pairs",
            follows.iter().map(BTreeSet::len).sum(),
            budget.max_cells,
        )?;
        Ok(Self {
            live_terminals: live,
            allowed_follows: follows
                .into_iter()
                .map(|x| x.into_iter().collect())
                .collect(),
            retained_productions: rules,
            nullable_nonterminals: nullable,
            start: g.start,
            nonterminals: g.nonterminals,
            work: spent,
        })
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
struct First {
    pending: u32,
    tail: u32,
}

/// Reusable preparation. Coordinates are Boolean residual × legal follow scope;
/// equal scopes/residuals share work without mixing distinct terminal labels.
#[derive(Debug, Clone)]
pub struct PreparedGrammarTrace {
    prepared: PreparedTrace,
    scopes: Vec<Vec<u32>>,
    coordinates: Vec<(usize, u32)>,
    transitions: Vec<Vec<u32>>,
    reset_destinations: Vec<Vec<Vec<(u32, u32)>>>,
    stats: GrammarPreparationStats,
}

impl PreparedGrammarTrace {
    pub fn new(
        terminals: &[TraceDfa],
        grammar: &GrammarSpec,
        options: PrepareOptions,
    ) -> Result<Self, AnalysisError> {
        let started = Instant::now();
        let scope = GrammarScope::derive(grammar, terminals.len(), options.budget)?;
        Self::from_scope(
            terminals,
            &scope,
            grammar.productions.len(),
            options,
            started,
        )
    }
    fn from_scope(
        terminals: &[TraceDfa],
        g: &GrammarScope,
        supplied_rules: usize,
        options: PrepareOptions,
        started: Instant,
    ) -> Result<Self, AnalysisError> {
        let p = PreparedTrace::new(terminals, options)?;
        let alphabet = p.class_bytes.len();
        let mut scope_ids = FxHashMap::<Vec<u32>, usize>::default();
        let mut scopes = Vec::new();
        let mut terminal_scope = vec![None; terminals.len()];
        for (t, allowed) in g.allowed_follows.iter().enumerate() {
            if !g.live_terminals[t] {
                continue;
            }
            let id = *scope_ids.entry(allowed.clone()).or_insert_with(|| {
                let i = scopes.len();
                scopes.push(allowed.clone());
                i
            });
            terminal_scope[t] = Some(id);
        }
        let mut coordinates = vec![(usize::MAX, 0)];
        let mut coordinate_ids = FxHashMap::<(usize, u32), u32>::default();
        let mut spent = g.work;
        for (t, s) in terminal_scope.iter().enumerate() {
            let Some(scope) = *s else { continue };
            let root = p.roots[t];
            if coordinate_ids.contains_key(&(scope, root)) {
                continue;
            }
            limit(
                "grammar-scoped residual coordinates",
                coordinates.len() + 1,
                options.budget.max_states,
            )?;
            coordinate_ids.insert((scope, root), coordinates.len() as u32);
            coordinates.push((scope, root));
            let mut queue = vec![root];
            while let Some(q) = queue.pop() {
                work(&mut spent, alphabet + 1, options.budget.max_work)?;
                for b in 0..alphabet {
                    let target = p.table[q as usize * alphabet + b];
                    if target != 0 && !coordinate_ids.contains_key(&(scope, target)) {
                        limit(
                            "grammar-scoped residual coordinates",
                            coordinates.len() + 1,
                            options.budget.max_states,
                        )?;
                        coordinate_ids.insert((scope, target), coordinates.len() as u32);
                        coordinates.push((scope, target));
                        queue.push(target);
                    }
                }
            }
        }
        limit(
            "grammar-scoped transition cells",
            coordinates.len().saturating_mul(alphabet),
            options.budget.max_cells,
        )?;
        let transitions = coordinates
            .iter()
            .map(|&(scope, q)| {
                (0..alphabet)
                    .map(|b| {
                        let dest = p.table[q as usize * alphabet + b];
                        if dest == 0 {
                            0
                        } else {
                            coordinate_ids[&(scope, dest)]
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        limit(
            "grammar reset destination cells",
            scopes
                .iter()
                .map(Vec::len)
                .sum::<usize>()
                .saturating_mul(alphabet),
            options.budget.max_cells,
        )?;
        let mut reset_destinations = Vec::new();
        for allowed in &scopes {
            let mut per_byte = Vec::new();
            for b in 0..alphabet {
                let mut dests = Vec::new();
                for &t in allowed {
                    work(&mut spent, 1, options.budget.max_work)?;
                    let target = p.table[p.roots[t as usize] as usize * alphabet + b];
                    if target != 0 {
                        dests.push((
                            t,
                            coordinate_ids[&(
                                terminal_scope[t as usize].expect("reachable successor scope"),
                                target,
                            )],
                        ));
                    }
                }
                per_byte.push(dests);
            }
            reset_destinations.push(per_byte);
        }
        let stats = GrammarPreparationStats {
            supplied_terminals: terminals.len(),
            reachable_productive_terminals: g.live_terminals.iter().filter(|x| **x).count(),
            supplied_productions: supplied_rules,
            retained_productions: g.retained_productions.len(),
            allowed_adjacent_pairs: g.allowed_follows.iter().map(Vec::len).sum(),
            distinct_follow_scopes: scopes.len(),
            scoped_residual_coordinates: coordinates.len() - 1,
            projected_boolean_states: p.state_count() - 1,
            preparation_ms: started.elapsed().as_secs_f64() * 1000.,
            grammar_work: spent,
        };
        Ok(Self {
            prepared: p,
            scopes,
            coordinates,
            transitions,
            reset_destinations,
            stats,
        })
    }
    pub fn stats(&self) -> &GrammarPreparationStats {
        &self.stats
    }
    /// Fresh analysis caches; preparation may be shared across vocabulary calls.
    pub fn analyze(
        &self,
        vocab: &Vocab,
        budget: TraceBudget,
    ) -> Result<GrammarAnalysis, AnalysisError> {
        self.analyze_with(vocab, EndpointPolicy::Residual, true, budget)
    }
    pub fn analyze_with(
        &self,
        vocab: &Vocab,
        endpoint: EndpointPolicy,
        cache: bool,
        budget: TraceBudget,
    ) -> Result<GrammarAnalysis, AnalysisError> {
        let started = Instant::now();
        let mut stats = TraceStats::default();
        let tokens = vocab
            .entries_map()
            .iter()
            .map(|(&i, b)| (i, b.as_slice()))
            .collect::<Vec<_>>();
        limit(
            "grammar trace vocabulary entries",
            tokens.len(),
            budget.max_cells,
        )?;
        for &(_, bytes) in &tokens {
            if bytes.is_empty() {
                return Err(AnalysisError::InvalidInput(
                    "empty ordinary token is not admitted".into(),
                ));
            }
            limit(
                "grammar trace token bytes",
                bytes.len(),
                budget.max_token_bytes,
            )?;
            stats.vocabulary_bytes =
                stats
                    .vocabulary_bytes
                    .checked_add(bytes.len())
                    .ok_or_else(|| {
                        AnalysisError::InvalidInput("vocabulary byte size overflow".into())
                    })?;
        }
        stats.token_count = tokens.len();
        stats.observation_roots = self.coordinates.len() - 1;
        let p = &self.prepared;
        let pending = |q: usize| {
            if !p.future[q] {
                0
            } else if endpoint == EndpointPolicy::Mask {
                1
            } else {
                p.endpoint_classes[q] + 1
            }
        };
        let mut columns = Columns::<First>::new(self.coordinates.len(), budget);
        let mut languages = Languages::new(budget)?;
        let initial = columns.intern(
            self.coordinates
                .iter()
                .map(|&(_, q)| First {
                    pending: pending(q as usize),
                    tail: if p.accepting[q as usize] { END } else { EMPTY },
                })
                .collect(),
        )?;
        let mut ids = Vec::with_capacity(tokens.len());
        for &(_, bytes) in &tokens {
            let mut source = initial;
            for &byte in bytes.iter().rev() {
                work(&mut stats.work, 1, budget.max_work)?;
                let b = p.byte_class[byte as usize];
                if cache {
                    if let Some(&target) = columns.transitions.get(&(source, b)) {
                        stats.transition_cache_hits += 1;
                        source = target;
                        continue;
                    }
                }
                let child = columns.values[source as usize].clone();
                let mut resets = Vec::with_capacity(self.scopes.len());
                for scope in 0..self.scopes.len() {
                    let mut node = Node::empty();
                    for &(t, dest) in &self.reset_destinations[scope][b as usize] {
                        let v = child[dest as usize];
                        if v.pending != 0 {
                            node.pending.push((t, v.pending));
                        }
                        if v.tail != EMPTY {
                            node.edges.push((t, v.tail));
                        }
                    }
                    work(
                        &mut stats.work,
                        self.reset_destinations[scope][b as usize].len() + 1,
                        budget.max_work,
                    )?;
                    resets.push(languages.intern(node)?);
                }
                let mut column = Vec::with_capacity(self.coordinates.len());
                for (i, &(scope, q)) in self.coordinates.iter().enumerate() {
                    let mut v = child[self.transitions[i][b as usize] as usize];
                    if p.accepting[q as usize] {
                        v.tail = languages.union(v.tail, resets[scope])?;
                    }
                    column.push(v);
                }
                work(&mut stats.work, column.len(), budget.max_work)?;
                let target = columns.intern(column)?;
                if cache {
                    columns.cache(source, b, target)?;
                }
                stats.prepend_transitions += 1;
                source = target;
            }
            ids.push(source);
        }
        stats.reverse_columns = columns.values.len();
        stats.signature_cells = stats.reverse_columns.saturating_mul(self.coordinates.len());
        stats.language_nodes = languages.len();
        stats.language_cells = languages.cells();
        stats.union_pairs = languages.union_count();
        work(&mut stats.work, languages.union_work, budget.max_work)?;
        let mut class_ids = FxHashMap::<u32, u32>::default();
        let mut classes = Vec::<Vec<u32>>::new();
        let mut token_classes = Vec::new();
        let mut reps = Vec::new();
        let mut lengths = Vec::new();
        let mut dead_class = None;
        for (&(id, bytes), &column) in tokens.iter().zip(&ids) {
            let next = classes.len() as u32;
            let cls = *class_ids.entry(column).or_insert_with(|| {
                classes.push(Vec::new());
                reps.push(id);
                lengths.push(bytes.len());
                next
            });
            classes[cls as usize].push(id);
            token_classes.push(cls);
            if (bytes.len(), id) < (lengths[cls as usize], reps[cls as usize]) {
                lengths[cls as usize] = bytes.len();
                reps[cls as usize] = id;
            }
            if columns.values[column as usize]
                .iter()
                .all(|v| v.pending == 0 && v.tail == EMPTY)
            {
                if dead_class.is_some_and(|d| d != cls) {
                    return Err(AnalysisError::Kernel(
                        "multiple dead grammar-scoped classes".into(),
                    ));
                }
                dead_class = Some(cls);
            }
        }
        stats.total_ms = started.elapsed().as_secs_f64() * 1000.;
        let partition = TraceAnalysis {
            endpoint_policy: endpoint,
            algorithm: TraceAlgorithm::Projected,
            token_ids: tokens.iter().map(|t| t.0).collect(),
            token_classes,
            classes,
            representatives: reps,
            dead_class,
            stats,
        };
        Ok(GrammarAnalysis {
            partition,
            grammar: self.stats.clone(),
            contract: if endpoint == EndpointPolicy::Residual {
                "CFG-derived adjacent-terminal scope; exact all-completion right residuals; representative-safe for supplied CFG"
            } else {
                "CFG-derived adjacent-terminal scope; current-token mask only; commit original bytes"
            },
        })
    }
}
