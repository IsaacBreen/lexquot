//! Grammar-aware vocabulary equivalence without a parser or runtime dependency.
//!
//! The original GLRMask pipeline has grammar-derived scopes; a flat terminal
//! family loses those scopes and also exposes implementation-level character
//! rules as observations. This frontend restores grammar structure explicitly.
//! It contracts only *proved* regular SCCs, derives legal terminal adjacency,
//! and retains exact all-completion/right-residual observations for the result.
//! When the entire grammar is regular, a minimized DFA token-transformation
//! analysis computes its exact two-sided byte-language congruence.
//!
//! Safety is for the supplied ordinary CFG's **byte language**, not terminal
//! identities, parse trees, longest-match priorities, semantic actions, or all
//! unrelated CFGs. The old `trace` and inherited L1/L2P APIs keep their contracts.
//! No fitted CFGzip partition or GLRMask compiled object is an input.

#![doc = include_str!("../../GRAMMAR_GUIDE.md")]

mod actions;
mod dfa;
mod lower;
mod masks;
pub use crate::trace::grammar::Symbol;
use crate::trace::grammar::{GrammarSpec, PreparedGrammarTrace, Production};
use crate::trace::{PrepareOptions, PreparedTrace, TraceAnalysis, TraceBudget, TraceDfa};
use crate::{AnalysisError, Vocab};
pub use dfa::Dfa;
use serde::{Deserialize, Serialize};
use std::time::Instant;

/// An ordinary CFG over regular byte languages. `rules[n]` lists the alternative
/// right hand sides of nonterminal n; an empty RHS denotes epsilon. Terminal
/// DFAs may be nullable; preparation lifts nullability into grammar structure.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Grammar {
    pub terminals: Vec<Dfa>,
    pub rules: Vec<Vec<Vec<Symbol>>>,
    pub start: u32,
}
impl Grammar {
    pub fn prepare(&self, options: Options) -> Result<PreparedGrammar, AnalysisError> {
        PreparedGrammar::new(self, options)
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(default)]
pub struct Budget {
    pub max_nonterminals: usize,
    pub max_symbols: usize,
    pub max_input_states: usize,
    pub max_nfa_states: usize,
    pub max_dfa_states: usize,
    pub max_cells: usize,
    pub max_work: usize,
}
impl Default for Budget {
    fn default() -> Self {
        Self {
            max_nonterminals: 100_000,
            max_symbols: 1_000_000,
            max_input_states: 100_000,
            max_nfa_states: 20_000,
            max_dfa_states: 5_000,
            max_cells: 32_000_000,
            max_work: 500_000_000,
        }
    }
}
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(default)]
pub struct Options {
    pub fold_regular: bool,
    pub follow_scopes: bool,
    pub regular_actions: bool,
    pub cache_transitions: bool,
    pub budget: Budget,
    pub trace_budget: TraceBudget,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            fold_regular: true,
            follow_scopes: true,
            regular_actions: true,
            cache_transitions: true,
            budget: Budget::default(),
            trace_budget: TraceBudget::default(),
        }
    }
}
#[derive(Debug, Clone, Default, Serialize)]
pub struct PreparationStats {
    pub source_terminals: usize,
    pub source_nonterminals: usize,
    pub source_dfa_states: usize,
    pub reachable_nonterminals: usize,
    pub folded_nonterminals: usize,
    pub folded_components: usize,
    pub left_linear_components: usize,
    pub nonregular_components: usize,
    pub budget_declined_components: usize,
    pub retained_terminals: usize,
    pub retained_nonterminals: usize,
    pub retained_dfa_states: usize,
    pub root_is_regular: bool,
    pub empty_language: bool,
    pub allowed_adjacent_pairs: usize,
    pub scopes: usize,
    pub work: usize,
    pub normalization_ms: f64,
    pub engine_preparation_ms: f64,
    pub total_ms: f64,
}
#[derive(Debug, Clone, Default, Serialize)]
pub struct AnalysisStats {
    pub observation_roots: usize,
    pub reverse_columns: usize,
    pub signature_cells: usize,
    pub prepend_transitions: usize,
    pub cache_hits: usize,
    pub vocabulary_bytes: usize,
    pub work: u64,
    pub analysis_ms: f64,
    pub construction_ms: f64,
    pub initial_state_quotient_computed: bool,
}
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TokenPartition {
    pub token_ids: Vec<u32>,
    pub token_classes: Vec<u32>,
    pub classes: Vec<Vec<u32>>,
    pub representatives: Vec<u32>,
    pub dead_class: Option<u32>,
}
impl TokenPartition {
    pub fn nondead_class_count(&self) -> usize {
        self.classes.len() - usize::from(self.dead_class.is_some())
    }
    pub fn token_class(&self, id: u32) -> Option<u32> {
        self.token_ids
            .binary_search(&id)
            .ok()
            .map(|i| self.token_classes[i])
    }
}
impl From<TraceAnalysis> for TokenPartition {
    fn from(p: TraceAnalysis) -> Self {
        Self {
            token_ids: p.token_ids,
            token_classes: p.token_classes,
            classes: p.classes,
            representatives: p.representatives,
            dead_class: p.dead_class,
        }
    }
}
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum Algorithm {
    EmptyLanguage,
    RegularDfaActions,
    /// Exact prefix-viability columns; original-token commits required.
    RegularDfaMasks,
    /// Grammar-conditioned completion paths with Boolean pending endpoints.
    GrammarScopedMasks,
    UniformFoldedMasks,
    GrammarScopedTrace,
    UniformFoldedTrace,
}
#[derive(Debug, Clone, Serialize)]
pub struct Analysis {
    pub partition: TokenPartition,
    pub algorithm: Algorithm,
    pub preparation: PreparationStats,
    pub stats: AnalysisStats,
    pub contract: &'static str,
}
#[derive(Debug, Clone)]
enum Engine {
    Empty,
    Regular(dfa::Dense),
    Scoped(PreparedGrammarTrace),
    Uniform(PreparedTrace),
}
/// Reusable grammar-dependent preparation. Each call to `analyze` starts with
/// fresh token-analysis caches; it does not reuse answers from a previous call.
#[derive(Debug, Clone)]
pub struct PreparedGrammar {
    normalized: Grammar,
    regular: DfaOrNone,
    engine: Engine,
    options: Options,
    stats: PreparationStats,
}
type DfaOrNone = Option<Dfa>;
impl PreparedGrammar {
    pub fn new(input: &Grammar, options: Options) -> Result<Self, AnalysisError> {
        let started = Instant::now();
        let mut lowered = lower::lower(input, &options)?;
        lowered.stats.normalization_ms = started.elapsed().as_secs_f64() * 1000.;
        let setup = Instant::now();
        let engine = if lowered.grammar.terminals.is_empty() {
            Engine::Empty
        } else if options.regular_actions && lowered.root_regular.is_some() {
            Engine::Regular(dfa::Dense::new(
                lowered.root_regular.as_ref().unwrap(),
                &options.budget,
                &mut lowered.stats.work,
            )?)
        } else {
            let g = &lowered.grammar;
            let terminals = g
                .terminals
                .iter()
                .map(|d| TraceDfa::new(d.start, d.accepting.clone(), d.transitions.clone()))
                .collect::<Result<Vec<_>, _>>()?;
            let prepare = PrepareOptions {
                budget: options.trace_budget,
                ..Default::default()
            };
            if options.follow_scopes {
                let productions = g
                    .rules
                    .iter()
                    .enumerate()
                    .flat_map(|(lhs, ps)| {
                        ps.iter().cloned().map(move |rhs| Production {
                            lhs: lhs as u32,
                            rhs,
                        })
                    })
                    .collect();
                let scope = GrammarSpec {
                    start: g.start,
                    nonterminals: g.rules.len(),
                    productions,
                };
                let engine = PreparedGrammarTrace::new(&terminals, &scope, prepare)?;
                lowered.stats.allowed_adjacent_pairs = engine.stats().allowed_adjacent_pairs;
                lowered.stats.scopes = engine.stats().distinct_follow_scopes;
                Engine::Scoped(engine)
            } else {
                Engine::Uniform(PreparedTrace::new(&terminals, prepare)?)
            }
        };
        lowered.stats.engine_preparation_ms = setup.elapsed().as_secs_f64() * 1000.;
        lowered.stats.total_ms = started.elapsed().as_secs_f64() * 1000.;
        Ok(Self {
            normalized: lowered.grammar,
            regular: lowered.root_regular,
            engine,
            options,
            stats: lowered.stats,
        })
    }
    pub fn normalized_grammar(&self) -> &Grammar {
        &self.normalized
    }
    /// A successful regularity certificate covers the entire original start
    /// language, including epsilon; absent means only regular islands folded.
    pub fn regular_language(&self) -> Option<&Dfa> {
        self.regular.as_ref()
    }
    pub fn stats(&self) -> &PreparationStats {
        &self.stats
    }
    /// Compute a static next-token mask partition for the supplied byte language.
    ///
    /// For a certified regular language this computes the COARSEST relation
    /// that preserves viability at every byte prefix. For a nonregular CFG it
    /// compares grammar-scoped completion paths with Boolean pending endpoints,
    /// a sufficient mask relation. `algorithm` distinguishes the two:
    /// no general-CFG optimality claim is made. EOS must be tested on the original checker state.
    ///
    /// Always commit the original sampled token bytes in both the grammar
    /// checker and the model context. Do not commit these representatives.
    pub fn analyze_masks(&self, vocab: &Vocab) -> Result<Analysis, AnalysisError> {
        guard(
            "grammar vocabulary entries",
            vocab.len(),
            self.options.trace_budget.max_cells,
        )?;
        let (partition, mut stats, algorithm) = match &self.engine {
            Engine::Regular(dfa) => {
                let (p, s) = masks::analyze(
                    dfa,
                    vocab,
                    self.options.trace_budget,
                    self.options.cache_transitions,
                )?;
                (p, s, Algorithm::RegularDfaMasks)
            }
            Engine::Scoped(p) => {
                let out = p.analyze_with(
                    vocab,
                    crate::trace::EndpointPolicy::Mask,
                    self.options.cache_transitions,
                    self.options.trace_budget,
                )?;
                let s = from_trace_stats(&out.partition.stats);
                (out.partition.into(), s, Algorithm::GrammarScopedMasks)
            }
            Engine::Uniform(p) => {
                let out = p
                    .request(vocab)
                    .endpoint(crate::trace::EndpointPolicy::Mask)
                    .cache_transitions(self.options.cache_transitions)
                    .budget(self.options.trace_budget)
                    .analyze()?;
                let s = from_trace_stats(&out.stats);
                (out.into(), s, Algorithm::UniformFoldedMasks)
            }
            Engine::Empty => {
                let mut out = self.analyze(vocab)?;
                out.contract = "All ordinary nonempty tokens are dead for empty/epsilon-only language; commit ORIGINAL token bytes; EOS checked separately";
                return Ok(out);
            }
        };
        stats.construction_ms = self.stats.total_ms + stats.analysis_ms;
        Ok(Analysis {
            partition,
            stats,
            algorithm,
            preparation: self.stats.clone(),
            contract: if algorithm == Algorithm::RegularDfaMasks {
                "Exact coarsest static prefix-viability partition over all byte prefixes of the supplied regular language; commit ORIGINAL token bytes, never mask representatives; EOS checked separately"
            } else {
                "Grammar-scoped sufficient prefix-viability partition for supplied CFG; not claimed coarsest; commit ORIGINAL token bytes, never mask representatives; EOS checked separately"
            },
        })
    }

    pub fn analyze(&self, vocab: &Vocab) -> Result<Analysis, AnalysisError> {
        guard(
            "grammar vocabulary entries",
            vocab.len(),
            self.options.trace_budget.max_cells,
        )?;
        let (partition, mut stats, algorithm) = match &self.engine {
            Engine::Empty => {
                let started = Instant::now();
                let mut p = TokenPartition::default();
                let mut best = None;
                for (&id, bytes) in vocab.entries_map() {
                    if bytes.is_empty() {
                        return Err(AnalysisError::InvalidInput("empty ordinary token".into()));
                    }
                    guard(
                        "grammar token bytes",
                        bytes.len(),
                        self.options.trace_budget.max_token_bytes,
                    )?;
                    p.token_ids.push(id);
                    p.token_classes.push(0);
                    best = Some(
                        best.map_or((bytes.len(), id), |(n, i)| (n, i).min((bytes.len(), id))),
                    );
                }
                if let Some((_, id)) = best {
                    p.classes.push(p.token_ids.clone());
                    p.representatives.push(id);
                    p.dead_class = Some(0);
                }
                (
                    p,
                    AnalysisStats {
                        analysis_ms: started.elapsed().as_secs_f64() * 1000.,
                        ..Default::default()
                    },
                    Algorithm::EmptyLanguage,
                )
            }
            Engine::Regular(dfa) => {
                let (p, s) = actions::analyze(
                    dfa,
                    vocab,
                    self.options.trace_budget,
                    self.options.cache_transitions,
                )?;
                (p, s, Algorithm::RegularDfaActions)
            }
            Engine::Scoped(p) => {
                let out = p.analyze_with(
                    vocab,
                    crate::trace::EndpointPolicy::Residual,
                    self.options.cache_transitions,
                    self.options.trace_budget,
                )?;
                let s = from_trace_stats(&out.partition.stats);
                (out.partition.into(), s, Algorithm::GrammarScopedTrace)
            }
            Engine::Uniform(p) => {
                let out = p
                    .request(vocab)
                    .cache_transitions(self.options.cache_transitions)
                    .budget(self.options.trace_budget)
                    .analyze()?;
                let s = from_trace_stats(&out.stats);
                (out.into(), s, Algorithm::UniformFoldedTrace)
            }
        };
        stats.construction_ms = self.stats.total_ms + stats.analysis_ms;
        Ok(Analysis {
            partition,
            stats,
            algorithm,
            preparation: self.stats.clone(),
            contract: "Exact byte-language substitution safety for the supplied CFG; no parse-tree, longest-match, semantic-action, or LM-token substitution claim",
        })
    }
}
fn from_trace_stats(s: &crate::trace::TraceStats) -> AnalysisStats {
    AnalysisStats {
        observation_roots: s.observation_roots,
        reverse_columns: s.reverse_columns,
        signature_cells: s.signature_cells,
        prepend_transitions: s.prepend_transitions,
        cache_hits: s.transition_cache_hits,
        vocabulary_bytes: s.vocabulary_bytes,
        work: s.work,
        analysis_ms: s.total_ms,
        ..Default::default()
    }
}
fn guard(resource: &'static str, requested: usize, limit: usize) -> Result<(), AnalysisError> {
    if requested > limit {
        Err(AnalysisError::BudgetExceeded {
            resource,
            requested: requested as u64,
            limit: limit as u64,
        })
    } else {
        Ok(())
    }
}
fn spend(work: &mut usize, amount: usize, limit: usize) -> Result<(), AnalysisError> {
    *work = work.saturating_add(amount);
    guard("grammar preparation work", *work, limit)
}
