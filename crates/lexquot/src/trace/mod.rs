//! Exact vocabulary quotienting with projected first-terminal observations.
//!
//! Unlike the inherited L2P observer, this module retains **all** terminal
//! completion positions. Regular terminals must not accept the empty string.
//! Every live residual is an admitted token-start coordinate, including states
//! unreachable from a caller's distinguished reset root. Terminal identity is
//! retained when lifting a projected observation, not stored on every residual.
//!
//! [`EndpointPolicy::Mask`] retains only current-token viability information and
//! requires committing the original token bytes. [`EndpointPolicy::Residual`]
//! additionally retains terminal residual right languages. Under ordinary CFG
//! semantics over the supplied nonempty regular terminal languages (without
//! external value-dependent constraints or lexical priority), this stronger
//! observer is sufficient for representative substitution. Neither policy is a
//! claim to compute the coarsest grammar-language congruence.
//!
//! Hash maps in this module compare complete keys. Hash collisions cannot merge
//! distinct observations. A reverse automaton shares exact observation columns
//! across vocabulary suffixes. No lexer-initial-state quotient is computed.

mod automata;
mod engine;
/// Grammar-conditioned vocabulary equivalence; derives safe follow scopes from a CFG.
pub mod grammar;
mod language;

pub use automata::{PreparedTrace, TraceDfa};

use crate::{AnalysisError, Vocab};
use serde::{Deserialize, Serialize};

/// Information retained about an unfinished terminal at a token boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EndpointPolicy {
    /// Only its terminal identity and existence of a nonempty continuation.
    /// Original bytes, not the representative, must be committed afterwards.
    Mask,
    /// Its terminal identity and residual right-language class.
    Residual,
}

/// The two backends compute the same observation when product-root coverage is
/// complete. The product backend checks that condition rather than guessing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TraceAlgorithm {
    Projected,
    Product,
}

/// Bounds apply to materialized analysis structures, not the regular-expression
/// frontend that a caller may use before constructing a [`TraceDfa`].
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct TraceBudget {
    pub max_states: usize,
    pub max_cells: usize,
    pub max_reverse_columns: usize,
    pub max_language_nodes: usize,
    pub max_union_pairs: usize,
    pub max_token_bytes: usize,
    pub max_work: u64,
}

impl Default for TraceBudget {
    fn default() -> Self {
        Self {
            max_states: 100_000,
            max_cells: 32_000_000,
            max_reverse_columns: 2_000_000,
            max_language_nodes: 2_000_000,
            max_union_pairs: 4_000_000,
            max_token_bytes: 4096,
            max_work: 1_000_000_000,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct PrepareOptions {
    pub minimize: bool,
    pub share_across_terminals: bool,
    pub budget: TraceBudget,
}

impl Default for PrepareOptions {
    fn default() -> Self {
        Self {
            minimize: true,
            share_across_terminals: true,
            budget: TraceBudget::default(),
        }
    }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PreparationStats {
    pub terminal_count: usize,
    pub source_states: usize,
    pub projected_states: usize,
    pub byte_classes: usize,
    pub preparation_ms: f64,
    pub minimization_ms: f64,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TraceStats {
    pub total_ms: f64,
    pub product_ms: f64,
    pub product_states: usize,
    pub observation_roots: usize,
    pub vocabulary_bytes: usize,
    pub token_count: usize,
    pub reverse_columns: usize,
    pub prepend_transitions: usize,
    pub transition_cache_hits: usize,
    pub language_nodes: usize,
    pub language_cells: usize,
    pub union_pairs: usize,
    pub work: u64,
    pub signature_cells: usize,
    pub state_quotient_computed: bool,
}

/// Token classes include an optional single globally lexical-dead class. That
/// class is useful for exact partition comparisons; a mask consumer rejects it.
/// This is not the same as grammar-specific invalidity in a particular context.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceAnalysis {
    pub endpoint_policy: EndpointPolicy,
    pub algorithm: TraceAlgorithm,
    pub token_ids: Vec<u32>,
    pub token_classes: Vec<u32>,
    pub classes: Vec<Vec<u32>>,
    pub representatives: Vec<u32>,
    pub dead_class: Option<u32>,
    pub stats: TraceStats,
}

impl TraceAnalysis {
    pub fn token_class(&self, original: u32) -> Option<u32> {
        self.token_ids
            .binary_search(&original)
            .ok()
            .map(|i| self.token_classes[i])
    }

    pub fn nondead_class_count(&self) -> usize {
        self.classes.len() - usize::from(self.dead_class.is_some())
    }
}

/// A fresh analysis has fresh reverse-column and trace-language caches. Reusing
/// [`PreparedTrace`] reuses only the terminal automata, not prior token answers.
pub struct TraceRequest<'a> {
    pub(crate) prepared: &'a PreparedTrace,
    pub(crate) vocab: &'a Vocab,
    pub(crate) endpoint: EndpointPolicy,
    pub(crate) algorithm: TraceAlgorithm,
    pub(crate) cache: bool,
    pub(crate) byte_classes: bool,
    pub(crate) budget: TraceBudget,
}

impl<'a> TraceRequest<'a> {
    pub fn new(prepared: &'a PreparedTrace, vocab: &'a Vocab) -> Self {
        Self {
            prepared,
            vocab,
            endpoint: EndpointPolicy::Residual,
            algorithm: TraceAlgorithm::Projected,
            cache: true,
            byte_classes: true,
            budget: TraceBudget::default(),
        }
    }

    pub fn endpoint(mut self, policy: EndpointPolicy) -> Self {
        self.endpoint = policy;
        self
    }

    pub fn algorithm(mut self, algorithm: TraceAlgorithm) -> Self {
        self.algorithm = algorithm;
        self
    }

    pub fn cache_transitions(mut self, cache: bool) -> Self {
        self.cache = cache;
        self
    }

    pub fn byte_classes(mut self, enabled: bool) -> Self {
        self.byte_classes = enabled;
        self
    }

    pub fn budget(mut self, budget: TraceBudget) -> Self {
        self.budget = budget;
        self
    }

    pub fn analyze(self) -> Result<TraceAnalysis, AnalysisError> {
        engine::analyze(self)
    }
}

pub(crate) fn limit(resource: &'static str, n: usize, bound: usize) -> Result<(), AnalysisError> {
    if n > bound {
        Err(AnalysisError::BudgetExceeded {
            resource,
            requested: n as u64,
            limit: bound as u64,
        })
    } else {
        Ok(())
    }
}

pub(crate) fn work(n: &mut u64, add: usize, bound: u64) -> Result<(), AnalysisError> {
    *n = n
        .checked_add(add as u64)
        .ok_or_else(|| AnalysisError::InvalidInput("trace work counter overflow".into()))?;
    if *n > bound {
        Err(AnalysisError::BudgetExceeded {
            resource: "trace work",
            requested: *n,
            limit: bound,
        })
    } else {
        Ok(())
    }
}
