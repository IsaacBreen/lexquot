//! Scoped token and lexer-state equivalence.
//!
//! The L1 projection answers a one-terminal live-prefix observation, not a
//! general commit transition. L2P retains terminal completions and reset suffixes.
//! Initial-state maps are observation domains, not replacements for a runtime
//! lexer. No parser or weighted-automaton dependency is required.
#![allow(dead_code, unused_variables)]
#![doc = include_str!("../README.md")]

pub use lexquot_vocab::Vocab;
pub use lexquot_lexer::{DFA, Expr, U8Set, parse_regex};
pub use lexquot_lexer::__private::automata::lexer::{Lexer, tokenizer::{Tokenizer, TerminalResidualCoordinates}};
pub use equiv_types::{GlobalScannerStateQuotient, InternalIdMap, ManyToOneIdMap};
#[doc(hidden)]
pub mod l1;
#[doc(hidden)]
pub mod l2p;
mod equiv_types;

pub(crate) use lexquot_vocab::__private as vocab;
pub(crate) mod automata {
    pub(crate) use lexquot_finite_automata::unweighted_u32;
    pub(crate) use lexquot_lexer::__private::automata::{lexer, regex};
}
pub(crate) mod ds {
    pub(crate) use lexquot_lexer::__private::ds::{bitset, u8set};
}
pub(crate) mod error {
    #[derive(Debug, thiserror::Error)]
    pub enum Error {
        #[error("Compilation resource limit exceeded: {0}")]
        ResourceLimit(String),
        #[error("Internal analysis invariant violated: {0}")]
        InternalInvariant(String),
    }
    pub use lexquot_invariant::__private::fail_internal_invariant;
    pub fn catch_internal_invariant<T>(f: impl FnOnce() -> T) -> Result<T, Error> {
        lexquot_invariant::__private::catch_compilation_resource_limit(|| {
            lexquot_invariant::__private::catch_internal_invariant_message(f)
        }).map_err(Error::ResourceLimit)?.map_err(Error::InternalInvariant)
    }
}
pub fn compile_profile_enabled() -> bool {
    std::env::var_os("LEXQUOT_PROFILE_COMPILE").is_some()
        || std::env::var_os("LEXQUOT_PROFILE_COMPILE_SUMMARY").is_some()
}
/// Materialize exact direct byte transitions; epsilon closures remain separate.
pub fn build_flat_transition_table(tokenizer: &Tokenizer) -> Vec<u32> {
    (0..tokenizer.num_states()).flat_map(|s| {
        (0..256).map(move |b| tokenizer.get_transition(s, b as u8))
    }).collect()
}
/// Build a lexer from already-parsed terminal expressions.
pub fn lexer_from_expressions(expressions: Vec<Expr>) -> Tokenizer {
    let n = expressions.len() as u32;
    automata::lexer::compile::build_regex_monolithic(&expressions)
        .into_tokenizer(n, Some(std::sync::Arc::from(expressions.into_boxed_slice())))
}
/// Compile terminal groups while retaining exact product-trace coordinates.
/// Distinct group IDs leave terminal families as an epsilon union; equal IDs
/// request a product within that group. No parser is constructed.
pub fn lexer_with_terminal_residuals(expressions: Vec<Expr>, groups: &[u32]) -> Result<Tokenizer, AnalysisError> {
    if expressions.is_empty() || expressions.len() != groups.len() {
        return Err(AnalysisError::InvalidInput("one lexer group is required per nonempty terminal expression list".into()));
    }
    let retained: std::sync::Arc<[Expr]> = expressions.clone().into();
    automata::lexer::compile::build_partitioned_tokenizer_with_product_trace_terminal_residuals(
        &expressions, None, groups, None, retained, Some(false), true,
    ).ok_or_else(|| AnalysisError::Kernel("product-trace lexer construction declined this representation".into()))
}

#[doc(hidden)]
pub mod compat_policy;
#[doc(hidden)]
pub use compat_policy::{vocab_inplace_disallowed_intersection_enabled, vocab_reuse_dense_disallowed_slots_enabled, vocab_reuse_single_target_disallowed_enabled};

#[doc(hidden)]
pub mod scope;
#[doc(hidden)]
pub mod follows;

pub mod api;
mod canonical;
pub mod residual;
pub mod partition;
pub mod token_effect;
pub use partition::{PartitionSpec, PartitionedRequest, PartitionedAnalysis};
pub use api::{Analysis, AnalysisRequest, AnalysisError, AnalysisStats, Assurance, Backend, Budget, Domain, Observation, refine_token_partitions, verify_refinement};
pub use residual::{ProjectedRoot, ResidualDfa, ResidualRequest, ResidualAnalysis, ResidualStats, PreparedResiduals};

/// Exact all-completion trace observers. This API is distinct from the inherited
/// L1/L2P latest-completion contract and computes vocabulary classes only.
pub mod trace;
