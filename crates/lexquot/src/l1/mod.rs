//! Single-terminal projected live-prefix equivalence.
//!
//! This is the actual production projected-residual algorithm. Terminal labels
//! remain on root mappings and results, not on the shared residual state machine.
use crate::{InternalIdMap, Lexer, ManyToOneIdMap, Tokenizer, Vocab};
use std::sync::Arc;
mod common;
mod projected;
pub(crate) use projected::external_survivor_columns;
mod support;
pub use projected::{
    L1VocabEquivResult, build, build_projected_vocab_equivalence, prepare_finite_vocab_projection,
    should_use_projected,
};

/// Optional byte-sorted parent vocabulary, borrowed without copying its tokens.
#[derive(Clone, Copy)]
pub struct LexicalOrderView<'a> {
    pub token_entries_sorted: &'a [(u32, Arc<[u8]>)],
    pub original_to_internal: &'a [u32],
}
/// Advanced kernel input. Use the checked analysis API for external inputs.
#[derive(Clone, Copy)]
pub struct BuildInput<'a> {
    pub partition_label: &'a str,
    pub tokenizer: &'a Tokenizer,
    pub vocab: &'a Vocab,
    pub active_terminals: &'a [bool],
    pub flat_trans: &'a Arc<[u32]>,
    pub transitions_by_byte: Option<&'a [u32]>,
    pub initial_state_map: Option<&'a ManyToOneIdMap>,
    pub initial_state_domain_is_exact: bool,
    pub subset_parent_order: Option<LexicalOrderView<'a>>,
    pub id_map_only: bool,
}
#[derive(Debug, Clone, Default)]
pub struct L1Profile {
    pub id_map_ms: f64,
    pub relation_assembly_ms: f64,
    pub compact_ms: f64,
    pub split_terminal_dwa_total_ms: f64,
    pub global_merge_ms: f64,
    pub determinize_ms: f64,
    pub minimize_ms: f64,
}
/// Exact compressed L1 observations. `by_terminal[t]` contains
/// `(state_class, token_classes)` rows. These are mask observations, not commit
/// transitions. An empty relation with a nonempty map is an id-map-only result.
#[derive(Debug, Clone)]
pub struct L1Relation {
    pub id_map: InternalIdMap,
    pub by_terminal: Vec<Vec<(u32, Vec<u32>)>>,
    pub profile: L1Profile,
}
#[derive(Debug)]
pub struct PreparedVocabulary {
    pub token_entries_sorted: Arc<[(u32, Arc<[u8]>)]>,
    pub original_to_internal: Arc<[u32]>,
}
impl crate::vocab::VocabDerivedArtifact for PreparedVocabulary {}
pub fn seed_vocabulary_order(vocab: &Vocab, entries: Arc<[(u32, Arc<[u8]>)]>, ids: Arc<[u32]>) {
    if vocab
        .vocab_derived_cache_get::<PreparedVocabulary>()
        .is_none()
    {
        vocab.vocab_derived_cache_set(Arc::new(PreparedVocabulary {
            token_entries_sorted: entries,
            original_to_internal: ids,
        }));
    }
}
pub fn prepared_l1_identity_vocab_order(vocab: &Vocab) -> Arc<PreparedVocabulary> {
    if let Some(cached) = vocab.vocab_derived_cache_get::<PreparedVocabulary>() {
        return cached;
    }
    let mut entries = vocab
        .entries_map()
        .iter()
        .map(|(&id, b)| (id, Arc::<[u8]>::from(b.clone())))
        .collect::<Vec<_>>();
    entries
        .sort_unstable_by(|(a, x), (b, y)| x.first().cmp(&y.first()).then(x.cmp(y)).then(a.cmp(b)));
    let mut ids = vec![u32::MAX; vocab.max_token_id() as usize + 1];
    for (i, (id, _)) in entries.iter().enumerate() {
        ids[*id as usize] = i as u32;
    }
    let result = Arc::new(PreparedVocabulary {
        token_entries_sorted: entries.into(),
        original_to_internal: ids.into(),
    });
    vocab.vocab_derived_cache_set(Arc::clone(&result));
    result
}
fn collect_active_terminal_signature(
    tokenizer: &Tokenizer,
    state: u32,
    active: &[bool],
) -> Vec<u32> {
    let mut signature = tokenizer
        .matched_terminals_iter(state)
        .chain(
            tokenizer
                .tokens_accessible_from_state(state)
                .iter()
                .map(|t| t as u32),
        )
        .filter(|&t| active.get(t as usize).copied().unwrap_or(false))
        .collect::<Vec<_>>();
    signature.sort_unstable();
    signature.dedup();
    signature
}
