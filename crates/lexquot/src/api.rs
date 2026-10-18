//! Checked entry points and explicit observation scopes.
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::time::Instant;

use crate::{InternalIdMap, Lexer, ManyToOneIdMap, Tokenizer, Vocab};

/// What one analysis is allowed to observe. Neither contract is a licence to
/// replace tokens during commit or replace the runtime lexer's transition table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Observation {
    /// The terminal set that remains live after consuming the whole token,
    /// without resetting to another terminal inside that token.
    L1,
    /// Completed-terminal traces, reset suffixes, and pending future terminals.
    L2P,
}

/// Algorithm choice, independent of the observation being requested.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Backend {
    /// Exact projected L1; collision-free canonical L2P.
    #[default]
    Auto,
    /// Independent scalar scanning and structurally interned observations.
    Canonical,
    /// Existing GLRMask production kernels. L2P uses probabilistic fingerprints;
    /// use `verify(true)` to certify returned merges against canonical keys.
    Production,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assurance {
    ExactObservation,
    FingerprintAssisted,
    CanonicallyVerified,
}

/// Resource limits are errors, never permission to return an incomplete quotient.
#[derive(Debug, Clone, Copy)]
pub struct Budget {
    /// Maximum materialized coordinate/signature cells. The canonical backend
    /// stores distinct columns and refines rows online, not the full Q-by-V table.
    pub max_table_cells: usize,
    pub max_canonical_nodes: usize,
    pub max_byte_steps: u64,
    pub max_map_entries: usize,
    pub max_token_bytes: usize,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            max_table_cells: 8_000_000,
            max_canonical_nodes: 2_000_000,
            max_byte_steps: 100_000_000,
            max_map_entries: 10_000_000,
            max_token_bytes: 4096,
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum AnalysisError {
    #[error("invalid analysis input: {0}")]
    InvalidInput(String),
    #[error("analysis budget exceeded for {resource}: requested {requested}, limit {limit}")]
    BudgetExceeded {
        resource: &'static str,
        requested: u64,
        limit: u64,
    },
    #[error("{axis} class merges distinguishable original IDs {left} and {right}")]
    UnsoundMerge {
        axis: &'static str,
        left: u32,
        right: u32,
    },
    #[error("analysis kernel failed: {0}")]
    Kernel(String),
}

#[derive(Debug, Clone, Default)]
pub struct AnalysisStats {
    pub total_ms: f64,
    pub verification_ms: f64,
    pub byte_steps: u64,
    pub canonical_nodes: usize,
    pub reset_suffix_scans: usize,
    pub table_cells: usize,
}

/// The explicit domain over which equivalence is established.
#[derive(Debug, Clone)]
pub struct Domain {
    pub name: String,
    pub observation: Observation,
    pub initial_states: Vec<u32>,
    pub token_ids: Vec<u32>,
    pub terminal_ids: Vec<u32>,
}

#[derive(Debug, Clone)]
pub struct Analysis {
    pub(crate) domain: Domain,
    pub(crate) maps: InternalIdMap,
    pub(crate) assurance: Assurance,
    pub(crate) stats: AnalysisStats,
}

impl Analysis {
    pub fn domain(&self) -> &Domain {
        &self.domain
    }
    pub fn maps(&self) -> &InternalIdMap {
        &self.maps
    }
    pub fn assurance(&self) -> Assurance {
        self.assurance
    }
    pub fn stats(&self) -> &AnalysisStats {
        &self.stats
    }
    /// `None` means outside this analysis domain, not equivalent to dead input.
    pub fn token_class(&self, id: u32) -> Option<u32> {
        mapped_class(&self.maps.vocab_tokens, id)
    }
    /// A class here is valid at token starts for this observation only.
    pub fn state_class(&self, id: u32) -> Option<u32> {
        mapped_class(&self.maps.tokenizer_states, id)
    }
    pub fn token_class_count(&self) -> usize {
        self.maps.vocab_tokens.internal_to_originals.len()
    }
    pub fn state_class_count(&self) -> usize {
        self.maps.tokenizer_states.internal_to_originals.len()
    }
}

fn mapped_class(map: &ManyToOneIdMap, id: u32) -> Option<u32> {
    map.original_to_internal
        .get(id as usize)
        .copied()
        .filter(|&c| c != u32::MAX)
}

/// A reusable query builder. The lexer and vocabulary are borrowed; each result
/// records its own scope. A restricted start set never restricts reset suffixes.
pub struct AnalysisRequest<'a> {
    pub(crate) lexer: &'a Tokenizer,
    pub(crate) vocab: &'a Vocab,
    pub(crate) observation: Observation,
    pub(crate) initial_states: Option<Vec<u32>>,
    pub(crate) terminals: Option<Vec<u32>>,
    pub(crate) follows: BTreeSet<(u32, u32)>,
    pub(crate) budget: Budget,
    backend: Backend,
    verify: bool,
    name: String,
}

impl<'a> AnalysisRequest<'a> {
    pub fn new(lexer: &'a Tokenizer, vocab: &'a Vocab, observation: Observation) -> Self {
        Self {
            lexer,
            vocab,
            observation,
            initial_states: None,
            terminals: None,
            follows: BTreeSet::new(),
            budget: Budget::default(),
            backend: Backend::Auto,
            verify: false,
            name: "standalone".into(),
        }
    }
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.name = name.into();
        self
    }
    pub fn backend(mut self, backend: Backend) -> Self {
        self.backend = backend;
        self
    }
    pub fn verify(mut self, enabled: bool) -> Self {
        self.verify = enabled;
        self
    }
    pub fn budget(mut self, budget: Budget) -> Self {
        self.budget = budget;
        self
    }
    pub fn initial_states(mut self, states: impl IntoIterator<Item = u32>) -> Self {
        self.initial_states = Some(states.into_iter().collect());
        self
    }
    pub fn terminals(mut self, terminals: impl IntoIterator<Item = u32>) -> Self {
        self.terminals = Some(terminals.into_iter().collect());
        self
    }
    /// Follow restrictions refer to grammar-terminal IDs, not model tokens.
    /// IGNORE-transparent policies must be normalized by the caller.
    pub fn forbidden_follows(mut self, pairs: impl IntoIterator<Item = (u32, u32)>) -> Self {
        self.follows = pairs.into_iter().collect();
        self
    }

    pub fn analyze(self) -> Result<Analysis, AnalysisError> {
        let started = Instant::now();
        let domain = self.checked_domain()?;
        let canonical = self.backend == Backend::Canonical
            || (self.backend == Backend::Auto && self.observation == Observation::L2P)
            || domain.initial_states.is_empty()
            || domain.token_ids.is_empty();
        let (maps, mut stats, mut assurance) = if canonical {
            let (maps, stats) = crate::canonical::analyze(&self, &domain)?;
            (maps, stats, Assurance::ExactObservation)
        } else {
            let maps = self.production(&domain)?;
            let assurance = if self.observation == Observation::L1 {
                Assurance::ExactObservation
            } else {
                Assurance::FingerprintAssisted
            };
            (maps, AnalysisStats::default(), assurance)
        };
        if self.verify && !canonical {
            let verify_started = Instant::now();
            let (reference, _) = crate::canonical::analyze(&self, &domain)?;
            verify_refinement(&maps.vocab_tokens, &reference.vocab_tokens, "token")?;
            verify_refinement(
                &maps.tokenizer_states,
                &reference.tokenizer_states,
                "initial state",
            )?;
            stats.verification_ms = verify_started.elapsed().as_secs_f64() * 1000.0;
            assurance = Assurance::CanonicallyVerified;
        }
        for &id in &domain.token_ids {
            if mapped_class(&maps.vocab_tokens, id).is_none() {
                return Err(AnalysisError::Kernel(format!(
                    "token {id} is missing from output domain"
                )));
            }
        }
        for &id in &domain.initial_states {
            if mapped_class(&maps.tokenizer_states, id).is_none() {
                return Err(AnalysisError::Kernel(format!(
                    "initial state {id} is missing from output domain"
                )));
            }
        }
        stats.total_ms = started.elapsed().as_secs_f64() * 1000.0;
        Ok(Analysis {
            domain,
            maps,
            assurance,
            stats,
        })
    }

    fn checked_domain(&self) -> Result<Domain, AnalysisError> {
        let n = self.lexer.num_states();
        // Dense ordinary-byte ID maps must be bounded before either backend.
        // Vocab::max_token_id excludes exact-only control IDs; those remain
        // entirely outside the equivalence domain and need no dense storage.
        check_limit(
            "state map entries",
            n as u64,
            self.budget.max_map_entries as u64,
        )?;
        let max_id = self.vocab.entries_map().keys().copied().max();
        if let Some(id) = max_id {
            check_limit(
                "token map entries",
                u64::from(id) + 1,
                self.budget.max_map_entries as u64,
            )?;
        }
        for (&id, bytes) in self.vocab.entries_map() {
            if bytes.is_empty() {
                return Err(AnalysisError::InvalidInput(format!(
                    "ordinary token {id} has empty bytes; keep special tokens outside this analysis"
                )));
            }
            check_limit(
                "token byte length",
                bytes.len() as u64,
                self.budget.max_token_bytes as u64,
            )?;
        }
        let mut states = self
            .initial_states
            .clone()
            .unwrap_or_else(|| (0..n).collect());
        states.sort_unstable();
        states.dedup();
        if states.iter().any(|&s| s >= n) {
            return Err(AnalysisError::InvalidInput(
                "initial state is outside the lexer".into(),
            ));
        }
        let observed = (0..n)
            .flat_map(|s| {
                self.lexer
                    .matched_terminals_iter(s)
                    .chain(self.lexer.possible_future_terminals_iter(s))
                    .collect::<Vec<_>>()
            })
            .collect::<BTreeSet<_>>();
        let mut terminals = self
            .terminals
            .clone()
            .unwrap_or_else(|| observed.iter().copied().collect());
        terminals.sort_unstable();
        terminals.dedup();
        if terminals.iter().any(|t| !observed.contains(t)) {
            return Err(AnalysisError::InvalidInput(
                "terminal is not observed anywhere in the lexer".into(),
            ));
        }
        if self.observation == Observation::L1 && !self.follows.is_empty() {
            return Err(AnalysisError::InvalidInput(
                "L1 does not observe terminal-to-terminal follows; use L2P".into(),
            ));
        }
        if self
            .follows
            .iter()
            .any(|(a, b)| !observed.contains(a) || !observed.contains(b))
        {
            return Err(AnalysisError::InvalidInput(
                "follow restriction contains an unknown terminal".into(),
            ));
        }
        Ok(Domain {
            name: self.name.clone(),
            observation: self.observation,
            initial_states: states,
            token_ids: self.vocab.entries_map().keys().copied().collect(),
            terminal_ids: terminals,
        })
    }

    fn production(&self, domain: &Domain) -> Result<InternalIdMap, AnalysisError> {
        let n = self.lexer.num_states() as usize;
        check_limit(
            "production flat transition cells",
            (n as u64).saturating_mul(256),
            self.budget.max_table_cells as u64,
        )?;
        let group_count = (0..self.lexer.num_states())
            .flat_map(|s| {
                self.lexer
                    .matched_terminals_iter(s)
                    .chain(self.lexer.possible_future_terminals_iter(s))
                    .collect::<Vec<_>>()
            })
            .max()
            .map_or(0, |t| t as usize + 1);
        let mut active = vec![false; group_count];
        for &t in &domain.terminal_ids {
            active[t as usize] = true;
        }
        let domain_map = map_from_classes(
            n,
            &domain.initial_states,
            &(0..domain.initial_states.len() as u32).collect::<Vec<_>>(),
        );
        let flat: Arc<[u32]> = crate::build_flat_transition_table(self.lexer).into();
        crate::error::catch_internal_invariant(|| {
            if self.observation == Observation::L1 {
                let result = crate::l1::build(crate::l1::BuildInput {
                    partition_label: "standalone",
                    tokenizer: self.lexer,
                    vocab: self.vocab,
                    active_terminals: &active,
                    flat_trans: &flat,
                    transitions_by_byte: None,
                    initial_state_map: Some(&domain_map),
                    initial_state_domain_is_exact: true,
                    subset_parent_order: None,
                    id_map_only: false,
                });
                if let Some(result) = result {
                    return Ok(result.id_map);
                }
                // A declined representation is not an empty language.
                return crate::canonical::analyze(self, domain).map(|(maps, _)| maps);
            }
            let mut follows = BTreeMap::<u32, crate::ds::bitset::BitSet>::new();
            for &(a, b) in &self.follows {
                follows
                    .entry(a)
                    .or_insert_with(|| crate::ds::bitset::BitSet::new(group_count))
                    .set(b as usize);
            }
            let (mut maps, _) = crate::l2p::combined::analyze_equivalences_with_group_filter(
                "standalone",
                self.lexer,
                self.vocab,
                &follows,
                None,
                true,
                None,
                Some(&active),
                None,
                None,
                0.0,
                Some(&flat),
                None,
                Some(&domain_map),
                false,
                Some(crate::l2p::combined::ScopedEquivalenceDomain {
                    continuation_state_map: None,
                }),
                None,
                None,
                None,
            );
            maps.tokenizer_states = crate::scope::restrict_quotient_to_initial_domain(
                &maps.tokenizer_states,
                &domain_map,
            )
            .ok_or_else(|| {
                AnalysisError::Kernel(
                    "production state map does not cover the requested starts".into(),
                )
            })?;
            Ok(maps)
        })
        .map_err(|e| AnalysisError::Kernel(e.to_string()))?
    }
}

pub(crate) fn check_limit(
    resource: &'static str,
    requested: u64,
    limit: u64,
) -> Result<(), AnalysisError> {
    if requested > limit {
        Err(AnalysisError::BudgetExceeded {
            resource,
            requested,
            limit,
        })
    } else {
        Ok(())
    }
}

pub(crate) fn map_from_classes(size: usize, originals: &[u32], classes: &[u32]) -> ManyToOneIdMap {
    let mut map = vec![u32::MAX; size];
    let count = classes.iter().copied().max().map_or(0, |c| c as usize + 1);
    let mut members = vec![Vec::new(); count];
    for (&original, &class) in originals.iter().zip(classes) {
        map[original as usize] = class;
        members[class as usize].push(original);
    }
    for group in &mut members {
        group.sort_unstable();
    }
    let reps = members.iter().map(|g| g[0]).collect();
    ManyToOneIdMap {
        original_to_internal: map,
        internal_to_originals: members,
        representative_original_ids: reps,
    }
}

/// Verify that every candidate merge is contained in a reference class.
/// Finer quotients are permitted, e.g. GLRMask's separately retained reset root.
/// This checks map consistency as well as semantic refinement, but does not
/// require the candidate to cover every reference ID. Group-only candidate
/// maps are supported; the reference must have a forward coordinate.
pub fn verify_refinement(
    candidate: &ManyToOneIdMap,
    reference: &ManyToOneIdMap,
    axis: &'static str,
) -> Result<(), AnalysisError> {
    validate_quotient_map(reference, axis)?;
    for members in &candidate.internal_to_originals {
        if let Some((&first, rest)) = members.split_first() {
            let expected = mapped_class(reference, first);
            if expected.is_none() {
                return Err(AnalysisError::UnsoundMerge {
                    axis,
                    left: first,
                    right: first,
                });
            }
            for &other in rest {
                if expected.is_none() || mapped_class(reference, other) != expected {
                    return Err(AnalysisError::UnsoundMerge {
                        axis,
                        left: first,
                        right: other,
                    });
                }
            }
        }
    }
    validate_quotient_map(candidate, axis)
}

fn validate_quotient_map(map: &ManyToOneIdMap, axis: &'static str) -> Result<(), AnalysisError> {
    let invalid = |reason: &str| {
        AnalysisError::InvalidInput(format!("inconsistent {axis} quotient: {reason}"))
    };
    if map.internal_to_originals.len() != map.representative_original_ids.len() {
        return Err(invalid("representative and class counts differ"));
    }
    let mut seen = BTreeMap::<u32, u32>::new();
    for (class, members) in map.internal_to_originals.iter().enumerate() {
        if members.is_empty() || !members.contains(&map.representative_original_ids[class]) {
            return Err(invalid(
                "class is empty or its representative is not a member",
            ));
        }
        for &id in members {
            if seen.insert(id, class as u32).is_some() {
                return Err(invalid("an original ID occurs more than once"));
            }
            if !map.original_to_internal.is_empty()
                && map.original_to_internal.get(id as usize).copied() != Some(class as u32)
            {
                return Err(invalid(
                    "forward coordinate disagrees with class membership",
                ));
            }
        }
    }
    for (id, &class) in map.original_to_internal.iter().enumerate() {
        if class != u32::MAX && seen.get(&(id as u32)).copied() != Some(class) {
            return Err(invalid("forward coordinate has no matching class member"));
        }
    }
    Ok(())
}

/// Common refinement of local observations. An absent coordinate is distinct
/// from a dead observation; class numbers from different analyses never alias.
pub fn refine_token_partitions(
    token_ids: &[u32],
    analyses: &[Analysis],
) -> Result<ManyToOneIdMap, AnalysisError> {
    let mut ids = token_ids.to_vec();
    ids.sort_unstable();
    ids.dedup();
    let size = ids.iter().copied().max().map_or(0, |x| x as usize + 1);
    check_limit(
        "refined token map entries",
        size as u64,
        Budget::default().max_map_entries as u64,
    )?;
    let mut keys = BTreeMap::<Vec<Option<u32>>, u32>::new();
    let mut classes = Vec::with_capacity(ids.len());
    for &token in &ids {
        let key = analyses
            .iter()
            .map(|a| a.token_class(token))
            .collect::<Vec<_>>();
        let next = keys.len() as u32;
        classes.push(*keys.entry(key).or_insert(next));
    }
    Ok(map_from_classes(size, &ids, &classes))
}
