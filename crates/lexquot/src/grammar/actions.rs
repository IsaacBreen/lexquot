//! Exact token transformations of a minimized DFA for a wholly regular CFG.
//! All DFA states are reachable from the root. Equality is precisely the
//! two-sided syntactic congruence of the fixed regular byte language.
use super::dfa::Dense;
use super::{AnalysisStats, TokenPartition, guard};
use crate::{AnalysisError, Vocab, trace::TraceBudget};
use rustc_hash::FxHashMap;
use std::sync::Arc;
use std::time::Instant;

pub(super) fn analyze(
    dfa: &Dense,
    vocab: &Vocab,
    budget: TraceBudget,
    cache: bool,
) -> Result<(TokenPartition, AnalysisStats), AnalysisError> {
    let started = Instant::now();
    let width = dfa.accepting.len();
    let alphabet = dfa.bytes.len();
    guard("regular grammar initial signature", width, budget.max_cells)?;
    guard(
        "regular grammar initial column",
        1,
        budget.max_reverse_columns,
    )?;
    let initial: Arc<[u32]> = (0..width as u32).collect::<Vec<_>>().into();
    let mut states = vec![initial.clone()];
    let mut ids = FxHashMap::<Arc<[u32]>, u32>::default();
    ids.insert(initial, 0);
    let mut transitions = FxHashMap::<(u32, u16), u32>::default();
    let mut answers = Vec::with_capacity(vocab.len());
    let mut stats = AnalysisStats {
        observation_roots: width.saturating_sub(1),
        ..Default::default()
    };
    for (&id, bytes) in vocab.entries_map() {
        if bytes.is_empty() {
            return Err(AnalysisError::InvalidInput(
                "empty/control token supplied as ordinary bytes".into(),
            ));
        }
        guard("grammar token bytes", bytes.len(), budget.max_token_bytes)?;
        let mut q = 0u32;
        for &b in bytes.iter().rev() {
            stats.work = stats.work.saturating_add(1);
            if stats.work > budget.max_work {
                return Err(AnalysisError::BudgetExceeded {
                    resource: "regular grammar token work",
                    requested: stats.work,
                    limit: budget.max_work,
                });
            }
            let byte = dfa.class[b as usize];
            if cache {
                if let Some(&next) = transitions.get(&(q, byte)) {
                    stats.cache_hits += 1;
                    q = next;
                    continue;
                }
            }
            stats.work = stats.work.saturating_add(width as u64);
            if stats.work > budget.max_work {
                return Err(AnalysisError::BudgetExceeded {
                    resource: "regular grammar token work",
                    requested: stats.work,
                    limit: budget.max_work,
                });
            }
            let child = &states[q as usize];
            let column: Vec<u32> = (0..width)
                .map(|s| child[dfa.delta[s * alphabet + byte as usize] as usize])
                .collect();
            let next = if let Some(&next) = ids.get(column.as_slice()) {
                next
            } else {
                guard(
                    "regular grammar columns",
                    states.len() + 1,
                    budget.max_reverse_columns,
                )?;
                guard(
                    "regular grammar signature cells",
                    (states.len() + 1).saturating_mul(width),
                    budget.max_cells,
                )?;
                let next = states.len() as u32;
                let column: Arc<[u32]> = column.into();
                states.push(column.clone());
                ids.insert(column, next);
                next
            };
            if cache {
                guard(
                    "regular grammar transitions",
                    transitions.len() + 1,
                    budget.max_cells,
                )?;
                transitions.insert((q, byte), next);
            }
            stats.prepend_transitions += 1;
            q = next;
        }
        answers.push((id, bytes.len(), q));
        stats.vocabulary_bytes = stats.vocabulary_bytes.saturating_add(bytes.len());
    }
    let mut map = TokenPartition::default();
    let mut groups = FxHashMap::<u32, u32>::default();
    let mut sizes = Vec::new();
    for (id, len, column) in answers {
        let next = map.classes.len() as u32;
        let c = *groups.entry(column).or_insert_with(|| {
            map.classes.push(vec![]);
            map.representatives.push(id);
            sizes.push(len);
            next
        });
        map.token_ids.push(id);
        map.token_classes.push(c);
        map.classes[c as usize].push(id);
        if (len, id) < (sizes[c as usize], map.representatives[c as usize]) {
            sizes[c as usize] = len;
            map.representatives[c as usize] = id;
        }
        if states[column as usize].iter().all(|&s| s == 0) {
            if map.dead_class.is_some_and(|x| x != c) {
                return Err(AnalysisError::Kernel(
                    "noncanonical dead regular token class".into(),
                ));
            }
            map.dead_class = Some(c);
        }
    }
    stats.reverse_columns = states.len();
    stats.signature_cells = states.len().saturating_mul(width);
    stats.analysis_ms = started.elapsed().as_secs_f64() * 1000.;
    Ok((map, stats))
}
