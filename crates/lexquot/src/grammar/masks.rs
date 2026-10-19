//! Exact mask-only token signatures on a reachable regular-language DFA.
//! B_u(q) = live(delta*(q,u)); B_bu(q) = B_u(delta(q,b)). Columns are
//! packed bits and hash-table equality compares the entire vector. The caller
//! MUST commit original token bytes; these classes are not substitution classes.
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
    guard("regular mask initial signature", width, budget.max_cells)?;
    guard("regular mask initial column", 1, budget.max_reverse_columns)?;
    let words = width.div_ceil(64);
    // Compute coaccessibility rather than assume that every nonzero input
    // state is live. This also covers empty and epsilon-only languages.
    guard(
        "regular mask coaccessibility cells",
        width.saturating_mul(alphabet),
        budget.max_cells,
    )?;
    if width.saturating_mul(alphabet) as u64 > budget.max_work {
        return Err(AnalysisError::BudgetExceeded {
            resource: "regular mask initial work",
            requested: width.saturating_mul(alphabet) as u64,
            limit: budget.max_work,
        });
    }
    let mut reverse = vec![Vec::new(); width];
    for s in 0..width {
        for &t in &dfa.delta[s * alphabet..(s + 1) * alphabet] {
            reverse[t as usize].push(s);
        }
    }
    let mut live = dfa.accepting.clone();
    let mut todo = live
        .iter()
        .enumerate()
        .filter_map(|(s, &a)| a.then_some(s))
        .collect::<Vec<_>>();
    while let Some(t) = todo.pop() {
        for &s in &reverse[t] {
            if !live[s] {
                live[s] = true;
                todo.push(s);
            }
        }
    }
    let mut bits = vec![0u64; words];
    for (s, &yes) in live.iter().enumerate() {
        if yes {
            bits[s / 64] |= 1 << (s % 64);
        }
    }
    let initial: Arc<[u64]> = bits.into();
    let mut states = vec![initial.clone()];
    let mut ids = FxHashMap::<Arc<[u64]>, u32>::default();
    ids.insert(initial, 0);
    let mut transitions = FxHashMap::<(u32, u16), u32>::default();
    let mut answers = Vec::with_capacity(vocab.len());
    let mut stats = AnalysisStats {
        observation_roots: width.saturating_sub(1),
        work: width.saturating_mul(alphabet) as u64,
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
                    resource: "regular mask token work",
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
                    resource: "regular mask token work",
                    requested: stats.work,
                    limit: budget.max_work,
                });
            }
            let child = &states[q as usize];
            let mut column = vec![0u64; words];
            for s in 0..width {
                let target = dfa.delta[s * alphabet + byte as usize] as usize;
                if child[target / 64] & (1 << (target % 64)) != 0 {
                    column[s / 64] |= 1 << (s % 64);
                }
            }
            let next = if let Some(&next) = ids.get(column.as_slice()) {
                next
            } else {
                guard(
                    "regular mask columns",
                    states.len() + 1,
                    budget.max_reverse_columns,
                )?;
                guard(
                    "regular mask signature cells",
                    (states.len() + 1).saturating_mul(words),
                    budget.max_cells,
                )?;
                let next = states.len() as u32;
                let column: Arc<[u64]> = column.into();
                states.push(column.clone());
                ids.insert(column, next);
                next
            };
            if cache {
                guard(
                    "regular mask transitions",
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
    stats.signature_cells = states.len().saturating_mul(words);
    stats.analysis_ms = started.elapsed().as_secs_f64() * 1000.;
    Ok((map, stats))
}
