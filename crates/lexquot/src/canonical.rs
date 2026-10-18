//! Collision-free finite-observation reference algorithm.
//!
//! Hash tables compare complete structural keys. No digest is used as evidence
//! of equality. L2P suffix graphs are constructed iteratively, so token length
//! does not become native call-stack depth.
use crate::api::{
    AnalysisError, AnalysisRequest, AnalysisStats, Domain, Observation, check_limit,
    map_from_classes,
};
use crate::{InternalIdMap, Lexer};
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Key {
    End,
    L1(Vec<u32>),
    L2P {
        pending: Vec<u32>,
        completed: Vec<(u32, u32)>,
    },
}
#[derive(Clone)]
struct Scan {
    pending: Vec<u32>,
    matches: Vec<(u32, usize)>,
}

struct Engine<'a, 'b> {
    request: &'a AnalysisRequest<'b>,
    terminals: BTreeSet<u32>,
    nodes: HashMap<Key, u32>,
    suffixes: HashMap<(Vec<u8>, u32), u32>,
    stats: AnalysisStats,
}
impl<'a, 'b> Engine<'a, 'b> {
    fn intern(&mut self, key: Key) -> Result<u32, AnalysisError> {
        if let Some(&id) = self.nodes.get(&key) {
            return Ok(id);
        }
        check_limit(
            "canonical nodes",
            self.nodes.len() as u64 + 1,
            self.request.budget.max_canonical_nodes as u64,
        )?;
        let id = self.nodes.len() as u32;
        self.nodes.insert(key, id);
        Ok(id)
    }
    fn step(&mut self, config: &[u32], byte: u8) -> Result<Vec<u32>, AnalysisError> {
        self.stats.byte_steps = self.stats.byte_steps.saturating_add(config.len() as u64);
        check_limit(
            "byte steps",
            self.stats.byte_steps,
            self.request.budget.max_byte_steps,
        )?;
        Ok(self.request.lexer.step_all(config, byte).to_vec())
    }
    fn pending(&self, config: &[u32]) -> Vec<u32> {
        config
            .iter()
            .flat_map(|&s| self.request.lexer.possible_future_terminals_iter(s))
            .filter(|t| self.terminals.contains(t))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
    fn scan(&mut self, start: u32, bytes: &[u8]) -> Result<Scan, AnalysisError> {
        let closures = self.request.lexer.all_singleton_epsilon_closures();
        let mut config = closures[start as usize].to_vec();
        let mut pending = self.pending(&config);
        let mut matches = BTreeMap::<u32, usize>::new();
        let mut consumed = 0usize;
        for (index, &byte) in bytes.iter().enumerate() {
            if pending.is_empty() {
                break;
            }
            config = self.step(&config, byte)?;
            consumed = index + 1;
            for &state in &config {
                for t in self.request.lexer.matched_terminals_iter(state) {
                    if self.terminals.contains(&t) {
                        matches.insert(t, index + 1);
                    }
                }
            }
            pending = self.pending(&config);
        }
        if consumed != bytes.len() {
            pending.clear();
        }
        Ok(Scan {
            pending,
            matches: matches.into_iter().collect(),
        })
    }
    fn l1(&mut self, start: u32, bytes: &[u8]) -> Result<u32, AnalysisError> {
        let closures = self.request.lexer.all_singleton_epsilon_closures();
        let mut config = closures[start as usize].to_vec();
        for &byte in bytes {
            if config.is_empty() {
                break;
            }
            config = self.step(&config, byte)?;
        }
        let live = config
            .iter()
            .flat_map(|&s| {
                self.request
                    .lexer
                    .matched_terminals_iter(s)
                    .chain(self.request.lexer.possible_future_terminals_iter(s))
                    .collect::<Vec<_>>()
            })
            .filter(|t| self.terminals.contains(t))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        self.intern(Key::L1(live))
    }
    fn key(
        &self,
        scan: &Scan,
        offset: usize,
        len: usize,
        previous: Option<u32>,
        tails: &BTreeMap<(usize, u32), u32>,
    ) -> Key {
        let allowed = |t: u32| previous.is_none_or(|p| !self.request.follows.contains(&(p, t)));
        let pending = scan
            .pending
            .iter()
            .copied()
            .filter(|&t| allowed(t))
            .collect();
        let completed = scan
            .matches
            .iter()
            .filter(|&&(t, _)| allowed(t))
            .map(|&(t, p)| {
                let endpoint = offset + p;
                (
                    t,
                    if endpoint == len {
                        0
                    } else {
                        tails[&(endpoint, t)]
                    },
                )
            })
            .collect();
        Key::L2P { pending, completed }
    }
    fn l2p(&mut self, starts: &[u32], bytes: &[u8]) -> Result<Vec<u32>, AnalysisError> {
        let mut roots = Vec::with_capacity(starts.len());
        let mut queue = BTreeSet::<usize>::new();
        let mut incoming = BTreeMap::<usize, BTreeSet<u32>>::new();
        for &start in starts {
            let scan = self.scan(start, bytes)?;
            for &(t, p) in &scan.matches {
                if p < bytes.len() {
                    queue.insert(p);
                    incoming.entry(p).or_default().insert(t);
                }
            }
            roots.push(scan);
        }
        let mut suffix_scans = BTreeMap::<usize, Scan>::new();
        let mut tails = BTreeMap::<(usize, u32), u32>::new();
        while let Some(position) = queue.pop_first() {
            let predecessors = incoming[&position].iter().copied().collect::<Vec<_>>();
            let all_cached = predecessors
                .iter()
                .all(|&t| self.suffixes.contains_key(&(bytes[position..].to_vec(), t)));
            if all_cached {
                for t in predecessors {
                    tails.insert(
                        (position, t),
                        self.suffixes[&(bytes[position..].to_vec(), t)],
                    );
                }
                continue;
            }
            let scan = self.scan(self.request.lexer.initial_state_id(), &bytes[position..])?;
            self.stats.reset_suffix_scans += 1;
            for &(t, p) in &scan.matches {
                let endpoint = position + p;
                if endpoint < bytes.len() {
                    queue.insert(endpoint);
                    incoming.entry(endpoint).or_default().insert(t);
                }
            }
            suffix_scans.insert(position, scan);
        }
        for (&position, scan) in suffix_scans.iter().rev() {
            for &previous in &incoming[&position] {
                let cache_key = (bytes[position..].to_vec(), previous);
                let id = if let Some(&id) = self.suffixes.get(&cache_key) {
                    id
                } else {
                    let key = self.key(scan, position, bytes.len(), Some(previous), &tails);
                    let id = self.intern(key)?;
                    self.suffixes.insert(cache_key, id);
                    id
                };
                tails.insert((position, previous), id);
            }
        }
        roots
            .iter()
            .map(|scan| self.intern(self.key(scan, 0, bytes.len(), None, &tails)))
            .collect()
    }
}

pub(crate) fn analyze(
    request: &AnalysisRequest<'_>,
    domain: &Domain,
) -> Result<(InternalIdMap, AnalysisStats), AnalysisError> {
    // Equal byte strings share work, but retain every original model-token ID.
    let mut aliases = BTreeMap::<Vec<u8>, Vec<u32>>::new();
    for (&id, bytes) in request.vocab.entries_map() {
        aliases.entry(bytes.clone()).or_default().push(id);
    }
    let cells = domain
        .initial_states
        .len()
        .checked_mul(aliases.len())
        .ok_or(AnalysisError::BudgetExceeded {
            resource: "observation table",
            requested: u64::MAX,
            limit: request.budget.max_table_cells as u64,
        })?;
    let mut engine = Engine {
        request,
        terminals: domain.terminal_ids.iter().copied().collect(),
        nodes: HashMap::from([(Key::End, 0)]),
        suffixes: HashMap::new(),
        stats: AnalysisStats {
            table_cells: cells,
            ..Default::default()
        },
    };
    // Row equivalence is the common refinement of distinct observation
    // columns. Refine online instead of retaining a dense Q-by-V matrix.
    // A repeated column adds no information and need not refine again.
    let mut state_classes = vec![0u32; domain.initial_states.len()];
    let mut columns = HashMap::<Vec<u32>, u32>::new();
    let mut token_classes = BTreeMap::<u32, u32>::new();
    for (bytes, ids) in aliases {
        let signatures = if request.observation == Observation::L1 {
            domain
                .initial_states
                .iter()
                .map(|&q| engine.l1(q, &bytes))
                .collect::<Result<Vec<_>, _>>()?
        } else {
            engine.l2p(&domain.initial_states, &bytes)?
        };
        let class = if let Some(&class) = columns.get(&signatures) {
            class
        } else {
            let materialized = domain
                .initial_states
                .len()
                .saturating_mul(columns.len().saturating_add(3));
            check_limit(
                "canonical signature cells",
                materialized as u64,
                request.budget.max_table_cells as u64,
            )?;
            let mut refinement = HashMap::<(u32, u32), u32>::new();
            for (old, &observation) in state_classes.iter_mut().zip(&signatures) {
                let next = refinement.len() as u32;
                *old = *refinement.entry((*old, observation)).or_insert(next);
            }
            let class = columns.len() as u32;
            columns.insert(signatures, class);
            class
        };
        for id in ids {
            token_classes.insert(id, class);
        }
    }
    let token_ids = token_classes.keys().copied().collect::<Vec<_>>();
    let classes = token_classes.values().copied().collect::<Vec<_>>();
    let token_size = token_ids.last().map_or(0, |&id| id as usize + 1);
    engine.stats.canonical_nodes = engine.nodes.len();
    Ok((
        InternalIdMap {
            tokenizer_states: map_from_classes(
                request.lexer.num_states() as usize,
                &domain.initial_states,
                &state_classes,
            ),
            vocab_tokens: map_from_classes(token_size, &token_ids, &classes),
            deferred_vocab_singleton_original_ids: None,
        },
        engine.stats,
    ))
}
