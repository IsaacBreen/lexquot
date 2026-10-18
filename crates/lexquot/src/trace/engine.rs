use super::automata::Product;
use super::language::{EMPTY, END, Languages, Node};
use super::{
    EndpointPolicy, TraceAlgorithm, TraceAnalysis, TraceBudget, TraceRequest, TraceStats, limit,
    work,
};
use crate::AnalysisError;
use rustc_hash::FxHashMap;
use std::hash::Hash;
use std::sync::Arc;
use std::time::Instant;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
struct First {
    pending: u32,
    tail: u32,
}

struct Columns<T> {
    values: Vec<Arc<[T]>>,
    ids: FxHashMap<Arc<[T]>, u32>,
    transitions: FxHashMap<(u32, u16), u32>,
    width: usize,
    budget: TraceBudget,
}

impl<T: Eq + Hash> Columns<T> {
    fn new(width: usize, budget: TraceBudget) -> Self {
        Self {
            values: Vec::new(),
            ids: FxHashMap::default(),
            transitions: FxHashMap::default(),
            width,
            budget,
        }
    }

    fn intern(&mut self, column: Vec<T>) -> Result<u32, AnalysisError> {
        debug_assert_eq!(column.len(), self.width);
        if let Some(&id) = self.ids.get(column.as_slice()) {
            return Ok(id);
        }
        limit(
            "trace reverse columns",
            self.values.len() + 1,
            self.budget.max_reverse_columns.min(u32::MAX as usize),
        )?;
        limit(
            "trace reverse signature cells",
            (self.values.len() + 1).saturating_mul(self.width),
            self.budget.max_cells,
        )?;
        let id = self.values.len() as u32;
        let column: Arc<[T]> = column.into();
        self.values.push(column.clone());
        self.ids.insert(column, id);
        Ok(id)
    }

    fn cache(&mut self, source: u32, byte: u16, target: u32) -> Result<(), AnalysisError> {
        limit(
            "trace cached prepend transitions",
            self.transitions.len() + 1,
            self.budget.max_cells,
        )?;
        self.transitions.insert((source, byte), target);
        Ok(())
    }
}

pub(super) fn analyze(request: TraceRequest<'_>) -> Result<TraceAnalysis, AnalysisError> {
    let started = Instant::now();
    let mut stats = TraceStats::default();
    let tokens = request
        .vocab
        .entries_map()
        .iter()
        .map(|(&id, bytes)| (id, bytes.as_slice()))
        .collect::<Vec<_>>();
    limit(
        "trace vocabulary entries",
        tokens.len(),
        request.budget.max_cells,
    )?;
    for &(_, bytes) in &tokens {
        if bytes.is_empty() {
            return Err(AnalysisError::InvalidInput(
                "empty byte tokens are outside the trace vocabulary domain".into(),
            ));
        }
        limit(
            "trace token bytes",
            bytes.len(),
            request.budget.max_token_bytes,
        )?;
        stats.vocabulary_bytes = stats
            .vocabulary_bytes
            .checked_add(bytes.len())
            .ok_or_else(|| AnalysisError::InvalidInput("vocabulary byte count overflow".into()))?;
    }
    stats.token_count = tokens.len();
    let mut languages = Languages::new(request.budget)?;
    let (columns, dead) = match request.algorithm {
        TraceAlgorithm::Projected => projected(&request, &tokens, &mut languages, &mut stats)?,
        TraceAlgorithm::Product => product(&request, &tokens, &mut languages, &mut stats)?,
    };
    stats.language_nodes = languages.len();
    stats.language_cells = languages.cells();
    stats.union_pairs = languages.union_count();
    work(
        &mut stats.work,
        languages.union_work,
        request.budget.max_work,
    )?;
    // Sparse original IDs never cause a max-ID-sized allocation. Ordinary token
    // IDs, including duplicate spellings, are reconstructed in original order.
    let mut class_ids = FxHashMap::<u32, u32>::default();
    let mut classes = Vec::<Vec<u32>>::new();
    let mut representatives = Vec::new();
    let mut representative_lengths = Vec::new();
    let mut token_classes = Vec::with_capacity(tokens.len());
    let mut dead_class = None;
    for ((&(id, bytes), &column), &is_dead) in tokens.iter().zip(&columns).zip(&dead) {
        let next = classes.len() as u32;
        let class = *class_ids.entry(column).or_insert_with(|| {
            classes.push(Vec::new());
            representatives.push(id);
            representative_lengths.push(bytes.len());
            next
        });
        let c = class as usize;
        classes[c].push(id);
        token_classes.push(class);
        if (bytes.len(), id) < (representative_lengths[c], representatives[c]) {
            representatives[c] = id;
            representative_lengths[c] = bytes.len();
        }
        if is_dead {
            if dead_class.is_some_and(|other| other != class) {
                return Err(AnalysisError::Kernel(
                    "multiple exact empty-observation classes".into(),
                ));
            }
            dead_class = Some(class);
        }
    }
    stats.total_ms = started.elapsed().as_secs_f64() * 1000.0;
    Ok(TraceAnalysis {
        endpoint_policy: request.endpoint,
        algorithm: request.algorithm,
        token_ids: tokens.iter().map(|&(id, _)| id).collect(),
        token_classes,
        classes,
        representatives,
        dead_class,
        stats,
    })
}

fn endpoint(request: &TraceRequest<'_>, s: usize) -> u32 {
    if !request.prepared.future[s] {
        0
    } else if request.endpoint == EndpointPolicy::Mask {
        1
    } else {
        request.prepared.endpoint_classes[s] + 1
    }
}

fn projected(
    request: &TraceRequest<'_>,
    tokens: &[(u32, &[u8])],
    languages: &mut Languages,
    stats: &mut TraceStats,
) -> Result<(Vec<u32>, Vec<bool>), AnalysisError> {
    let p = request.prepared;
    let width = p.state_count();
    let alphabet = p.class_bytes.len();
    stats.observation_roots = width - 1;
    let mut columns = Columns::<First>::new(width, request.budget);
    let base = (0..width)
        .map(|s| First {
            pending: endpoint(request, s),
            tail: if p.accepting[s] { END } else { EMPTY },
        })
        .collect();
    let initial = columns.intern(base)?;
    let mut answers = Vec::with_capacity(tokens.len());
    let mut dead = Vec::with_capacity(tokens.len());
    for &(_, bytes) in tokens {
        let mut source = initial;
        for &byte in bytes.iter().rev() {
            work(&mut stats.work, 1, request.budget.max_work)?;
            let b = p.byte_class[byte as usize];
            let cache_byte = if request.byte_classes { b } else { byte as u16 };
            if request.cache {
                if let Some(&target) = columns.transitions.get(&(source, cache_byte)) {
                    stats.transition_cache_hits += 1;
                    source = target;
                    continue;
                }
            }
            let child = columns.values[source as usize].clone();
            // All reset suffixes use the entire labelled terminal family.
            let mut reset = Node::empty();
            for &(terminal, target) in &p.root_destinations[b as usize] {
                let value = child[target as usize];
                if value.pending != 0 {
                    reset.pending.push((terminal, value.pending));
                }
                if value.tail != EMPTY {
                    reset.edges.push((terminal, value.tail));
                }
            }
            work(
                &mut stats.work,
                width + p.root_destinations[b as usize].len(),
                request.budget.max_work,
            )?;
            let reset = languages.intern(reset)?;
            let mut column = Vec::with_capacity(width);
            for s in 0..width {
                let target = p.table[s * alphabet + b as usize] as usize;
                let mut value = child[target];
                if p.accepting[s] {
                    value.tail = languages.union(value.tail, reset)?;
                }
                column.push(value);
            }
            let target = columns.intern(column)?;
            if request.cache {
                columns.cache(source, cache_byte, target)?;
            }
            stats.prepend_transitions += 1;
            source = target;
        }
        answers.push(source);
        dead.push(
            columns.values[source as usize]
                .iter()
                .all(|v| v.pending == 0 && v.tail == EMPTY),
        );
    }
    stats.reverse_columns = columns.values.len();
    stats.signature_cells = columns.values.len().saturating_mul(width);
    Ok((answers, dead))
}

fn product(
    request: &TraceRequest<'_>,
    tokens: &[(u32, &[u8])],
    languages: &mut Languages,
    stats: &mut TraceStats,
) -> Result<(Vec<u32>, Vec<bool>), AnalysisError> {
    let prepared = Instant::now();
    let p = request.prepared;
    let product = Product::build(p, request.budget)?;
    stats.product_ms = prepared.elapsed().as_secs_f64() * 1000.0;
    let width = product.rows.len();
    let alphabet = p.class_bytes.len();
    stats.product_states = width - 1;
    stats.observation_roots = width - 1;
    let mut columns = Columns::<u32>::new(width, request.budget);
    let mut base = Vec::with_capacity(width);
    for row in &product.rows {
        let mut node = Node::empty();
        for &(terminal, s) in row.iter() {
            let pending = endpoint(request, s as usize);
            if pending != 0 {
                node.pending.push((terminal, pending));
            }
            if p.accepting[s as usize] {
                node.edges.push((terminal, END));
            }
        }
        base.push(languages.intern(node)?);
    }
    let initial = columns.intern(base)?;
    let mut answers = Vec::with_capacity(tokens.len());
    let mut dead = Vec::with_capacity(tokens.len());
    for &(_, bytes) in tokens {
        let mut source = initial;
        for &byte in bytes.iter().rev() {
            work(&mut stats.work, 1, request.budget.max_work)?;
            let b = p.byte_class[byte as usize];
            let cache_byte = if request.byte_classes { b } else { byte as u16 };
            if request.cache {
                if let Some(&target) = columns.transitions.get(&(source, cache_byte)) {
                    stats.transition_cache_hits += 1;
                    source = target;
                    continue;
                }
            }
            let child = columns.values[source as usize].clone();
            // Product reset is state one; terminals are nonnullable, so this
            // one-byte transition includes every legal positive first match.
            let reset = child[product.table[alphabet + b as usize] as usize];
            let mut column = Vec::with_capacity(width);
            work(&mut stats.work, width, request.budget.max_work)?;
            for s in 0..width {
                let continuing = child[product.table[s * alphabet + b as usize] as usize];
                if reset == EMPTY || product.finals[s].is_empty() {
                    column.push(continuing);
                } else {
                    let completing = languages.intern(Node {
                        edges: product.finals[s].iter().map(|&t| (t, reset)).collect(),
                        ..Node::empty()
                    })?;
                    work(
                        &mut stats.work,
                        product.finals[s].len(),
                        request.budget.max_work,
                    )?;
                    column.push(languages.union(continuing, completing)?);
                }
            }
            let target = columns.intern(column)?;
            if request.cache {
                columns.cache(source, cache_byte, target)?;
            }
            stats.prepend_transitions += 1;
            source = target;
        }
        answers.push(source);
        dead.push(
            columns.values[source as usize]
                .iter()
                .all(|&id| id == EMPTY),
        );
    }
    stats.reverse_columns = columns.values.len();
    stats.signature_cells = columns.values.len().saturating_mul(width);
    Ok((answers, dead))
}
