//! Reproducible vocabulary-only trace benchmark. Every analysis invocation has
//! fresh trace/column caches; prepared terminal automata are reused explicitly.
//! Input DFAs use exactly the same byte languages as the matched CFG baseline.
use lexquot::trace::{
    EndpointPolicy, PrepareOptions, PreparedTrace, TraceAlgorithm, TraceBudget, TraceDfa,
};
use lexquot::{Expr, Vocab, parse_regex};
use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::error::Error;
use std::io::Write;
use std::time::Instant;

#[derive(Deserialize)]
struct DfaInput {
    start: u32,
    accepting: Vec<bool>,
    transitions: Vec<Vec<(u8, u32)>>,
}

#[derive(Deserialize)]
struct Case {
    name: String,
    #[serde(default)]
    dfas: Vec<DfaInput>,
    #[serde(default)]
    regexes: Vec<String>,
    #[serde(default)]
    expressions: Vec<Expr>,
    #[serde(default)]
    source: Value,
}

fn mix(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58476d1ce4e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}

fn decode(hex: &str) -> Result<Vec<u8>, String> {
    if hex.len() % 2 != 0 || !hex.is_ascii() {
        return Err("invalid hex byte spelling".into());
    }
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    let mut args = BTreeMap::new();
    let mut raw = std::env::args().skip(1);
    while let Some(key) = raw.next() {
        if !key.starts_with("--") {
            return Err(format!("expected option, got {key}").into());
        }
        let value = raw
            .next()
            .ok_or_else(|| format!("missing value for {key}"))?;
        if args.insert(key.clone(), value).is_some() {
            return Err(format!("duplicate option {key}").into());
        }
    }
    let opt = |key: &str, default: &str| args.get(key).cloned().unwrap_or_else(|| default.into());
    let input = args.get("--input").ok_or("--input case.json required")?;
    let vocab_path = args
        .get("--vocab")
        .ok_or("--vocab original-id-to-hex.json required")?;
    let mode = opt("--mode", "projected");
    let policy = opt("--policy", "residual");
    let algorithm = match mode.as_str() {
        "projected" => TraceAlgorithm::Projected,
        "product" => TraceAlgorithm::Product,
        _ => return Err("mode must be projected or product".into()),
    };
    let endpoint = match policy.as_str() {
        "residual" => EndpointPolicy::Residual,
        "mask" => EndpointPolicy::Mask,
        _ => return Err("policy must be residual or mask".into()),
    };
    let repeat: usize = opt("--repeat", "6").parse()?;
    let threads: usize = opt("--threads", "1").parse()?;
    let sample: usize = opt("--limit", "0").parse()?;
    let minimize = opt("--minimize", "true") == "true";
    let share = opt("--share", "true") == "true";
    let cache = opt("--cache", "true") == "true";
    let prepare_each = opt("--prepare-each", "true") == "true";
    let byte_classes = opt("--byte-classes", "true") == "true";
    if repeat == 0 || threads == 0 {
        return Err("repeat and threads must be positive".into());
    }
    if threads != 1 {
        return Err("trace kernels are single-threaded; parallel vocabulary shards require an explicit separate experiment".into());
    }
    let budget = TraceBudget {
        max_states: opt("--max-states", "100000").parse()?,
        max_cells: opt("--max-cells", "32000000").parse()?,
        max_reverse_columns: opt("--max-columns", "2000000").parse()?,
        max_language_nodes: opt("--max-nodes", "2000000").parse()?,
        max_union_pairs: opt("--max-unions", "4000000").parse()?,
        max_work: opt("--max-work", "1000000000").parse()?,
        ..TraceBudget::default()
    };
    let began = Instant::now();
    let raw_vocab: BTreeMap<u32, String> = serde_json::from_slice(&std::fs::read(vocab_path)?)?;
    let original_count = raw_vocab.len();
    let mut entries = raw_vocab
        .into_iter()
        .map(|(id, h)| decode(&h).map(|b| (id, b)))
        .collect::<Result<Vec<_>, _>>()?;
    if entries.iter().any(|(_, b)| b.is_empty()) {
        return Err(
            "empty tokens must be explicitly excluded by the recorded acquisition manifest".into(),
        );
    }
    if sample != 0 && entries.len() > sample {
        entries.sort_unstable_by_key(|(id, _)| mix(u64::from(*id) ^ 7));
        entries.truncate(sample);
        entries.sort_unstable_by_key(|(id, _)| *id);
    }
    let count = entries.len();
    let max_bytes = entries.iter().map(|(_, b)| b.len()).max().unwrap_or(0);
    let vocabulary = Vocab::new(entries);
    let vocabulary_io_ms = began.elapsed().as_secs_f64() * 1000.0;
    let case: Case = serde_json::from_slice(&std::fs::read(input)?)?;
    let pool = rayon::ThreadPoolBuilder::new().num_threads(1).build()?;
    let mut stdout = std::io::BufWriter::new(std::io::stdout().lock());
    eprintln!("phase=terminal_dfa_setup_start case={}", case.name);
    let setup = Instant::now();
    let terminals = pool.install(|| -> Result<Vec<TraceDfa>, lexquot::AnalysisError> {
        if !case.dfas.is_empty() {
            case.dfas
                .into_iter()
                .map(|d| TraceDfa::new(d.start, d.accepting, d.transitions))
                .collect()
        } else if !case.expressions.is_empty() {
            case.expressions
                .iter()
                .map(TraceDfa::from_expression)
                .collect()
        } else {
            case.regexes
                .iter()
                .map(|r| TraceDfa::from_expression(&parse_regex(r, false)))
                .collect()
        }
    });
    let terminal_dfa_ms = setup.elapsed().as_secs_f64() * 1000.0;
    let terminals = match terminals {
        Ok(value) => value,
        Err(error) => {
            writeln!(
                stdout,
                "{}",
                json!({"status":"error","phase":"terminal-dfa","case":case.name,"error":error.to_string(),"elapsed_ms":terminal_dfa_ms})
            )?;
            stdout.flush()?;
            return Err(error.into());
        }
    };
    eprintln!("phase=terminal_dfa_setup_complete ms={terminal_dfa_ms:.3}");
    let prep = pool.install(|| {
        PreparedTrace::new(
            &terminals,
            PrepareOptions {
                minimize,
                share_across_terminals: share,
                budget,
            },
        )
    });
    let prepared = match prep {
        Ok(value) => value,
        Err(error) => {
            writeln!(
                stdout,
                "{}",
                json!({"status":"error","phase":"preparation","case":case.name,"error":error.to_string()})
            )?;
            stdout.flush()?;
            return Err(error.into());
        }
    };
    eprintln!(
        "phase=preparation_complete states={} ms={:.3}",
        prepared.stats().projected_states,
        prepared.stats().preparation_ms
    );
    for repetition in 0..repeat {
        // A fresh-compilation trial includes real automaton preparation, rather
        // than adding one cached preparation time to unrelated warm samples.
        let fresh = if repetition > 0 && prepare_each {
            Some(pool.install(|| {
                PreparedTrace::new(
                    &terminals,
                    PrepareOptions {
                        minimize,
                        share_across_terminals: share,
                        budget,
                    },
                )
            })?)
        } else {
            None
        };
        let current = fresh.as_ref().unwrap_or(&prepared);
        eprintln!("phase=analysis_start repetition={repetition}");
        let started = Instant::now();
        let result = pool.install(|| {
            current
                .request(&vocabulary)
                .endpoint(endpoint)
                .algorithm(algorithm)
                .cache_transitions(cache)
                .byte_classes(byte_classes)
                .budget(budget)
                .analyze()
        });
        let analysis_ms = started.elapsed().as_secs_f64() * 1000.0;
        match result {
            Ok(result) => {
                eprintln!(
                    "phase=analysis_complete repetition={repetition} ms={analysis_ms:.3} classes={}",
                    result.nondead_class_count()
                );
                let mut class_sizes = result
                    .classes
                    .iter()
                    .enumerate()
                    .filter_map(|(id, members)| {
                        (Some(id as u32) != result.dead_class).then_some(members.len())
                    })
                    .collect::<Vec<_>>();
                class_sizes.sort_unstable();
                let record = json!({
                    "status":"ok", "case":case.name, "source":case.source, "algorithm":mode, "policy":policy,
                    "repetition":repetition,"first_invocation":repetition==0,
                    "cache_lifetime":if prepare_each { "fresh terminal preparation, trace and reverse caches per invocation" } else { "fresh trace and reverse caches per invocation; prepared DFA reused" },
                    "prepare_each":prepare_each,
                    "threads":threads,"minimize":minimize,"share":share,"cache":cache,"byte_classes":byte_classes,
                    "tokens":count,"source_vocab_entries":original_count,"max_token_bytes":max_bytes,"selection_seed":7,
                    "vocabulary_io_ms":vocabulary_io_ms,"terminal_dfa_ms":terminal_dfa_ms,
                    "preparation":current.stats(),"analysis_ms":analysis_ms,"construction_ms":current.stats().preparation_ms + analysis_ms,"stats":result.stats,
                    "classes_including_dead":result.classes.len(),"nondead_classes":result.nondead_class_count(),
                    "dead_tokens":result.dead_class.map_or(0,|c|result.classes[c as usize].len()),"class_sizes":class_sizes,
                    "budget":budget,"state_quotient_computed":false,
                });
                writeln!(stdout, "{record}")?;
                stdout.flush()?;
                if repetition == 0 {
                    if let Some(path) = args.get("--maps-out") {
                        std::fs::write(path, serde_json::to_vec(&result)?)?;
                    }
                }
                std::hint::black_box(result);
            }
            Err(error) => {
                writeln!(
                    stdout,
                    "{}",
                    json!({"status":"error","phase":"analysis","case":case.name,"algorithm":mode,"policy":policy,"repetition":repetition,"tokens":count,"error":error.to_string(),"elapsed_ms":analysis_ms,"preparation":current.stats()})
                )?;
                stdout.flush()?;
                return Err(error.into());
            }
        }
    }
    Ok(())
}
