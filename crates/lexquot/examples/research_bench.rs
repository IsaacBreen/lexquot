//! Reproducible lexical-analysis benchmark; no parser or model inference.
//!
//! Example:
//! cargo run --profile eqbench -p lexquot --example research_bench --
//!   --vocab /path/to/llama3_vocab.json --case json-lexical --backend l1-direct
use lexquot::{
    Analysis, AnalysisRequest, Backend, Budget, Expr, Lexer, Observation, PreparedResiduals,
    Tokenizer, Vocab, lexer_with_terminal_residuals, parse_regex, verify_refinement,
};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::error::Error;
use std::io::Write;
use std::time::Instant;

fn option(args: &BTreeMap<String, String>, key: &str, default: &str) -> String {
    args.get(key).cloned().unwrap_or_else(|| default.into())
}
fn mix(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58476d1ce4e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}
fn literal(text: &str) -> Expr {
    Expr::U8Seq(text.as_bytes().to_vec())
}
fn regex(text: &str) -> Expr {
    parse_regex(text, false)
}
fn fixture(name: &str) -> Result<Vec<Expr>, Box<dyn Error + Send + Sync>> {
    Ok(match name {
        "json-lexical" => {
            let mut e=vec![regex("[ \\t\\n\\r]+"),regex("-?(0|[1-9][0-9]*)(\\.[0-9]+)?([eE][+-]?[0-9]+)?"),
                regex(r#""([^"\\]|\\["\\/bfnrt]|\\u[0-9a-fA-F]{4})*""#)];
            e.extend(["{","}","[","]",":",",","true","false","null"].into_iter().map(literal));e
        }
        "identifier-keywords" => {
            let mut e=vec![regex("[A-Za-z_$][A-Za-z0-9_$]*"),regex("[0-9]+"),regex("[ \\t\\r\\n]+")];
            e.extend("async await break case catch class const continue debugger default delete do else export extends false finally for function if import in instanceof let new null of return static super switch this throw true try typeof var void while with yield public private protected interface implements package enum abstract boolean byte char double final float goto int long native short synchronized throws transient volatile select from where join group order having limit distinct insert update".split_whitespace().map(literal));e
        }
        "bounded-128" => vec![regex("[a-z]{1,128}"),literal(","),literal(";")],
        "many-fields" => (0..96).map(|i|literal(&format!("\"field_{i:03}\""))).collect(),
        "shared-residuals" => (0..48).map(|_|regex("[a-z]+" )).collect(),
        "unicode-literals" => ["東京","東京都","한국어","대한민국","café","caffè","naïve","München","Zürich","😀","🙂"].into_iter().map(literal).collect(),
        _ => return Err(format!("unknown fixture {name}; use json-lexical, identifier-keywords, bounded-128, many-fields, shared-residuals, unicode-literals, or --expr-json").into()),
    })
}
fn bucket(bytes: &[u8]) -> usize {
    if bytes.len() > 16 {
        0
    } else if bytes.iter().any(|&b| b >= 128) {
        1
    } else if bytes
        .iter()
        .all(|b| b.is_ascii_alphabetic() || b"_$".contains(b))
    {
        2
    } else if bytes
        .iter()
        .all(|b| b.is_ascii_digit() || b".+-eE".contains(b))
    {
        3
    } else {
        4
    }
}
fn execute(
    lexer: &Tokenizer,
    projected: &PreparedResiduals,
    vocab: &Vocab,
    backend: &str,
    scope: &str,
    budget: Budget,
) -> Result<(Analysis, Value), Box<dyn Error + Send + Sync>> {
    if backend.starts_with("l1-direct") {
        let mut request = projected
            .request(vocab)
            .budget(budget)
            .minimize(backend != "l1-direct-unminimized");
        if scope == "reset" {
            request = request.initial_states([lexer.initial_state_id()]);
        }
        let result = request.analyze()?;
        let s = result.residual_stats;
        return Ok((
            result.analysis,
            json!({"residual_source_states":s.source_states,"residual_minimized_states":s.minimized_states,
            "root_vectors":s.root_vectors,"reverse_states":s.reverse_states,"reverse_transitions":s.reverse_transitions,
            "predecessor_visits":s.predecessor_visits,"minimize_ms":s.minimize_ms,"reverse_ms":s.reverse_ms,"reconstruction_ms":s.reconstruction_ms}),
        ));
    }
    let (observation, algorithm) = match backend {
        "l1-projected" => (Observation::L1, Backend::Production),
        "l1-canonical" => (Observation::L1, Backend::Canonical),
        "l2p-production" => (Observation::L2P, Backend::Production),
        "l2p-canonical" => (Observation::L2P, Backend::Canonical),
        _ => return Err(format!("unknown backend {backend}").into()),
    };
    let mut request = AnalysisRequest::new(lexer, vocab, observation)
        .backend(algorithm)
        .budget(budget);
    if scope == "reset" {
        request = request.initial_states([lexer.initial_state_id()]);
    }
    let result = request.analyze()?;
    let s = &result.stats();
    let details = json!({"byte_steps":s.byte_steps,"canonical_nodes":s.canonical_nodes,"reset_suffix_scans":s.reset_suffix_scans,"table_cells":s.table_cells});
    Ok((result, details))
}
fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    let mut args = BTreeMap::new();
    let mut raw = std::env::args().skip(1);
    while let Some(key) = raw.next() {
        if !key.starts_with("--") {
            return Err(format!("expected --option, got {key}").into());
        }
        let value = raw
            .next()
            .ok_or_else(|| format!("missing value for {key}"))?;
        args.insert(key, value);
    }
    let name = option(&args, "--case", "json-lexical");
    let backend = option(&args, "--backend", "l1-direct");
    let scope = option(&args, "--scope", "all");
    if !["all", "reset"].contains(&scope.as_str()) {
        return Err("scope must be all or reset".into());
    }
    let partition = option(&args, "--partition", "none");
    if !["none", "shape"].contains(&partition.as_str()) {
        return Err("partition must be none or shape".into());
    }
    let threads = option(&args, "--threads", "1").parse::<usize>()?;
    let repetitions = option(&args, "--repetitions", "6").parse::<usize>()?;
    if threads == 0 || repetitions == 0 {
        return Err("threads and repetitions must be positive".into());
    }
    let group_width = option(&args, "--group-width", "1").parse::<usize>()?;
    if group_width == 0 {
        return Err("group-width must be positive".into());
    }
    let limit = option(&args, "--limit", "128000").parse::<usize>()?;
    let check = option(&args, "--verify", "false") == "true";
    let vocab_path = args
        .get("--vocab")
        .ok_or("--vocab PATH is required (JSON original-ID to hexadecimal bytes)")?;
    let start = Instant::now();
    let raw_vocab: BTreeMap<u32, String> = serde_json::from_slice(&std::fs::read(vocab_path)?)?;
    let source_count = raw_vocab.len();
    let mut entries = raw_vocab
        .into_iter()
        .filter(|(id, _)| *id < 128000)
        .map(|(id, hex)| {
            if hex.len() % 2 != 0 {
                return Err(format!("odd hex byte length for token {id}"));
            }
            let bytes = (0..hex.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).map_err(|e| e.to_string()))
                .collect::<Result<Vec<_>, _>>()?;
            Ok((id, bytes))
        })
        .collect::<Result<Vec<_>, String>>()?;
    if entries.len() > limit {
        entries.sort_unstable_by_key(|(id, _)| mix(u64::from(*id) ^ 7));
        entries.truncate(limit);
        entries.sort_unstable_by_key(|(id, _)| *id);
    }
    let vocab_size = entries.len();
    let mut shards: BTreeMap<usize, Vec<(u32, Vec<u8>)>> = BTreeMap::new();
    for (id, bytes) in entries {
        shards
            .entry(if partition == "shape" {
                bucket(&bytes)
            } else {
                0
            })
            .or_default()
            .push((id, bytes));
    }
    let vocabularies = shards
        .into_iter()
        .map(|(id, entries)| (id, Vocab::new(entries)))
        .collect::<Vec<_>>();
    let vocabulary_load_ms = start.elapsed().as_secs_f64() * 1000.0;
    let expressions: Vec<Expr> = if let Some(path) = args.get("--expr-json") {
        serde_json::from_slice(&std::fs::read(path)?)?
    } else {
        fixture(&name)?
    };
    let terminal_count = expressions.len();
    let groups = (0..terminal_count)
        .map(|i| (i / group_width) as u32)
        .collect::<Vec<_>>();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build()?;
    eprintln!("phase=lexer_setup_start case={name}");
    let setup = Instant::now();
    let lexer = pool.install(|| lexer_with_terminal_residuals(expressions, &groups))?;
    let _ = lexer.all_singleton_epsilon_closures();
    let projected = PreparedResiduals::from_lexer(&lexer)?;
    let lexer_setup_ms = setup.elapsed().as_secs_f64() * 1000.0;
    eprintln!(
        "phase=lexer_setup_complete ms={lexer_setup_ms:.3} states={}",
        lexer.num_states()
    );
    let budget = Budget {
        max_table_cells: 32_000_000,
        max_byte_steps: 500_000_000,
        max_canonical_nodes: 2_000_000,
        ..Budget::default()
    };
    let mut stdout = std::io::BufWriter::new(std::io::stdout().lock());
    for repetition in 0..repetitions {
        eprintln!("phase=analysis_start repetition={repetition}");
        let started = Instant::now();
        let results = pool.install(|| {
            vocabularies
                .iter()
                .map(|(id, vocab)| {
                    execute(&lexer, &projected, vocab, &backend, &scope, budget)
                        .map(|(a, m)| (*id, a, m))
                })
                .collect::<Result<Vec<_>, _>>()
        });
        let elapsed_ms = started.elapsed().as_secs_f64() * 1000.0;
        eprintln!("phase=analysis_complete repetition={repetition} ms={elapsed_ms:.3}");
        let results = match results {
            Ok(results) => results,
            Err(error) => {
                writeln!(
                    stdout,
                    "{}",
                    json!({"status":"error","case":name,"backend":backend,"scope":scope,"partition":partition,"tokens":vocab_size,"raw_states":lexer.num_states(),"error":error.to_string(),"elapsed_ms":elapsed_ms})
                )?;
                stdout.flush()?;
                return Err(error);
            }
        };
        let mut verification = Value::Null;
        if check && repetition == 0 {
            eprintln!("phase=verification_start");
            let began = Instant::now();
            for ((_, vocabulary), (_, candidate, _)) in vocabularies.iter().zip(&results) {
                let observation = if backend.starts_with("l1") {
                    Observation::L1
                } else {
                    Observation::L2P
                };
                let mut request = AnalysisRequest::new(&lexer, vocabulary, observation)
                    .backend(Backend::Canonical)
                    .budget(budget);
                if scope == "reset" {
                    request = request.initial_states([lexer.initial_state_id()]);
                }
                let reference = request.analyze()?;
                verify_refinement(
                    &candidate.maps().vocab_tokens,
                    &reference.maps().vocab_tokens,
                    "token",
                )?;
                verify_refinement(
                    &candidate.maps().tokenizer_states,
                    &reference.maps().tokenizer_states,
                    "initial state",
                )?;
            }
            verification = json!({"status":"all_candidate_merges_checked","elapsed_ms":began.elapsed().as_secs_f64()*1000.0});
        }
        let token_classes = results
            .iter()
            .map(|(_, a, _)| a.token_class_count())
            .sum::<usize>();
        let state_classes_sum = results
            .iter()
            .map(|(_, a, _)| a.state_class_count())
            .sum::<usize>();
        let quotient_cells = results
            .iter()
            .map(|(_, a, _)| a.token_class_count() * a.state_class_count())
            .sum::<usize>();
        let shard_details=results.iter().map(|(id,a,metrics)|json!({"id":id,"tokens":a.domain().token_ids.len(),"initial_states":a.domain().initial_states.len(),"token_classes":a.token_class_count(),"state_classes":a.state_class_count(),"assurance":format!("{:?}",a.assurance()),"metrics":metrics})).collect::<Vec<_>>();
        writeln!(
            stdout,
            "{}",
            json!({"status":"ok","case":name,"backend":backend,"scope":scope,"partition":partition,"threads":threads,"repetition":repetition,"cache":"same-vocabulary; first invocation marked separately","first_invocation":repetition==0,"source_vocab_entries":source_count,"tokens":vocab_size,"excluded_control_ids":"IDs >= 128000","selection_seed":7,"raw_states":lexer.num_states(),"terminals":terminal_count,"group_width":group_width,"vocabulary_load_ms":vocabulary_load_ms,"lexer_setup_ms":lexer_setup_ms,"elapsed_ms":elapsed_ms,"token_classes":token_classes,"state_classes_sum":state_classes_sum,"quotient_cells":quotient_cells,"shards":shard_details,"verification":verification})
        )?;
        stdout.flush()?;
        if repetition + 1 == repetitions {
            if let Some(path) = args.get("--maps-out") {
                let maps=results.iter().map(|(id,a,_)|json!({"shard":id,"tokens":a.maps().vocab_tokens.internal_to_originals,"states":a.maps().tokenizer_states.internal_to_originals})).collect::<Vec<_>>();
                std::fs::write(path, serde_json::to_vec(&maps)?)?;
            }
        }
        std::hint::black_box(results);
    }
    Ok(())
}
