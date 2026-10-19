//! Grammar-aware pipeline benchmark with immutable original ID-to-byte inputs.
use lexquot::Vocab;
use lexquot::grammar::{Dfa, Grammar, Options, Symbol};
use serde::Deserialize;
use serde_json::json;
use std::{collections::BTreeMap, error::Error, fs, time::Instant};
#[derive(Deserialize)]
struct RawTrace {
    dfas: Vec<Dfa>,
}
#[derive(Deserialize)]
struct RawGrammar {
    labels: Vec<String>,
    rules: BTreeMap<String, Vec<Vec<String>>>,
}
fn main() -> Result<(), Box<dyn Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() < 4 || args.len() > 5 {
        return Err("usage: grammar_aware_bench trace.json lexical-cfg.json vocabulary.json output.json [full|scope|uniform|fold|fold-scope]".into());
    }
    let raw: RawTrace = serde_json::from_slice(&fs::read(&args[0])?)?;
    let src: RawGrammar = serde_json::from_slice(&fs::read(&args[1])?)?;
    if raw.dfas.len() != src.labels.len() {
        return Err("terminal order/domain mismatch".into());
    }
    let ids = src
        .rules
        .keys()
        .enumerate()
        .map(|(i, k)| (k.clone(), i as u32))
        .collect::<BTreeMap<_, _>>();
    let labels = src
        .labels
        .iter()
        .enumerate()
        .map(|(i, k)| (k.clone(), i as u32))
        .collect::<BTreeMap<_, _>>();
    let mut rules = vec![vec![]; ids.len()];
    for (lhs, ps) in src.rules {
        for p in ps {
            let mut rhs = Vec::new();
            for s in p {
                if s == "ε" {
                    continue;
                }
                rhs.push(if let Some(&t) = labels.get(&s) {
                    Symbol::Terminal(t)
                } else {
                    Symbol::Nonterminal(*ids.get(&s).ok_or("unknown grammar symbol")?)
                });
            }
            rules[ids[&lhs] as usize].push(rhs);
        }
    }
    let grammar = Grammar {
        start: *ids.get("S").ok_or("missing normalized start")?,
        terminals: raw.dfas,
        rules,
    };
    let raw_vocab: BTreeMap<u32, String> = serde_json::from_slice(&fs::read(&args[2])?)?;
    let entries = raw_vocab
        .into_iter()
        .map(|(id, h)| -> Result<_, Box<dyn Error>> {
            if h.len() % 2 != 0 || !h.is_ascii() {
                return Err("invalid vocabulary hex spelling".into());
            }
            let bytes = (0..h.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&h[i..i + 2], 16))
                .collect::<Result<Vec<_>, _>>()?;
            Ok((id, bytes))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let vocab = Vocab::new(entries);
    let variant = args.get(4).map(String::as_str).unwrap_or("full");
    let mut opts = Options::default();
    match variant {
        "full" => {}
        "scope" => {
            opts.fold_regular = false;
            opts.regular_actions = false;
        }
        "uniform" => {
            opts.fold_regular = false;
            opts.regular_actions = false;
            opts.follow_scopes = false;
        }
        "fold" => {
            opts.regular_actions = false;
            opts.follow_scopes = false;
        }
        "fold-scope" => opts.regular_actions = false,
        _ => return Err("unknown pipeline variant".into()),
    }
    let started = Instant::now();
    let prepared = grammar.prepare(opts)?;
    let result = prepared.analyze(&vocab)?;
    let whole = started.elapsed().as_secs_f64() * 1000.;
    let info = json!({"status":"ok","variant":variant,"algorithm":result.algorithm,"construction_ms":whole,"preparation_ms":result.preparation.total_ms,"analysis_ms":result.stats.analysis_ms,"nondead_classes":result.partition.nondead_class_count(),"including_dead_classes":result.partition.classes.len(),"dead_tokens":result.partition.dead_class.map(|c|result.partition.classes[c as usize].len()).unwrap_or(0),"token_count":result.partition.token_ids.len(),"preparation":result.preparation,"stats":result.stats,"contract":result.contract});
    fs::write(&args[3], serde_json::to_vec(&result)?)?;
    fs::write(
        format!("{}.normalized.json", &args[3]),
        serde_json::to_vec(prepared.normalized_grammar())?,
    )?;
    if let Some(dfa) = prepared.regular_language() {
        fs::write(
            format!("{}.regular.json", &args[3]),
            serde_json::to_vec(dfa)?,
        )?;
    }
    println!("{}", serde_json::to_string(&info)?);
    Ok(())
}
