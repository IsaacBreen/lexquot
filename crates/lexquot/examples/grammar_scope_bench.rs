use lexquot::Vocab;
use lexquot::trace::grammar::{GrammarSpec, PreparedGrammarTrace, Production, Symbol};
use lexquot::trace::{PrepareOptions, TraceBudget, TraceDfa};
use serde::Deserialize;
use serde_json::json;
use std::{collections::BTreeMap, error::Error, fs, time::Instant};
#[derive(Deserialize)]
struct RawDfa {
    start: u32,
    accepting: Vec<bool>,
    transitions: Vec<Vec<(u8, u32)>>,
}
#[derive(Deserialize)]
struct RawTrace {
    dfas: Vec<RawDfa>,
}
#[derive(Deserialize)]
struct RawGrammar {
    labels: Vec<String>,
    rules: BTreeMap<String, Vec<Vec<String>>>,
}
fn main() -> Result<(), Box<dyn Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 4 {
        return Err(
            "usage: grammar_bench trace.json lexical-cfg.json vocab-id-hex.json output.json".into(),
        );
    }
    let raw: RawTrace = serde_json::from_slice(&fs::read(&args[0])?)?;
    let grammar: RawGrammar = serde_json::from_slice(&fs::read(&args[1])?)?;
    if raw.dfas.len() != grammar.labels.len() {
        return Err("terminal order/domain mismatch".into());
    }
    let ids = grammar
        .rules
        .keys()
        .enumerate()
        .map(|(i, k)| (k.clone(), i as u32))
        .collect::<BTreeMap<_, _>>();
    let labels = grammar
        .labels
        .iter()
        .enumerate()
        .map(|(i, k)| (k.clone(), i as u32))
        .collect::<BTreeMap<_, _>>();
    let mut productions = Vec::new();
    for (lhs, rules) in grammar.rules {
        for rule in rules {
            let mut rhs = Vec::new();
            for symbol in rule {
                if symbol == "ε" {
                    continue;
                }
                rhs.push(if let Some(t) = labels.get(&symbol) {
                    Symbol::Terminal(*t)
                } else {
                    Symbol::Nonterminal(*ids.get(&symbol).ok_or("unknown symbol")?)
                });
            }
            productions.push(Production {
                lhs: ids[&lhs],
                rhs,
            });
        }
    }
    let g = GrammarSpec {
        start: *ids.get("S").ok_or("missing start")?,
        nonterminals: ids.len(),
        productions,
    };
    let vocab: BTreeMap<u32, String> = serde_json::from_slice(&fs::read(&args[2])?)?;
    let tokens = vocab
        .into_iter()
        .map(|(id, h)| {
            if h.len() % 2 != 0 {
                return Err("bad hex".into());
            }
            let bytes = (0..h.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&h[i..i + 2], 16))
                .collect::<Result<Vec<_>, _>>()?;
            Ok((id, bytes))
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
    let v = Vocab::new(tokens);
    let start = Instant::now();
    let dfas = raw
        .dfas
        .into_iter()
        .map(|d| TraceDfa::new(d.start, d.accepting, d.transitions))
        .collect::<Result<Vec<_>, _>>()?;
    let p = PreparedGrammarTrace::new(&dfas, &g, PrepareOptions::default())?;
    let r = p.analyze(&v, TraceBudget::default())?;
    let elapsed = start.elapsed().as_secs_f64() * 1000.;
    let row = json!({"status":"ok","construction_ms":elapsed,"preparation":r.grammar,"analysis_ms":r.partition.stats.total_ms,"nondead_classes":r.partition.nondead_class_count(),"including_dead_classes":r.partition.classes.len(),"dead_tokens":r.partition.dead_class.map(|c|r.partition.classes[c as usize].len()).unwrap_or(0),"contract":r.contract});
    fs::write(&args[3], serde_json::to_vec(&r)?)?;
    println!("{}", serde_json::to_string(&row)?);
    Ok(())
}
