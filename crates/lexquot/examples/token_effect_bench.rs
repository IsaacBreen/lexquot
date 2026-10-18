//! Reproducible token-effect experiment entry point. No model is loaded.
//!
//! Input JSON: {"terminals":["[a-z]+","[0-9]+"],
//!              "tokens":[[0,[97]],[1,[98,99]]],"options":{...},"repeats":6}
//! `automata` may replace regex `terminals`, and `vocab_path` may replace tokens.
//! External vocab JSON is an array of [original_u32_id, byte_array] pairs.
//! Prints one JSON line per completed repetition, then a final class-map line;
//! a process deadline therefore does not erase previously completed samples.
use lexquot::token_effect::{
    EffectOptions, PreparedTokenEffects, SymbolicByteRun, TerminalAutomaton,
};
use serde::Deserialize;
use std::error::Error;
use std::fs;
use std::io::{self, Write};
use std::time::Instant;

#[derive(Deserialize)]
struct Input {
    #[serde(default)]
    terminals: Vec<String>,
    #[serde(default)]
    automata: Vec<TerminalAutomaton>,
    #[serde(default)]
    expressions_path: Option<String>,
    #[serde(default)]
    symbolic_byte_run: Option<SymbolicByteRun>,
    #[serde(default)]
    tokens: Vec<(u32, Vec<u8>)>,
    #[serde(default)]
    vocab_path: Option<String>,
    #[serde(default)]
    options: EffectOptions,
    #[serde(default = "six")]
    repeats: usize,
    #[serde(default)]
    name: String,
}
fn six() -> usize {
    6
}
fn emit(value: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    println!("{value}");
    io::stdout().flush()?;
    Ok(())
}
fn main() -> Result<(), Box<dyn Error>> {
    let input_path = std::env::args()
        .nth(1)
        .ok_or("usage: token_effect_bench input.json")?;
    let input: Input = serde_json::from_slice(&fs::read(input_path)?)?;
    if input.repeats == 0 {
        return Err("repeats must be positive".into());
    }
    let loaded = Instant::now();
    let tokens: Vec<(u32, Vec<u8>)> = match input.vocab_path {
        Some(path) => serde_json::from_slice(&fs::read(path)?)?,
        None => input.tokens,
    };
    let load_ms = loaded.elapsed().as_secs_f64() * 1000.0;
    let frontend = Instant::now();
    if let Some(run) = input.symbolic_byte_run {
        emit(
            &serde_json::json!({"event":"frontend","name":input.name,"vocab_load_ms":load_ms,"frontend_ms":0.0,"vocabulary":tokens.len(),"terminal_count":1,"symbolic_byte_run":run}),
        )?;
        for repetition in 0..input.repeats {
            let start = Instant::now();
            let analysis = run.analyze(&tokens)?;
            emit(
                &serde_json::json!({"event":"sample","name":input.name,"repetition":repetition,"prepare_plus_analysis_ms":start.elapsed().as_secs_f64()*1000.0,"stats":analysis.stats}),
            )?;
            if repetition + 1 == input.repeats {
                emit(
                    &serde_json::json!({"event":"classes","name":input.name,"token_ids":analysis.token_ids,"classes":analysis.classes,"representatives":analysis.representatives}),
                )?;
            }
        }
        return Ok(());
    }
    let terminals = if let Some(path) = input.expressions_path {
        let expressions: Vec<lexquot::Expr> = serde_json::from_slice(&fs::read(path)?)?;
        expressions
            .iter()
            .map(TerminalAutomaton::from_expr)
            .collect::<Result<Vec<_>, _>>()?
    } else if input.automata.is_empty() {
        input
            .terminals
            .iter()
            .map(|r| TerminalAutomaton::from_expr(&lexquot::parse_regex(r, false)))
            .collect::<Result<Vec<_>, _>>()?
    } else {
        input.automata
    };
    let frontend_ms = frontend.elapsed().as_secs_f64() * 1000.0;
    emit(
        &serde_json::json!({"event":"frontend","name":input.name,"vocab_load_ms":load_ms,"frontend_ms":frontend_ms,"vocabulary":tokens.len(),"terminal_count":terminals.len(),"options":input.options}),
    )?;
    let mut previous = None;
    for repetition in 0..input.repeats {
        // Fresh preparation and all analysis caches for every repetition.
        let start = Instant::now();
        let prepared = PreparedTokenEffects::new(&terminals, input.options.clone())?;
        let analysis = prepared.analyze(&tokens)?;
        if let Some(old) = &previous {
            assert_eq!(
                old, &analysis.classes,
                "class IDs must be deterministic across fresh runs"
            );
        }
        emit(
            &serde_json::json!({"event":"sample","name":input.name,"repetition":repetition,"prepare_plus_analysis_ms":start.elapsed().as_secs_f64()*1000.0,"stats":analysis.stats}),
        )?;
        previous = Some(analysis.classes.clone());
        if repetition + 1 == input.repeats {
            emit(
                &serde_json::json!({"event":"classes","name":input.name,"token_ids":analysis.token_ids,"classes":analysis.classes,"representatives":analysis.representatives}),
            )?;
        }
    }
    Ok(())
}
