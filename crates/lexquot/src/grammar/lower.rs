//! Exact regular-island normalization, with a conservative fallback for every
//! nonlinear or budget-declined SCC. No parser table or GLRMask runtime is built.
use super::dfa::Nfa;
use super::{Budget, Dfa, Grammar, Options, PreparationStats, Symbol, guard, spend};
use crate::AnalysisError;
use std::collections::BTreeSet;
use std::sync::Arc;

type Rules = Vec<Vec<Vec<Symbol>>>;
#[derive(Clone, Debug)]
pub(super) struct Lowered {
    pub grammar: Grammar,
    pub root_regular: Option<Dfa>,
    pub stats: PreparationStats,
}

fn components(rules: &Rules, reachable: &[bool]) -> Vec<Vec<usize>> {
    let n = rules.len();
    let mut edges = vec![Vec::new(); n];
    let mut reverse = edges.clone();
    for (v, ps) in rules.iter().enumerate() {
        if reachable[v] {
            for p in ps {
                for s in p {
                    if let Symbol::Nonterminal(w) = s {
                        edges[v].push(*w as usize);
                        reverse[*w as usize].push(v);
                    }
                }
            }
        }
    }
    let mut seen = vec![false; n];
    let mut order = Vec::new();
    for root in 0..n {
        if !reachable[root] || seen[root] {
            continue;
        }
        seen[root] = true;
        let mut stack = vec![(root, 0)];
        while let Some((v, index)) = stack.last_mut() {
            if *index == edges[*v].len() {
                order.push(*v);
                stack.pop();
                continue;
            }
            let w = edges[*v][*index];
            *index += 1;
            if !seen[w] {
                seen[w] = true;
                stack.push((w, 0));
            }
        }
    }
    seen.fill(false);
    let mut output = Vec::new();
    for root in order.into_iter().rev() {
        if seen[root] {
            continue;
        }
        let mut c = Vec::new();
        let mut todo = vec![root];
        seen[root] = true;
        while let Some(v) = todo.pop() {
            c.push(v);
            for &w in &reverse[v] {
                if !seen[w] {
                    seen[w] = true;
                    todo.push(w);
                }
            }
        }
        c.sort_unstable();
        output.push(c);
    }
    output.reverse();
    output
}

pub(super) fn lower(input: &Grammar, options: &Options) -> Result<Lowered, AnalysisError> {
    let budget = &options.budget;
    let mut work = 0usize;
    guard(
        "grammar nonterminals",
        input.rules.len(),
        budget.max_nonterminals,
    )?;
    guard(
        "grammar terminals",
        input.terminals.len(),
        budget.max_input_states,
    )?;
    if input.rules.is_empty() || input.start as usize >= input.rules.len() {
        return Err(AnalysisError::InvalidInput(
            "invalid grammar start/nonterminal domain".into(),
        ));
    }
    let mut term = Vec::with_capacity(input.terminals.len());
    let mut source_states = 0usize;
    for original in &input.terminals {
        let mut d = original.clone();
        d.validate(budget)?;
        source_states = source_states.saturating_add(d.state_count());
        guard(
            "grammar input states",
            source_states,
            budget.max_input_states,
        )?;
        term.push(Arc::new(d.minimize(budget, &mut work)?));
    }
    let mut total_symbols = 0usize;
    for rules in &input.rules {
        for prod in rules {
            total_symbols = total_symbols.saturating_add(prod.len() + 1);
            guard(
                "grammar production symbols",
                total_symbols,
                budget.max_symbols,
            )?;
            for s in prod {
                match s {
                    Symbol::Terminal(t) if *t as usize >= term.len() => {
                        return Err(AnalysisError::InvalidInput(
                            "terminal outside grammar domain".into(),
                        ));
                    }
                    Symbol::Nonterminal(n) if *n as usize >= input.rules.len() => {
                        return Err(AnalysisError::InvalidInput(
                            "nonterminal outside grammar domain".into(),
                        ));
                    }
                    _ => {}
                }
            }
        }
    }
    // Productiveness is essential before FIRST/LAST or SCC recognition: a dead
    // rule is not an extra possible trace and never prevents a live optimization.
    let mut productive = vec![false; input.rules.len()];
    loop {
        let mut changed = false;
        for (v, ps) in input.rules.iter().enumerate() {
            if !productive[v] {
                spend(
                    &mut work,
                    ps.iter().map(|p| p.len() + 1).sum(),
                    budget.max_work,
                )?;
                if ps.iter().any(|p| {
                    p.iter().all(|s| match s {
                        Symbol::Terminal(t) => !term[*t as usize].is_empty(),
                        Symbol::Nonterminal(n) => productive[*n as usize],
                    })
                }) {
                    productive[v] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut stats = PreparationStats {
        source_terminals: term.len(),
        source_nonterminals: input.rules.len(),
        source_dfa_states: source_states,
        ..Default::default()
    };
    if !productive[input.start as usize] {
        stats.empty_language = true;
        stats.work = work;
        return Ok(Lowered {
            grammar: Grammar {
                terminals: vec![],
                rules: vec![vec![]],
                start: 0,
            },
            root_regular: Some(Dfa::empty()),
            stats,
        });
    }
    let mut rules = input
        .rules
        .iter()
        .map(|ps| {
            ps.iter()
                .filter(|p| {
                    p.iter().all(|s| match s {
                        Symbol::Terminal(t) => !term[*t as usize].is_empty(),
                        Symbol::Nonterminal(n) => productive[*n as usize],
                    })
                })
                .cloned()
                .collect()
        })
        .collect::<Rules>();
    let mut reachable = vec![false; rules.len()];
    let mut queue = vec![input.start as usize];
    while let Some(v) = queue.pop() {
        if reachable[v] {
            continue;
        }
        reachable[v] = true;
        for p in &rules[v] {
            for s in p {
                if let Symbol::Nonterminal(n) = s {
                    queue.push(*n as usize);
                }
            }
        }
    }
    for (v, ps) in rules.iter_mut().enumerate() {
        if !reachable[v] {
            ps.clear();
        }
    }
    stats.reachable_nonterminals = reachable.iter().filter(|&&x| x).count();
    let mut regular = vec![None::<Arc<Dfa>>; rules.len()];
    if options.fold_regular {
        for component in components(&rules, &reachable) {
            let mut member = vec![false; rules.len()];
            for &v in &component {
                member[v] = true;
            }
            let mut right = true;
            let mut left = true;
            let mut known = true;
            for &v in &component {
                for p in &rules[v] {
                    let internal = p
                        .iter()
                        .enumerate()
                        .filter_map(|(i, s)| match s {
                            Symbol::Nonterminal(w) if member[*w as usize] => Some(i),
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    if internal.len() > 1 {
                        right = false;
                        left = false;
                    }
                    if internal.len() == 1 {
                        right &= internal[0] + 1 == p.len();
                        left &= internal[0] == 0;
                    }
                    for s in p {
                        if let Symbol::Nonterminal(w) = s {
                            if !member[*w as usize] && regular[*w as usize].is_none() {
                                known = false;
                            }
                        }
                    }
                }
            }
            if !known || !(right || left) {
                stats.nonregular_components += 1;
                continue;
            }
            // Alias/terminal and epsilon productions need no copying or subset construction.
            if component.len() == 1 {
                let v = component[0];
                if rules[v].len() == 1 {
                    if rules[v][0].is_empty() {
                        regular[v] = Some(Arc::new(Dfa::epsilon()));
                        stats.folded_nonterminals += 1;
                        continue;
                    }
                    if rules[v][0].len() == 1 {
                        let d = match rules[v][0][0] {
                            Symbol::Terminal(t) => Some(term[t as usize].clone()),
                            Symbol::Nonterminal(n) if !member[n as usize] => {
                                regular[n as usize].clone()
                            }
                            _ => None,
                        };
                        if let Some(d) = d {
                            regular[v] = Some(d);
                            stats.folded_nonterminals += 1;
                            continue;
                        }
                    }
                }
            }
            let built = (|| -> Result<Vec<Arc<Dfa>>, AnalysisError> {
                let mut nfa = Nfa::new();
                let mut entries = vec![0u32; rules.len()];
                for &v in &component {
                    entries[v] = nfa.state(budget)?;
                }
                let anchor = nfa.state(budget)?;
                for &v in &component {
                    for p in &rules[v] {
                        let internal = p.iter().position(
                            |s| matches!(s,Symbol::Nonterminal(n) if member[*n as usize]),
                        );
                        let (mut source, target, sequence) = if right {
                            let target = internal.map_or(anchor, |i| {
                                let Symbol::Nonterminal(n) = p[i] else {
                                    unreachable!()
                                };
                                entries[n as usize]
                            });
                            (
                                entries[v],
                                target,
                                if internal.is_some() {
                                    &p[..p.len() - 1]
                                } else {
                                    p.as_slice()
                                },
                            )
                        } else {
                            let source = internal.map_or(anchor, |i| {
                                let Symbol::Nonterminal(n) = p[i] else {
                                    unreachable!()
                                };
                                entries[n as usize]
                            });
                            (
                                source,
                                entries[v],
                                if internal.is_some() {
                                    &p[1..]
                                } else {
                                    p.as_slice()
                                },
                            )
                        };
                        if sequence.is_empty() {
                            nfa.epsilon(source, target);
                        }
                        for (i, s) in sequence.iter().enumerate() {
                            let end = if i + 1 == sequence.len() {
                                target
                            } else {
                                nfa.state(budget)?
                            };
                            let d = match s {
                                Symbol::Terminal(t) => term[*t as usize].as_ref(),
                                Symbol::Nonterminal(n) => {
                                    regular[*n as usize].as_ref().unwrap().as_ref()
                                }
                            };
                            nfa.append(source, end, d, budget, &mut work)?;
                            source = end;
                        }
                    }
                }
                component
                    .iter()
                    .map(|&v| {
                        nfa.determinize(
                            if right { entries[v] } else { anchor },
                            if right { anchor } else { entries[v] },
                            budget,
                            &mut work,
                        )
                        .map(Arc::new)
                    })
                    .collect()
            })();
            match built {
                Ok(ds) => {
                    for (&v, d) in component.iter().zip(ds) {
                        regular[v] = Some(d);
                    }
                    stats.folded_nonterminals += component.len();
                    stats.folded_components += 1;
                    if !right {
                        stats.left_linear_components += 1;
                    }
                }
                Err(AnalysisError::BudgetExceeded { .. }) => {
                    stats.budget_declined_components += 1;
                }
                Err(e) => return Err(e),
            }
        }
    }
    let root_regular = regular[input.start as usize]
        .as_ref()
        .map(|d| d.as_ref().clone());
    // Stop traversing at a proved regular island. Keeping its old descendant
    // terminals would recreate the very over-refinement this API eliminates.
    let mut frontier = BTreeSet::<Symbol>::new();
    let mut keep = BTreeSet::<usize>::new();
    let mut todo = vec![Symbol::Nonterminal(input.start)];
    while let Some(s) = todo.pop() {
        match s {
            Symbol::Terminal(_) => {
                frontier.insert(s);
            }
            Symbol::Nonterminal(n) if regular[n as usize].is_some() => {
                frontier.insert(s);
            }
            Symbol::Nonterminal(n) => {
                if keep.insert(n as usize) {
                    for p in &rules[n as usize] {
                        todo.extend_from_slice(p);
                    }
                }
            }
        }
    }
    let mut new_rules = vec![Vec::new(); keep.len()];
    let mut ntmap = vec![None; rules.len()];
    for (i, &v) in keep.iter().enumerate() {
        ntmap[v] = Some(i as u32);
    }
    let mut replacements = std::collections::BTreeMap::<Symbol, Option<Symbol>>::new();
    let mut terminals = Vec::<Dfa>::new();
    let mut language_ids = FxLanguages::default();
    for s in frontier {
        let d = match s {
            Symbol::Terminal(t) => term[t as usize].as_ref(),
            Symbol::Nonterminal(n) => regular[n as usize].as_ref().unwrap().as_ref(),
        };
        let positive = d.positive().minimize(budget, &mut work)?;
        if positive.is_empty() {
            replacements.insert(s, None);
            continue;
        }
        let id = if let Some(&id) = language_ids.get(&positive) {
            id
        } else {
            let id = terminals.len() as u32;
            language_ids.insert(positive.clone(), id);
            terminals.push(positive);
            id
        };
        let symbol = if d.nullable() {
            let n = new_rules.len() as u32;
            new_rules.push(vec![vec![], vec![Symbol::Terminal(id)]]);
            Symbol::Nonterminal(n)
        } else {
            Symbol::Terminal(id)
        };
        replacements.insert(s, Some(symbol));
    }
    for &v in &keep {
        for prod in &rules[v] {
            let mut out = Vec::new();
            for &s in prod {
                if let Some(value) = replacements.get(&s) {
                    if let Some(symbol) = value {
                        out.push(*symbol);
                    }
                } else {
                    let Symbol::Nonterminal(n) = s else {
                        unreachable!()
                    };
                    out.push(Symbol::Nonterminal(ntmap[n as usize].unwrap()));
                }
            }
            new_rules[ntmap[v].unwrap() as usize].push(out);
        }
    }
    let start = if let Some(&s) = replacements.get(&Symbol::Nonterminal(input.start)) {
        let n = new_rules.len() as u32;
        new_rules.push(vec![s.into_iter().collect()]);
        n
    } else {
        ntmap[input.start as usize].unwrap()
    };
    stats.retained_terminals = terminals.len();
    stats.retained_nonterminals = new_rules.len();
    stats.retained_dfa_states = terminals.iter().map(Dfa::state_count).sum();
    stats.root_is_regular = root_regular.is_some();
    stats.work = work;
    Ok(Lowered {
        grammar: Grammar {
            start,
            terminals,
            rules: new_rules,
        },
        root_regular,
        stats,
    })
}
type FxLanguages = rustc_hash::FxHashMap<Dfa, u32>;

/// Exact possible adjacent *terminal labels* in derivable terminal words.
/// This is a grammar-aware overapproximation of stack context, not full PDA
/// reachability. Nullable symbols are handled without exponential expansion.
pub(super) fn follows(g: &Grammar, budget: &Budget) -> Result<Vec<Vec<u32>>, AnalysisError> {
    let n = g.rules.len();
    let t = g.terminals.len();
    guard(
        "grammar adjacency cells",
        n.saturating_mul(t).saturating_mul(2) + t.saturating_mul(t),
        budget.max_cells,
    )?;
    let mut work = 0;
    let mut nullable = vec![false; n];
    loop {
        let mut changed = false;
        for (v, ps) in g.rules.iter().enumerate() {
            if !nullable[v]
                && ps.iter().any(|p| {
                    p.iter()
                        .all(|s| matches!(s,Symbol::Nonterminal(w) if nullable[*w as usize]))
                })
            {
                nullable[v] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut first = vec![BTreeSet::<u32>::new(); n];
    let mut last = first.clone();
    loop {
        let mut changed = false;
        for (v, ps) in g.rules.iter().enumerate() {
            for p in ps {
                for reverse in [false, true] {
                    let mut added = BTreeSet::new();
                    for &s in if reverse {
                        p.iter().rev().copied().collect::<Vec<_>>()
                    } else {
                        p.clone()
                    }
                    .iter()
                    {
                        spend(&mut work, t + 1, budget.max_work)?;
                        match s {
                            Symbol::Terminal(a) => {
                                added.insert(a);
                                break;
                            }
                            Symbol::Nonterminal(w) => {
                                added.extend(if reverse {
                                    &last[w as usize]
                                } else {
                                    &first[w as usize]
                                });
                                if !nullable[w as usize] {
                                    break;
                                }
                            }
                        }
                    }
                    let target = if reverse { &mut last[v] } else { &mut first[v] };
                    let before = target.len();
                    target.extend(added);
                    changed |= before != target.len();
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut output = vec![BTreeSet::new(); t];
    for ps in &g.rules {
        for p in ps {
            let mut suffix = BTreeSet::<u32>::new();
            for s in p.iter().rev() {
                let (a, b, empty) = match s {
                    Symbol::Terminal(t) => (BTreeSet::from([*t]), BTreeSet::from([*t]), false),
                    Symbol::Nonterminal(n) => (
                        first[*n as usize].clone(),
                        last[*n as usize].clone(),
                        nullable[*n as usize],
                    ),
                };
                for v in b {
                    spend(&mut work, suffix.len() + 1, budget.max_work)?;
                    output[v as usize].extend(&suffix);
                }
                if !empty {
                    suffix.clear();
                }
                suffix.extend(a);
            }
        }
    }
    Ok(output
        .into_iter()
        .map(|s| s.into_iter().collect())
        .collect())
}
