//! Independent small-CFG and raw-DFA safety oracles for the grammar-scoped path.
//! No production grammar-analysis/trace internals are used by `bounded_language`.
use Symbol::{Nonterminal as N, Terminal as T};
use lexquot::trace::grammar::{
    GrammarScope, GrammarSpec, PreparedGrammarTrace, Production, Symbol,
};
use lexquot::trace::{EndpointPolicy, PrepareOptions, PreparedTrace, TraceBudget, TraceDfa};
use lexquot::{Vocab, parse_regex};
use std::collections::{BTreeSet, HashMap};
fn terminal(s: &str) -> TraceDfa {
    TraceDfa::from_expression(&parse_regex(s, false)).unwrap()
}
fn words(alphabet: &[u8], max: usize) -> Vec<Vec<u8>> {
    let mut all = vec![Vec::new()];
    let mut current = all.clone();
    for _ in 0..max {
        let mut next = Vec::new();
        for w in &current {
            for b in alphabet {
                let mut x = w.clone();
                x.push(*b);
                next.push(x)
            }
        }
        all.extend(next.clone());
        current = next;
    }
    all
}
fn accepts(d: &TraceDfa, w: &[u8]) -> bool {
    let mut state = d.start() as usize;
    for b in w {
        let Some((_, s)) = d.transitions()[state].iter().find(|(byte, _)| byte == b) else {
            return false;
        };
        state = *s as usize;
    }
    d.accepting()[state]
}
fn grammar(n: usize, rules: Vec<(u32, Vec<Symbol>)>) -> GrammarSpec {
    GrammarSpec {
        start: 0,
        nonterminals: n,
        productions: rules
            .into_iter()
            .map(|(lhs, rhs)| Production { lhs, rhs })
            .collect(),
    }
}
fn vocab(tokens: &[Vec<u8>]) -> Vocab {
    Vocab::new(
        tokens
            .iter()
            .enumerate()
            .map(|(i, b)| ((i as u32) * 17 + 3, b.clone()))
            .collect(),
    )
}
fn partition_equal(a: &[u32], b: &[u32]) {
    assert_eq!(a.len(), b.len());
    let (mut ab, mut ba) = (HashMap::new(), HashMap::new());
    for (&x, &y) in a.iter().zip(b) {
        assert_eq!(*ab.entry(x).or_insert(y), y);
        assert_eq!(*ba.entry(y).or_insert(x), x);
    }
}
/// Finite least fixed point of the ORIGINAL CFG, substituting original DFA
/// byte languages. Epsilon, both recursion directions and ambiguous derivations
/// terminate because all sets are bounded by `max` bytes.
fn bounded_language(
    ds: &[TraceDfa],
    g: &GrammarSpec,
    alphabet: &[u8],
    max: usize,
) -> BTreeSet<Vec<u8>> {
    let possible = words(alphabet, max);
    let terms = ds
        .iter()
        .map(|d| {
            possible
                .iter()
                .filter(|w| accepts(d, w))
                .cloned()
                .collect::<BTreeSet<_>>()
        })
        .collect::<Vec<_>>();
    let mut nts = vec![BTreeSet::<Vec<u8>>::new(); g.nonterminals];
    loop {
        let mut changed = false;
        for p in &g.productions {
            let mut strings = BTreeSet::from([Vec::<u8>::new()]);
            for sym in &p.rhs {
                let rhs = match sym {
                    T(t) => &terms[*t as usize],
                    N(n) => &nts[*n as usize],
                };
                let mut next = BTreeSet::new();
                for left in &strings {
                    for right in rhs {
                        if left.len() + right.len() <= max {
                            let mut s = left.clone();
                            s.extend(right);
                            next.insert(s);
                        }
                    }
                }
                strings = next;
                if strings.is_empty() {
                    break;
                }
            }
            let before = nts[p.lhs as usize].len();
            nts[p.lhs as usize].extend(strings);
            changed |= before != nts[p.lhs as usize].len();
        }
        if !changed {
            break;
        }
    }
    nts[g.start as usize].clone()
}
fn check_contexts(
    ds: &[TraceDfa],
    g: &GrammarSpec,
    alphabet: &[u8],
    token_max: usize,
    context_max: usize,
) -> usize {
    let tokens = words(alphabet, token_max)
        .into_iter()
        .filter(|w| !w.is_empty())
        .collect::<Vec<_>>();
    let v = vocab(&tokens);
    let prep = PreparedGrammarTrace::new(ds, g, PrepareOptions::default()).unwrap();
    let a = prep.analyze(&v, TraceBudget::default()).unwrap().partition;
    let accepted = bounded_language(ds, g, alphabet, token_max + context_max * 2);
    let contexts = words(alphabet, context_max);
    let mut checks = 0;
    for (i, b) in tokens.iter().enumerate() {
        let c = a.token_classes[i] as usize;
        let r = ((a.representatives[c] - 3) / 17) as usize;
        let w = &tokens[r];
        if b == w {
            continue;
        }
        for l in &contexts {
            for right in &contexts {
                let x = [l.as_slice(), b.as_slice(), right.as_slice()].concat();
                let y = [l.as_slice(), w.as_slice(), right.as_slice()].concat();
                assert_eq!(
                    accepted.contains(&x),
                    accepted.contains(&y),
                    "incorrect merge {b:?} and {w:?}, contexts{l:?}/{right:?}, G={g:?}"
                );
                checks += 1;
            }
        }
    }
    checks
}
#[test]
fn derived_follows_include_nullable_interiors_but_not_unreachable_or_unproductive_rules() {
    let g = grammar(
        5,
        vec![
            (0, vec![T(0), N(1), T(1)]),
            (1, vec![]),
            (1, vec![T(2)]),
            (2, vec![T(1), T(0)]),
            (0, vec![T(3), N(3)]),
            (3, vec![N(4)]),
            (4, vec![N(3)]),
        ],
    );
    let s = GrammarScope::derive(&g, 4, TraceBudget::default()).unwrap();
    assert_eq!(s.live_terminals, vec![true, true, true, false]);
    assert_eq!(s.allowed_follows, vec![vec![1, 2], vec![], vec![1], vec![]]);
    assert!(s.nullable_nonterminals[1]);
    assert!(!s.nullable_nonterminals[0]);
    assert_eq!(s.retained_productions.len(), 3);
}
#[test]
fn terminal_and_nonterminal_domains_reject_invalid_indices() {
    let b = TraceBudget::default();
    for g in [
        grammar(1, vec![(1, vec![T(0)])]),
        grammar(1, vec![(0, vec![T(1)])]),
        grammar(1, vec![(0, vec![N(1)])]),
        GrammarSpec {
            start: 1,
            ..grammar(1, vec![(0, vec![T(0)])])
        },
        grammar(1, vec![(0, vec![N(0)])]),
    ] {
        assert!(GrammarScope::derive(&g, 1, b).is_err());
    }
    assert!(
        GrammarScope::derive(
            &grammar(1, vec![(0, vec![T(0)])]),
            1,
            TraceBudget { max_work: 0, ..b }
        )
        .is_err()
    );
    assert!(
        GrammarScope::derive(
            &grammar(2, vec![(0, vec![])]),
            1,
            TraceBudget { max_states: 1, ..b }
        )
        .is_err()
    );
}
#[test]
fn whole_lexeme_alphabet_collapses_without_invented_adjacent_terminals() {
    let ds = vec![terminal("[a-z]+"), terminal("[bfnt]")];
    let g = grammar(1, vec![(0, vec![T(0)])]);
    let tokens = vec![
        b"the".to_vec(),
        b"and".to_vec(),
        b"a".to_vec(),
        b"bbbb".to_vec(),
        b"!".to_vec(),
    ];
    let v = vocab(&tokens);
    let new = PreparedGrammarTrace::new(&ds, &g, PrepareOptions::default())
        .unwrap()
        .analyze(&v, TraceBudget::default())
        .unwrap();
    for i in 1..4 {
        assert_eq!(
            new.partition.token_classes[0],
            new.partition.token_classes[i]
        );
    }
    assert_ne!(
        new.partition.token_classes[0],
        new.partition.token_classes[4]
    );
    assert_eq!(new.partition.nondead_class_count(), 1);
    let old = PreparedTrace::new(&ds, PrepareOptions::default())
        .unwrap()
        .request(&v)
        .analyze()
        .unwrap();
    assert!(old.classes.len() > new.partition.classes.len());
}
#[test]
fn escape_alphabet_must_be_preceded_by_escape_not_arbitrary_string_char() {
    let ds = vec![
        terminal("[abnt]"),
        terminal("x"),
        terminal("[nt]"),
        terminal("q"),
    ];
    // S -> q C q, C -> epsilon | character C | x escape C
    let g = grammar(
        2,
        vec![
            (0, vec![T(3), N(1), T(3)]),
            (1, vec![]),
            (1, vec![T(0), N(1)]),
            (1, vec![T(1), T(2), N(1)]),
        ],
    );
    let scope = GrammarScope::derive(&g, ds.len(), TraceBudget::default()).unwrap();
    assert!(!scope.allowed_follows[0].contains(&2));
    assert!(scope.allowed_follows[1].contains(&2));
    let v = vocab(&[
        b"aat".to_vec(),
        b"aab".to_vec(),
        b"aan".to_vec(),
        b"xan".to_vec(),
    ]);
    let result = PreparedGrammarTrace::new(&ds, &g, PrepareOptions::default())
        .unwrap()
        .analyze(&v, TraceBudget::default())
        .unwrap()
        .partition;
    assert_eq!(result.token_classes[0], result.token_classes[1]);
    assert_eq!(result.token_classes[0], result.token_classes[2]);
    assert_ne!(result.token_classes[0], result.token_classes[3]);
}
#[test]
fn recursive_nullable_and_ambiguous_grammars_preserve_all_tested_byte_contexts() {
    let ds = vec![terminal("[ab]"), terminal("a+"), terminal("b+")];
    let grammars = [
        grammar(1, vec![(0, vec![T(0)]), (0, vec![T(0), N(0)])]),
        grammar(
            2,
            vec![(0, vec![T(1), N(1), T(2)]), (1, vec![]), (1, vec![N(0)])],
        ),
        grammar(
            1,
            vec![
                (0, vec![T(1)]),
                (0, vec![T(1), T(2)]),
                (0, vec![T(0), N(0)]),
            ],
        ),
        grammar(
            2,
            vec![(0, vec![N(1), T(2)]), (1, vec![]), (1, vec![N(1), T(1)])],
        ),
    ];
    let mut checks = 0;
    for g in grammars {
        checks += check_contexts(&ds, &g, b"ab", 3, 2);
    }
    assert!(checks > 1000, "test must exercise real nontrivial merges");
}
#[test]
fn seeded_generated_cfgs_preserve_contextual_substitution() {
    let ds = vec![
        terminal("[ab]"),
        terminal("a+"),
        terminal("b"),
        terminal("ab|ba"),
    ];
    let mut seed = 917413u64;
    let mut random = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut total = 0;
    for _ in 0..90 {
        let count = 2 + (random() % 3) as usize;
        let mut rules = Vec::new();
        for n in 0..count {
            rules.push((n as u32, vec![T((random() % 4) as u32)]));
            for _ in 0..2 {
                let len = (random() % 4) as usize;
                let rhs = (0..len)
                    .map(|_| {
                        if random() % 3 == 0 {
                            N((random() % count as u64) as u32)
                        } else {
                            T((random() % 4) as u32)
                        }
                    })
                    .collect();
                rules.push((n as u32, rhs));
            }
        }
        total += check_contexts(&ds, &grammar(count, rules), b"ab", 3, 1);
    }
    assert!(total > 1000);
}
#[test]
fn cached_and_uncached_scoped_analysis_are_identical_with_shared_or_raw_residuals() {
    let ds = vec![terminal("a+"), terminal("a+b"), terminal("b")];
    let g = grammar(
        2,
        vec![
            (0, vec![T(0), N(1), T(2)]),
            (1, vec![]),
            (1, vec![T(1)]),
            (1, vec![T(2), N(1)]),
        ],
    );
    let tokens = words(b"abx", 3)
        .into_iter()
        .filter(|w| !w.is_empty())
        .collect::<Vec<_>>();
    let v = vocab(&tokens);
    let canonical = PreparedGrammarTrace::new(&ds, &g, PrepareOptions::default())
        .unwrap()
        .analyze(&v, TraceBudget::default())
        .unwrap();
    for minimize in [true, false] {
        for share in [true, false] {
            for cache in [true, false] {
                let p = PreparedGrammarTrace::new(
                    &ds,
                    &g,
                    PrepareOptions {
                        minimize,
                        share_across_terminals: share,
                        ..Default::default()
                    },
                )
                .unwrap();
                let got = p
                    .analyze_with(&v, EndpointPolicy::Residual, cache, TraceBudget::default())
                    .unwrap();
                partition_equal(
                    &canonical.partition.token_classes,
                    &got.partition.token_classes,
                );
            }
        }
    }
}
#[test]
fn sparse_original_ids_duplicate_spellings_and_empty_vocabulary_are_preserved() {
    let ds = [terminal("a+")];
    let g = grammar(1, vec![(0, vec![T(0)])]);
    let p = PreparedGrammarTrace::new(&ds, &g, PrepareOptions::default()).unwrap();
    let v = Vocab::new(vec![
        (u32::MAX - 5, b"aa".to_vec()),
        (17, b"a".to_vec()),
        (991, b"aa".to_vec()),
        (5, b"x".to_vec()),
    ]);
    let a = p.analyze(&v, TraceBudget::default()).unwrap().partition;
    assert_eq!(a.token_ids, vec![5, 17, 991, u32::MAX - 5]);
    assert_eq!(a.classes.iter().map(Vec::len).sum::<usize>(), 4);
    assert_eq!(a.token_class(17), a.token_class(u32::MAX - 5));
    assert_eq!(a.representatives[a.token_class(17).unwrap() as usize], 17);
    assert!(
        p.analyze(&Vocab::new(vec![]), TraceBudget::default())
            .unwrap()
            .partition
            .classes
            .is_empty()
    );
}
#[test]
fn epsilon_only_cfg_rejects_all_nonempty_byte_tokens_and_budgets_fail_closed() {
    let ds = [terminal("a+")];
    let g = grammar(1, vec![(0, vec![])]);
    let p = PreparedGrammarTrace::new(&ds, &g, PrepareOptions::default()).unwrap();
    let v = vocab(&[b"a".to_vec(), b"aa".to_vec(), b"xyz".to_vec()]);
    let a = p.analyze(&v, TraceBudget::default()).unwrap().partition;
    assert_eq!(a.classes.len(), 1);
    assert_eq!(a.nondead_class_count(), 0);
    assert_eq!(a.dead_class, Some(0));
    assert!(
        p.analyze(
            &v,
            TraceBudget {
                max_work: 0,
                ..Default::default()
            }
        )
        .is_err()
    );
    assert!(
        p.analyze(
            &v,
            TraceBudget {
                max_reverse_columns: 0,
                ..Default::default()
            }
        )
        .is_err()
    );
    assert!(
        p.analyze(
            &v,
            TraceBudget {
                max_token_bytes: 1,
                ..Default::default()
            }
        )
        .is_err()
    );
}
