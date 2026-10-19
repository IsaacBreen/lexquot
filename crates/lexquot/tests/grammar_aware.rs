//! Independent finite-language and context-substitution qualification. The
//! membership oracle expands the ORIGINAL CFG, never the token classifier.
use lexquot::grammar::Symbol::{Nonterminal as N, Terminal as T};
use lexquot::grammar::{Algorithm, Budget, Dfa, Grammar, Options, TokenPartition};
use lexquot::{Vocab, parse_regex, trace::TraceDfa};
use std::collections::HashMap;
fn regex(s: &str) -> Dfa {
    Dfa::from(&TraceDfa::from_expression(&parse_regex(s, false)).unwrap())
}
fn words(alphabet: &[u8], n: usize) -> Vec<Vec<u8>> {
    let mut out = vec![vec![]];
    let mut level = vec![vec![]];
    for _ in 0..n {
        level = level
            .iter()
            .flat_map(|s| {
                alphabet.iter().map(move |&b| {
                    let mut t = s.clone();
                    t.push(b);
                    t
                })
            })
            .collect();
        out.extend(level.clone());
    }
    out
}
fn membership(g: &Grammar, x: &[u8]) -> bool {
    let m = x.len() + 1;
    let mut table = vec![vec![false; m * m]; g.rules.len()];
    let terminals = g
        .terminals
        .iter()
        .map(|d| {
            (0..m)
                .flat_map(|i| (0..m).map(move |j| i <= j && d.accepts(&x[i..j])))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    loop {
        let mut changed = false;
        for (a, prods) in g.rules.iter().enumerate() {
            for prod in prods {
                for begin in 0..m {
                    let mut positions = vec![false; m];
                    positions[begin] = true;
                    for s in prod {
                        let matrix = match s {
                            T(t) => &terminals[*t as usize],
                            N(n) => &table[*n as usize],
                        };
                        let mut next = vec![false; m];
                        for i in begin..m {
                            if positions[i] {
                                for j in i..m {
                                    next[j] |= matrix[i * m + j];
                                }
                            }
                        }
                        positions = next;
                    }
                    for end in begin..m {
                        if positions[end] && !table[a][begin * m + end] {
                            table[a][begin * m + end] = true;
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    table[g.start as usize][x.len()]
}
fn cached_membership(g: &Grammar, x: Vec<u8>, cache: &mut HashMap<Vec<u8>, bool>) -> bool {
    if let Some(&a) = cache.get(&x) {
        a
    } else {
        let a = membership(g, &x);
        cache.insert(x, a);
        a
    }
}
fn check(g: &Grammar, alphabet: &[u8], options: Options) -> TokenPartition {
    let p = g.prepare(options).unwrap();
    for w in words(alphabet, 5) {
        let original = membership(g, &w);
        assert_eq!(
            original,
            membership(p.normalized_grammar(), &w),
            "normalization changed {w:?}: {g:?}"
        );
        if let Some(dfa) = p.regular_language() {
            assert_eq!(
                original,
                dfa.accepts(&w),
                "regular certificate changed {w:?}: {g:?}"
            );
        }
    }
    let tokens = words(alphabet, 3).into_iter().skip(1).collect::<Vec<_>>();
    let vocab = Vocab::new(
        tokens
            .iter()
            .enumerate()
            .map(|(i, b)| (i as u32, b.clone()))
            .collect(),
    );
    let result = p.analyze(&vocab).unwrap();
    let contexts = words(alphabet, 2);
    let mut cache = HashMap::new();
    for (i, v) in tokens.iter().enumerate() {
        let c = result.partition.token_class(i as u32).unwrap();
        let rep = result.partition.representatives[c as usize];
        let r = &tokens[rep as usize];
        if v == r {
            continue;
        }
        for x in &contexts {
            for y in &contexts {
                let a = [x.as_slice(), v.as_slice(), y.as_slice()].concat();
                let b = [x.as_slice(), r.as_slice(), y.as_slice()].concat();
                assert_eq!(
                    cached_membership(g, a.clone(), &mut cache),
                    cached_membership(g, b.clone(), &mut cache),
                    "unsafe representative: {a:?} versus {b:?}; original grammar {g:?}"
                );
            }
        }
    }
    result.partition
}
#[test]
fn right_linear_string_fragment_is_one_language_not_a_sequence_counter() {
    let g = Grammar {
        terminals: vec![regex("\""), regex("[ab]")],
        start: 0,
        rules: vec![vec![vec![T(0), N(1)]], vec![vec![T(0)], vec![T(1), N(1)]]],
    };
    let prepared = g.prepare(Options::default()).unwrap();
    assert!(prepared.stats().root_is_regular);
    assert_eq!(prepared.stats().retained_terminals, 1);
    let tokens = [
        b"a".as_slice(),
        b"b",
        b"aa",
        b"abb",
        b"\"a",
        b"\"b",
        b"\"\"",
        b"\"\"\"\"",
    ];
    let v = Vocab::new(
        tokens
            .iter()
            .enumerate()
            .map(|(i, b)| (i as u32, b.to_vec()))
            .collect(),
    );
    let r = prepared.analyze(&v).unwrap();
    assert_eq!(r.algorithm, Algorithm::RegularDfaActions);
    for i in 1..4 {
        assert_eq!(r.partition.token_class(0), r.partition.token_class(i));
    }
    assert_eq!(r.partition.token_class(4), r.partition.token_class(5));
    assert_ne!(r.partition.token_class(6), r.partition.token_class(7));
    check(&g, b"ab\"", Options::default());
}
#[test]
fn left_linear_components_preserve_order_and_nullable_bases() {
    let g = Grammar {
        terminals: vec![regex("a"), regex("b")],
        start: 0,
        rules: vec![vec![vec![N(1)]], vec![vec![N(1), T(0)], vec![T(1)], vec![]]],
    };
    let p = g.prepare(Options::default()).unwrap();
    assert!(p.stats().root_is_regular);
    assert!(p.stats().left_linear_components > 0);
    for w in [b"".as_slice(), b"a", b"b", b"baaa"] {
        assert!(membership(&g, w));
    }
    assert!(!membership(&g, b"ab"));
    check(&g, b"ab", Options::default());
}
#[test]
fn genuinely_nested_recursion_is_not_misidentified_as_regular() {
    let g = Grammar {
        terminals: vec![regex("a"), regex("b")],
        start: 0,
        rules: vec![vec![vec![], vec![T(0), N(0), T(1)]]],
    };
    let p = g.prepare(Options::default()).unwrap();
    assert!(!p.stats().root_is_regular);
    assert!(p.stats().nonregular_components > 0);
    check(&g, b"ab", Options::default());
}
#[test]
fn mixed_direction_recursive_scc_declines_safely() {
    let g = Grammar {
        terminals: vec![regex("a"), regex("b")],
        start: 0,
        rules: vec![vec![vec![T(0), N(0)], vec![N(0), T(1)], vec![]]],
    };
    assert!(
        !g.prepare(Options::default())
            .unwrap()
            .stats()
            .root_is_regular
    );
    check(&g, b"ab", Options::default());
}
#[test]
fn nullable_terminal_start_is_lifted_without_losing_positive_cycles() {
    let a_star = Dfa::new(0, vec![true], vec![vec![(b'a', 0)]]);
    let g = Grammar {
        terminals: vec![a_star, regex("b")],
        start: 0,
        rules: vec![vec![vec![T(0), T(1)]]],
    };
    check(&g, b"ab", Options::default());
    check(
        &g,
        b"ab",
        Options {
            fold_regular: false,
            ..Default::default()
        },
    );
}
#[test]
fn unreachable_and_unproductive_grammar_branches_do_not_pollute_observation() {
    let g = Grammar {
        terminals: vec![regex("a+"), regex("b{1,6}")],
        start: 0,
        rules: vec![
            vec![vec![T(0)], vec![N(1), T(1)]],
            vec![vec![N(1)]],
            vec![vec![T(1)]],
        ],
    };
    let p = g.prepare(Options::default()).unwrap();
    assert_eq!(p.stats().retained_terminals, 1);
    check(&g, b"ab", Options::default());
}
#[test]
fn empty_and_epsilon_only_languages_return_complete_dead_token_classes() {
    for rules in [vec![vec![]], vec![vec![vec![]]], vec![vec![vec![N(0)]]]] {
        let g = Grammar {
            terminals: vec![],
            start: 0,
            rules,
        };
        let p = g.prepare(Options::default()).unwrap();
        let v = Vocab::new(vec![(3, b"a".to_vec()), (700, b"ba".to_vec())]);
        let result = p.analyze(&v).unwrap();
        assert_eq!(result.partition.classes, vec![vec![3, 700]]);
        assert_eq!(result.partition.dead_class, Some(0));
        for w in words(b"ab", 3) {
            assert_eq!(membership(&g, &w), membership(p.normalized_grammar(), &w));
        }
    }
}
#[test]
fn folding_resource_decline_is_safe_and_does_not_change_the_grammar() {
    let g = Grammar {
        terminals: vec![regex("a"), regex("b")],
        start: 0,
        rules: vec![vec![vec![T(0), T(1)], vec![T(1), T(0)]]],
    };
    let options = Options {
        budget: Budget {
            max_nfa_states: 2,
            ..Default::default()
        },
        ..Default::default()
    };
    let p = g.prepare(options).unwrap();
    assert!(p.stats().budget_declined_components > 0);
    assert!(!p.stats().root_is_regular);
    check(&g, b"ab", options);
}
#[test]
fn duplicate_byte_spellings_sparse_ids_and_fresh_calls_are_stable() {
    let g = Grammar {
        terminals: vec![regex("[ab]+")],
        start: 0,
        rules: vec![vec![vec![T(0)]]],
    };
    let p = g.prepare(Options::default()).unwrap();
    let v = Vocab::new(vec![
        (99, b"a".to_vec()),
        (7, b"a".to_vec()),
        (9811, b"bb".to_vec()),
    ]);
    let a = p.analyze(&v).unwrap();
    let b = p.analyze(&v).unwrap();
    assert_eq!(a.partition.token_ids, vec![7, 99, 9811]);
    assert_eq!(a.partition.classes, b.partition.classes);
    assert_eq!(a.partition.classes.len(), 1);
    assert_eq!(a.partition.representatives, vec![7]);
}
#[test]
fn regular_transformations_match_a_separate_forward_transition_oracle() {
    let g = Grammar {
        terminals: vec![regex("(ab|ba)*aa?")],
        start: 0,
        rules: vec![vec![vec![T(0)]]],
    };
    let p = g.prepare(Options::default()).unwrap();
    let d = p.regular_language().unwrap();
    let tokens = words(b"ab", 5).into_iter().skip(1).collect::<Vec<_>>();
    let v = Vocab::new(
        tokens
            .iter()
            .enumerate()
            .map(|(i, b)| (i as u32, b.clone()))
            .collect(),
    );
    let a = p.analyze(&v).unwrap();
    let keys = tokens
        .iter()
        .map(|bytes| {
            (0..d.state_count())
                .map(|s| {
                    let mut state = Some(s as u32);
                    for b in bytes {
                        state = state.and_then(|s| {
                            d.transitions[s as usize]
                                .iter()
                                .find(|(x, _)| x == b)
                                .map(|(_, t)| *t)
                        });
                    }
                    state
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    for i in 0..tokens.len() {
        for j in 0..tokens.len() {
            assert_eq!(
                keys[i] == keys[j],
                a.partition.token_class(i as u32) == a.partition.token_class(j as u32)
            );
        }
    }
}
#[test]
fn invalid_grammar_indices_are_errors() {
    let mut g = Grammar {
        terminals: vec![regex("a")],
        start: 0,
        rules: vec![vec![vec![N(1)]]],
    };
    assert!(g.prepare(Options::default()).is_err());
    g.rules = vec![vec![vec![T(1)]]];
    assert!(g.prepare(Options::default()).is_err());
    g.rules = vec![vec![vec![T(0)]]];
    g.terminals[0].transitions[0].push((b'a', 999));
    assert!(g.prepare(Options::default()).is_err());
}
#[test]
fn generated_cfgs_preserve_the_original_language_and_all_tested_context_substitutions() {
    let mut seed = 192717u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for case in 0..40 {
        let n = 2 + (next() % 3) as usize;
        let mut rules = vec![vec![]; n];
        for ps in &mut rules {
            ps.push(if next() % 3 == 0 {
                vec![]
            } else {
                vec![T((next() % 2) as u32)]
            });
            for _ in 0..2 {
                let len = (next() % 4) as usize;
                let mut rhs = Vec::new();
                for _ in 0..len {
                    rhs.push(if next() % 2 == 0 {
                        T((next() % 2) as u32)
                    } else {
                        N((next() % n as u64) as u32)
                    });
                }
                ps.push(rhs);
            }
        }
        let g = Grammar {
            terminals: vec![regex("a"), regex("b")],
            start: 0,
            rules,
        };
        check(&g, b"ab", Options::default());
        if case % 5 == 0 {
            check(
                &g,
                b"ab",
                Options {
                    regular_actions: false,
                    ..Default::default()
                },
            );
            check(
                &g,
                b"ab",
                Options {
                    fold_regular: false,
                    ..Default::default()
                },
            );
        }
    }
}
