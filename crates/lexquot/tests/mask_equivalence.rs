use Symbol::{Nonterminal as N, Terminal as T};
use lexquot::grammar::{Algorithm, Dfa, Grammar, Options, Symbol};
use lexquot::{Vocab, parse_regex, trace::TraceDfa};
fn from_regex(s: &str) -> Grammar {
    Grammar {
        terminals: vec![Dfa::from(
            &TraceDfa::from_expression(&parse_regex(s, false)).unwrap(),
        )],
        rules: vec![vec![vec![T(0)]]],
        start: 0,
    }
}
fn vocab(words: &[&[u8]]) -> Vocab {
    Vocab::new(
        words
            .iter()
            .enumerate()
            .map(|(i, w)| (i as u32, w.to_vec()))
            .collect(),
    )
}
fn words(n: usize) -> Vec<Vec<u8>> {
    let mut all = vec![vec![]];
    let mut level = all.clone();
    for _ in 0..n {
        let mut next = vec![];
        for p in &level {
            for b in b"ab" {
                let mut w = p.clone();
                w.push(*b);
                next.push(w);
            }
        }
        all.extend(next.clone());
        level = next;
    }
    all.into_iter().filter(|w| !w.is_empty()).collect()
}
// Direct raw-DFA reachability/coaccessibility oracle: independent of minimizer
// and backward-column classifier. A missing transition leads to dead None.
fn signatures(d: &Dfa, ws: &[Vec<u8>]) -> Vec<Vec<bool>> {
    let mut roots = vec![d.start];
    let mut seen = vec![false; d.accepting.len()];
    seen[d.start as usize] = true;
    let mut k = 0;
    while k < roots.len() {
        for &(_, t) in &d.transitions[roots[k] as usize] {
            if !seen[t as usize] {
                seen[t as usize] = true;
                roots.push(t);
            }
        }
        k += 1;
    }
    let mut live = d.accepting.clone();
    loop {
        let mut changed = false;
        for (s, row) in d.transitions.iter().enumerate() {
            if !live[s] && row.iter().any(|(_, t)| live[*t as usize]) {
                live[s] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    ws.iter()
        .map(|w| {
            roots
                .iter()
                .map(|&q| {
                    let mut s = Some(q);
                    for b in w {
                        s = s.and_then(|q| {
                            d.transitions[q as usize]
                                .iter()
                                .find(|(a, _)| a == b)
                                .map(|(_, t)| *t)
                        });
                    }
                    s.is_some_and(|q| live[q as usize])
                })
                .collect()
        })
        .collect()
}
#[test]
fn masks_merge_different_futures_but_representative_commits_do_not() {
    let p = from_regex("a0c|a1d").prepare(Options::default()).unwrap();
    let v = vocab(&[b"0", b"1", b"c", b"d"]);
    let mask = p.analyze_masks(&v).unwrap();
    let strong = p.analyze(&v).unwrap();
    assert_eq!(mask.algorithm, Algorithm::RegularDfaMasks);
    assert_eq!(mask.partition.token_class(0), mask.partition.token_class(1));
    assert_ne!(
        strong.partition.token_class(0),
        strong.partition.token_class(1)
    );
    assert!(p.regular_language().unwrap().accepts(b"a0c"));
    assert!(!p.regular_language().unwrap().accepts(b"a1c"));
}
#[test]
fn generated_raw_dfas_match_exact_forward_liveness_at_every_reachable_state() {
    let ws = words(4);
    let mut seed = 58392u64;
    let mut rand = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for _ in 0..120 {
        let n = 2 + (rand() % 8) as usize;
        let start = (rand() % n as u64) as u32;
        let d = Dfa::new(
            start,
            (0..n).map(|_| rand() % 3 == 0).collect(),
            (0..n)
                .map(|_| {
                    b"ab"
                        .iter()
                        .filter_map(|&b| {
                            let r = rand();
                            (r % 5 != 0).then_some((b, ((r / 5) % n as u64) as u32))
                        })
                        .collect()
                })
                .collect(),
        );
        let truth = signatures(&d, &ws);
        let g = Grammar {
            terminals: vec![d],
            rules: vec![vec![vec![T(0)]]],
            start: 0,
        };
        let v = Vocab::new(
            ws.iter()
                .enumerate()
                .map(|(i, w)| ((3 * i + 7) as u32, w.clone()))
                .collect(),
        );
        let p = g.prepare(Options::default()).unwrap();
        let a = p.analyze_masks(&v).unwrap();
        let strong = p.analyze(&v).unwrap();
        for i in 0..ws.len() {
            for j in 0..ws.len() {
                let id = (3 * i + 7) as u32;
                let jd = (3 * j + 7) as u32;
                assert_eq!(
                    a.partition.token_class(id) == a.partition.token_class(jd),
                    truth[i] == truth[j],
                    "i={i} j={j}"
                );
                if strong.partition.token_class(id) == strong.partition.token_class(jd) {
                    assert_eq!(a.partition.token_class(id), a.partition.token_class(jd));
                }
            }
        }
    }
}
#[test]
fn packed_boundaries_and_long_tokens_match_raw_forward_oracle() {
    let n = 131;
    let mut rows = vec![vec![]; n];
    for (s, row) in rows.iter_mut().enumerate().take(n - 1) {
        row.push((b'a', (s + 1) as u32));
    }
    let mut finals = vec![false; n];
    finals[n - 1] = true;
    let d = Dfa::new(0, finals, rows);
    let ws = (1..=135).map(|n| vec![b'a'; n]).collect::<Vec<_>>();
    let truth = signatures(&d, &ws);
    let g = Grammar {
        terminals: vec![d],
        rules: vec![vec![vec![T(0)]]],
        start: 0,
    };
    let v = Vocab::new(
        ws.iter()
            .enumerate()
            .map(|(i, w)| (i as u32, w.clone()))
            .collect(),
    );
    let p = g.prepare(Options::default()).unwrap();
    let a = p.analyze_masks(&v).unwrap();
    for i in 0..ws.len() {
        for j in 0..ws.len() {
            assert_eq!(
                a.partition.token_class(i as u32) == a.partition.token_class(j as u32),
                truth[i] == truth[j]
            );
        }
    }
}
#[test]
fn cached_uncached_and_duplicate_sparse_tokens_are_identical() {
    let g = from_regex("a(b|c)*d");
    let v = Vocab::new(vec![
        (19, b"b".to_vec()),
        (902, b"cc".to_vec()),
        (12000, b"b".to_vec()),
        (77, b"!".to_vec()),
    ]);
    let a = g
        .prepare(Options::default())
        .unwrap()
        .analyze_masks(&v)
        .unwrap();
    let b = g
        .prepare(Options {
            cache_transitions: false,
            ..Default::default()
        })
        .unwrap()
        .analyze_masks(&v)
        .unwrap();
    assert_eq!(a.partition.classes, b.partition.classes);
    assert_eq!(a.partition.token_class(19), a.partition.token_class(12000));
    assert_eq!(a.partition.token_class(19), a.partition.token_class(902));
    assert!(a.partition.dead_class.is_some());
}
#[test]
fn nonregular_path_is_mask_safe_and_labelled_not_minimal() {
    let g = Grammar {
        terminals: vec![
            Dfa::from(&TraceDfa::from_expression(&parse_regex("a", false)).unwrap()),
            Dfa::from(&TraceDfa::from_expression(&parse_regex("b", false)).unwrap()),
        ],
        rules: vec![vec![vec![], vec![T(0), N(0), T(1)]]],
        start: 0,
    };
    let p = g.prepare(Options::default()).unwrap();
    assert!(p.regular_language().is_none());
    let v = vocab(&[b"a", b"b", b"aa", b"ab"]);
    let m = p.analyze_masks(&v).unwrap();
    assert_eq!(m.algorithm, Algorithm::GrammarScopedMasks);
    assert!(m.contract.contains("sufficient"));
    let ws = words(5);
    let viable = |w: &[u8]| {
        let a = w.iter().take_while(|&&b| b == b'a').count();
        w[a..].iter().all(|&b| b == b'b') && w.len() - a <= a
    };
    let tokens = [b"a".to_vec(), b"b".to_vec(), b"aa".to_vec(), b"ab".to_vec()];
    for x in ws {
        for i in 0..tokens.len() {
            for j in 0..tokens.len() {
                if m.partition.token_class(i as u32) == m.partition.token_class(j as u32) {
                    assert_eq!(
                        viable(&[x.clone(), tokens[i].clone()].concat()),
                        viable(&[x.clone(), tokens[j].clone()].concat())
                    );
                }
            }
        }
    }
}
#[test]
fn epsilon_empty_and_unreachable_components_do_not_change_masks() {
    for accept in [false, true] {
        let g = Grammar {
            terminals: vec![Dfa::new(
                0,
                vec![accept, true],
                vec![vec![], vec![(b'a', 1)]],
            )],
            rules: vec![vec![vec![T(0)]]],
            start: 0,
        };
        let p = g.prepare(Options::default()).unwrap();
        let a = p.analyze_masks(&vocab(&[b"a", b"aa", b"b"])).unwrap();
        assert_eq!(a.partition.classes.len(), 1);
        assert_eq!(a.partition.dead_class, Some(0));
    }
}
#[test]
fn original_commits_preserve_masks_and_eos_while_substitution_can_fail() {
    let p = from_regex("a|ab").prepare(Options::default()).unwrap();
    let v = vocab(&[b"a", b"ab", b"b"]);
    let m = p.analyze_masks(&v).unwrap();
    assert_eq!(m.partition.token_class(0), m.partition.token_class(1));
    // Both viable initially, but EOS and next masks must use ACTUAL consumed word.
    let d = p.regular_language().unwrap();
    assert!(d.accepts(b"a"));
    assert!(d.accepts(b"ab"));
    assert!(!d.accepts(b"abb"));
}
#[test]
fn work_budget_errors_do_not_return_partial_partition() {
    let mut opts = Options::default();
    opts.trace_budget.max_work = 1;
    let p = from_regex("[ab]+").prepare(opts).unwrap();
    assert!(p.analyze_masks(&vocab(&[b"ab"])).is_err());
    let empty = from_regex("[ab]+")
        .prepare(Options::default())
        .unwrap()
        .analyze_masks(&Vocab::new(vec![]))
        .unwrap();
    assert!(empty.partition.classes.is_empty());
}

#[test]
fn scoped_masks_for_disabled_folding_preserve_finite_language_prefix_viability() {
    let g = from_regex("a0c|a1d");
    let p = g
        .prepare(Options {
            fold_regular: false,
            regular_actions: false,
            ..Default::default()
        })
        .unwrap();
    let ws = [
        b"0".to_vec(),
        b"1".to_vec(),
        b"a".to_vec(),
        b"c".to_vec(),
        b"d".to_vec(),
        b"a0".to_vec(),
        b"a1".to_vec(),
    ];
    let v = Vocab::new(
        ws.iter()
            .enumerate()
            .map(|(i, w)| (i as u32, w.clone()))
            .collect(),
    );
    let m = p.analyze_masks(&v).unwrap();
    let language = [b"a0c".to_vec(), b"a1d".to_vec()];
    let prefixes = language
        .iter()
        .flat_map(|w| (0..=w.len()).map(|i| w[..i].to_vec()))
        .collect::<Vec<_>>();
    for x in prefixes {
        for i in 0..ws.len() {
            for j in 0..ws.len() {
                if m.partition.token_class(i as u32) == m.partition.token_class(j as u32) {
                    let xu = [x.clone(), ws[i].clone()].concat();
                    let xv = [x.clone(), ws[j].clone()].concat();
                    assert_eq!(
                        language.iter().any(|w| w.starts_with(&xu)),
                        language.iter().any(|w| w.starts_with(&xv))
                    );
                }
            }
        }
    }
}
