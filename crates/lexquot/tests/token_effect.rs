use lexquot::token_effect::SymbolicByteRun;
use lexquot::token_effect::{
    EffectAnalysis, EffectOptions, PreparedTokenEffects, TerminalAutomaton,
};
use std::collections::{BTreeMap, BTreeSet};

fn terminal(s: &str) -> TerminalAutomaton {
    TerminalAutomaton::from_expr(&lexquot::parse_regex(s, false)).unwrap()
}
fn vocab(alphabet: &[u8], max: usize) -> Vec<(u32, Vec<u8>)> {
    let mut out = Vec::new();
    let mut frontier = vec![Vec::new()];
    for _ in 0..max {
        let next = frontier
            .iter()
            .flat_map(|p| {
                alphabet.iter().map(move |&b| {
                    let mut q = p.clone();
                    q.push(b);
                    q
                })
            })
            .collect::<Vec<_>>();
        out.extend(next.iter().cloned());
        frontier = next;
    }
    out.into_iter()
        .enumerate()
        .map(|(i, v)| (i as u32, v))
        .collect()
}
fn normalized(a: &EffectAnalysis) -> Vec<u32> {
    let mut seen = BTreeMap::new();
    a.classes
        .iter()
        .map(|&c| {
            let n = seen.len() as u32;
            *seen.entry(c).or_insert(n)
        })
        .collect()
}
fn accepts_terminal(d: &TerminalAutomaton, x: &[u8]) -> bool {
    let mut q = d.start;
    for &b in x {
        let Some(&(_, s)) = d.transitions[q as usize].iter().find(|e| e.0 == b) else {
            return false;
        };
        q = s;
    }
    d.accepting[q as usize]
}
// Independent segmentation oracle for a finite grammar production. It does
// not use any effect keys, reset DFA, projected states or interned graph.
fn accepts_sequence(ds: &[TerminalAutomaton], seq: &[usize], x: &[u8]) -> bool {
    let mut reachable = BTreeSet::from([0usize]);
    for &t in seq {
        let mut next = BTreeSet::new();
        for &i in &reachable {
            for j in i + 1..=x.len() {
                if accepts_terminal(&ds[t], &x[i..j]) {
                    next.insert(j);
                }
            }
        }
        reachable = next;
    }
    reachable.contains(&x.len())
}

#[test]
fn alphabet_factorization_suffix_sharing_and_collision_checked_stitching_are_exact() {
    let tokens = vocab(b"abc", 4);
    for regex in [
        vec!["a+", "b+", "ab|ac"],
        vec!["[ab]+", "a[bc]*", "c"],
        vec!["ab", "ba", "c+"],
        vec!["a{1,4}", "b{2,5}", "[abc]"],
    ] {
        let ds = regex.iter().map(|s| terminal(s)).collect::<Vec<_>>();
        let slow = PreparedTokenEffects::new(
            &ds,
            EffectOptions {
                partition_first_byte: false,
                cache_suffixes: false,
                ..Default::default()
            },
        )
        .unwrap()
        .analyze(&tokens)
        .unwrap();
        for partition_first_byte in [false, true] {
            for cache_suffixes in [false, true] {
                for constant_stitch_digest in [false, true] {
                    let opts = EffectOptions {
                        partition_first_byte,
                        cache_suffixes,
                        constant_stitch_digest,
                        ..Default::default()
                    };
                    let got = PreparedTokenEffects::new(&ds, opts)
                        .unwrap()
                        .analyze(&tokens)
                        .unwrap();
                    assert_eq!(
                        normalized(&slow),
                        normalized(&got),
                        "{regex:?} partition={partition_first_byte} cache={cache_suffixes}"
                    );
                }
            }
        }
    }
}

#[test]
fn completed_match_finals_and_endpoint_residuals_are_not_live_prefix_observations() {
    let ds = [terminal("a{1,3}"), terminal("b")];
    let tokens = vec![
        (4, b"a".to_vec()),
        (90, b"aa".to_vec()),
        (99, b"aaa".to_vec()),
        (10_000, b"ab".to_vec()),
    ];
    let a = PreparedTokenEffects::new(&ds, EffectOptions::default())
        .unwrap()
        .analyze(&tokens)
        .unwrap();
    assert_eq!(a.stats.token_classes, 4);
    assert!(accepts_sequence(&ds, &[0], b"aaa"));
    assert!(!accepts_sequence(&ds, &[0], b"aaaa"));
}

#[test]
fn duplicate_sparse_ids_are_preserved_and_control_inputs_fail_closed() {
    let ds = [terminal("[ab]+")];
    let prep = PreparedTokenEffects::new(&ds, EffectOptions::default()).unwrap();
    let a = prep
        .analyze(&[
            (u32::MAX, b"a".to_vec()),
            (9, b"a".to_vec()),
            (4, b"b".to_vec()),
        ])
        .unwrap();
    assert_eq!(a.token_ids, vec![4, 9, u32::MAX]);
    assert_eq!(a.stats.token_classes, 1);
    assert_eq!(a.representatives, vec![4]);
    assert!(prep.analyze(&[(0, vec![])]).is_err());
    assert!(prep.analyze(&[(0, vec![b'a']), (0, vec![b'b'])]).is_err());
    assert!(prep.analyze(&[]).unwrap().classes.is_empty());
    assert!(TerminalAutomaton::new(0, vec![true], vec![vec![]]).is_err());
    assert!(TerminalAutomaton::new(0, vec![false], vec![vec![(b'a', 1)]]).is_err());
}

#[test]
fn budgets_abort_without_returning_partial_equivalence() {
    let ds = [terminal("[ab]+")];
    let prep = PreparedTokenEffects::new(
        &ds,
        EffectOptions {
            max_token_bytes: 2,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(prep.analyze(&[(0, b"aaa".to_vec())]).is_err());
    assert!(
        PreparedTokenEffects::new(
            &ds,
            EffectOptions {
                max_table_cells: 1,
                ..Default::default()
            }
        )
        .is_err()
    );
    let prep = PreparedTokenEffects::new(
        &ds,
        EffectOptions {
            max_nodes: 2,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(prep.analyze(&[(0, b"a".to_vec())]).is_err());
}

#[test]
fn projected_initials_match_full_product_for_reachable_regex_components() {
    let tokens = vocab(b"abc", 4);
    for regex in [
        vec!["[ab]+", "b[ac]*", "c"],
        vec!["abc|aba", "[ac]+", "b"],
        vec!["a{1,4}", "b{1,3}", "c"],
    ] {
        let ds = regex.iter().map(|s| terminal(s)).collect::<Vec<_>>();
        let p = PreparedTokenEffects::new(&ds, EffectOptions::default())
            .unwrap()
            .analyze(&tokens)
            .unwrap();
        let c = PreparedTokenEffects::new(
            &ds,
            EffectOptions {
                combined_initial: true,
                ..Default::default()
            },
        )
        .unwrap()
        .analyze(&tokens)
        .unwrap();
        assert_eq!(normalized(&p), normalized(&c), "{regex:?}");
    }
}

#[test]
fn every_computed_merge_preserves_independent_grammar_membership_in_byte_contexts() {
    let ds = [terminal("[ab]+"), terminal("c"), terminal("cc")];
    let tokens = vocab(b"abc", 3);
    let a = PreparedTokenEffects::new(&ds, EffectOptions::default())
        .unwrap()
        .analyze(&tokens)
        .unwrap();
    let mut contexts = vec![Vec::new()];
    contexts.extend(vocab(b"abc", 2).into_iter().map(|(_, b)| b));
    let mut sequences = vec![vec![]];
    sequences.extend(
        vocab(&[0, 1, 2], 3)
            .into_iter()
            .map(|(_, s)| s.into_iter().map(|x| x as usize).collect::<Vec<_>>()),
    );
    let mut checks = 0u64;
    for (i, (_, v)) in tokens.iter().enumerate() {
        let rep = a.representatives[a.classes[i] as usize] as usize;
        let u = &tokens[rep].1;
        if v == u {
            continue;
        }
        for w in &contexts {
            for z in &contexts {
                let x = [w.as_slice(), v.as_slice(), z.as_slice()].concat();
                let y = [w.as_slice(), u.as_slice(), z.as_slice()].concat();
                for seq in &sequences {
                    assert_eq!(
                        accepts_sequence(&ds, seq, &x),
                        accepts_sequence(&ds, seq, &y),
                        "seq={seq:?} x={x:?} y={y:?}"
                    );
                    checks += 1;
                }
            }
        }
    }
    assert!(
        checks > 1000,
        "test fixture must produce actual nontrivial merges"
    );
}

#[test]
fn generated_dfas_preserve_partition_variants_and_context_language() {
    let mut rng = 0x12345u64;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    let tokens = vocab(b"ab", 4);
    for _case in 0..30 {
        let mut ds = Vec::new();
        for _ in 0..3 {
            let n = 3 + (next() % 4) as usize;
            let finals = (0..n).map(|s| s > 0 && next() % 2 == 0).collect::<Vec<_>>();
            let transitions = (0..n)
                .map(|_| {
                    b"ab"
                        .iter()
                        .filter_map(|&b| {
                            let v = next();
                            (v % 5 != 0).then_some((b, (v % n as u64) as u32))
                        })
                        .collect()
                })
                .collect();
            ds.push(TerminalAutomaton::new(0, finals, transitions).unwrap());
        }
        let expected = PreparedTokenEffects::new(
            &ds,
            EffectOptions {
                partition_first_byte: false,
                cache_suffixes: false,
                ..Default::default()
            },
        )
        .unwrap()
        .analyze(&tokens)
        .unwrap();
        let actual = PreparedTokenEffects::new(
            &ds,
            EffectOptions {
                constant_stitch_digest: true,
                ..Default::default()
            },
        )
        .unwrap()
        .analyze(&tokens)
        .unwrap();
        assert_eq!(normalized(&expected), normalized(&actual));
        for (i, (_, v)) in tokens.iter().enumerate() {
            let u = &tokens[actual.representatives[actual.classes[i] as usize] as usize].1;
            for seq in [&[0usize][..], &[0, 1], &[1, 2, 0], &[2, 2]] {
                for (w, z) in [
                    (b"".as_slice(), b"".as_slice()),
                    (b"ab", b"ba"),
                    (b"a", b"b"),
                ] {
                    assert_eq!(
                        accepts_sequence(&ds, seq, &[w, v, z].concat()),
                        accepts_sequence(&ds, seq, &[w, u, z].concat())
                    );
                }
            }
        }
    }
}

#[test]
fn symbolic_byte_run_matches_materialized_small_bounds_without_clipping() {
    let tokens = vocab(b"abc", 4);
    for min in 1..=4 {
        for max in min..=8 {
            let ds = [terminal(&format!("[ab]{{{min},{max}}}"))];
            let materialized = PreparedTokenEffects::new(&ds, EffectOptions::default())
                .unwrap()
                .analyze(&tokens)
                .unwrap();
            let symbolic = SymbolicByteRun {
                alphabet: b"ab".to_vec(),
                min,
                max: Some(max),
            }
            .analyze(&tokens)
            .unwrap();
            assert_eq!(
                normalized(&materialized),
                normalized(&symbolic),
                "min={min},max={max}"
            );
        }
    }
}

#[test]
fn billion_run_bounds_are_symbolic_and_nullable_run_is_handled_explicitly() {
    let tokens = vec![
        (0, b"a".to_vec()),
        (1, b"b".to_vec()),
        (2, vec![b'a'; 128]),
        (3, vec![b'b'; 128]),
        (4, b"c".to_vec()),
    ];
    for min in [0, 1, 999_999_999] {
        let a = SymbolicByteRun {
            alphabet: b"ab".to_vec(),
            min,
            max: Some(1_000_000_000),
        }
        .analyze(&tokens)
        .unwrap();
        assert_eq!(a.classes, vec![0, 0, 1, 1, 2]);
        assert_eq!(a.stats.source_states, 0);
    }
    let empty = SymbolicByteRun {
        alphabet: b"ab".to_vec(),
        min: 0,
        max: Some(0),
    }
    .analyze(&tokens)
    .unwrap();
    assert_eq!(empty.classes, vec![0, 0, 0, 0, 0]);
    assert!(
        SymbolicByteRun {
            alphabet: b"ab".to_vec(),
            min: 2,
            max: Some(1)
        }
        .analyze(&tokens)
        .is_err()
    );
}
