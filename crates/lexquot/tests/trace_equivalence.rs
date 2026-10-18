//! Independent forward enumeration of all lexical decompositions. This oracle
//! does not use reverse columns, structural-language interning, or product
//! recurrence, so shared implementation mistakes are not hidden by agreement.
use lexquot::trace::{
    EndpointPolicy, PrepareOptions, PreparedTrace, TraceAlgorithm, TraceAnalysis, TraceBudget,
    TraceDfa,
};
use lexquot::{Vocab, parse_regex};
use std::collections::{BTreeSet, HashMap};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Ending {
    Boundary,
    Pending(u32, u32),
}
type Word = (Vec<u32>, Ending);
type Language = BTreeSet<Word>;

fn endpoint(p: &PreparedTrace, state: u32, policy: EndpointPolicy) -> u32 {
    if !p.can_continue(state).unwrap() {
        0
    } else if policy == EndpointPolicy::Mask {
        1
    } else {
        p.endpoint_class(state).unwrap() + 1
    }
}

fn reset(p: &PreparedTrace, bytes: &[u8], policy: EndpointPolicy) -> Language {
    if bytes.is_empty() {
        return BTreeSet::from([(Vec::new(), Ending::Boundary)]);
    }
    let mut result = BTreeSet::new();
    for (terminal, &root) in p.terminal_roots().iter().enumerate() {
        let mut state = root;
        for (i, &b) in bytes.iter().enumerate() {
            state = p.transition(state, b).unwrap();
            if state == 0 {
                break;
            }
            if p.is_accepting(state).unwrap() {
                for (mut word, end) in reset(p, &bytes[i + 1..], policy) {
                    word.insert(0, terminal as u32);
                    result.insert((word, end));
                }
            }
            if i + 1 == bytes.len() {
                let residual = endpoint(p, state, policy);
                if residual != 0 {
                    result.insert((Vec::new(), Ending::Pending(terminal as u32, residual)));
                }
            }
        }
    }
    result
}

fn oracle(p: &PreparedTrace, bytes: &[u8], policy: EndpointPolicy) -> Vec<(u32, Language)> {
    (1..p.state_count() as u32)
        .map(|initial| {
            let mut state = initial;
            let mut completed = BTreeSet::new();
            if p.is_accepting(state).unwrap() {
                completed.extend(reset(p, bytes, policy));
            }
            for (i, &b) in bytes.iter().enumerate() {
                state = p.transition(state, b).unwrap();
                if state == 0 {
                    break;
                }
                if p.is_accepting(state).unwrap() {
                    completed.extend(reset(p, &bytes[i + 1..], policy));
                }
            }
            (endpoint(p, state, policy), completed)
        })
        .collect()
}

fn words(alphabet: &[u8], max_len: usize) -> Vec<Vec<u8>> {
    let mut all = Vec::new();
    let mut level = vec![Vec::new()];
    for _ in 0..max_len {
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
        all.extend(level.iter().cloned());
    }
    all
}

fn same_partition(a: &[u32], b: &[u32]) {
    assert_eq!(a.len(), b.len());
    let (mut ab, mut ba) = (HashMap::new(), HashMap::new());
    for (&x, &y) in a.iter().zip(b) {
        assert_eq!(
            *ab.entry(x).or_insert(y),
            y,
            "left partition merged a distinction"
        );
        assert_eq!(
            *ba.entry(y).or_insert(x),
            x,
            "right partition merged a distinction"
        );
    }
}

fn oracle_classes(p: &PreparedTrace, tokens: &[Vec<u8>], policy: EndpointPolicy) -> Vec<u32> {
    let mut ids = HashMap::new();
    tokens
        .iter()
        .map(|token| {
            let key = oracle(p, token, policy);
            let next = ids.len() as u32;
            *ids.entry(key).or_insert(next)
        })
        .collect()
}

fn analyze(
    p: &PreparedTrace,
    tokens: &[Vec<u8>],
    policy: EndpointPolicy,
    algorithm: TraceAlgorithm,
) -> TraceAnalysis {
    let vocabulary = Vocab::new(
        tokens
            .iter()
            .enumerate()
            .map(|(id, b)| (id as u32, b.clone()))
            .collect(),
    );
    p.request(&vocabulary)
        .endpoint(policy)
        .algorithm(algorithm)
        .analyze()
        .unwrap()
}

#[test]
fn exhaustive_ambiguous_completion_positions_match_forward_oracle() {
    let terminals = ["a+", "aa", "b+", "ab", "(a|b)a"]
        .map(|r| TraceDfa::from_expression(&parse_regex(r, false)).unwrap());
    let p = PreparedTrace::new(&terminals, PrepareOptions::default()).unwrap();
    let tokens = words(b"ab", 5);
    for policy in [EndpointPolicy::Mask, EndpointPolicy::Residual] {
        let expected = oracle_classes(&p, &tokens, policy);
        let projected = analyze(&p, &tokens, policy, TraceAlgorithm::Projected);
        let product = analyze(&p, &tokens, policy, TraceAlgorithm::Product);
        same_partition(&expected, &projected.token_classes);
        same_partition(&expected, &product.token_classes);
        assert!(!projected.stats.state_quotient_computed);
        assert_eq!(projected.stats.product_states, 0);
    }
}

fn rand(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

#[test]
fn random_automata_and_representation_ablations_preserve_exact_partitions() {
    let tokens = words(b"ab", 4);
    let vocabulary = Vocab::new(
        tokens
            .iter()
            .enumerate()
            .map(|(id, b)| (id as u32, b.clone()))
            .collect(),
    );
    for seed in 1..=48u64 {
        let mut random = seed * 7829;
        let terminals = (0..(1 + seed as usize % 3))
            .map(|_| {
                let n = 2 + rand(&mut random) as usize % 5;
                let mut finals = vec![false; n];
                finals[n - 1] = true;
                for f in &mut finals[1..n - 1] {
                    *f = rand(&mut random) % 3 == 0;
                }
                let rows = (0..n)
                    .map(|s| {
                        let mut row = Vec::new();
                        if s + 1 < n {
                            row.push((b'a', s as u32 + 1));
                        } else if rand(&mut random) % 2 == 0 {
                            row.push((b'a', rand(&mut random) as u32 % n as u32));
                        }
                        if rand(&mut random) % 3 != 0 {
                            row.push((b'b', rand(&mut random) as u32 % n as u32));
                        }
                        row
                    })
                    .collect();
                TraceDfa::new(0, finals, rows).unwrap()
            })
            .collect::<Vec<_>>();
        let p = PreparedTrace::new(&terminals, PrepareOptions::default()).unwrap();
        for policy in [EndpointPolicy::Mask, EndpointPolicy::Residual] {
            let expected = oracle_classes(&p, &tokens, policy);
            same_partition(
                &expected,
                &analyze(&p, &tokens, policy, TraceAlgorithm::Projected).token_classes,
            );
            same_partition(
                &expected,
                &analyze(&p, &tokens, policy, TraceAlgorithm::Product).token_classes,
            );
            let uncached = p
                .request(&vocabulary)
                .endpoint(policy)
                .cache_transitions(false)
                .byte_classes(false)
                .analyze()
                .unwrap();
            same_partition(&expected, &uncached.token_classes);
            for (minimize, share) in [(false, false), (true, false)] {
                let q = PreparedTrace::new(
                    &terminals,
                    PrepareOptions {
                        minimize,
                        share_across_terminals: share,
                        ..PrepareOptions::default()
                    },
                )
                .unwrap();
                same_partition(
                    &expected,
                    &analyze(&q, &tokens, policy, TraceAlgorithm::Projected).token_classes,
                );
            }
        }
    }
}

#[test]
fn endpoint_policy_distinguishes_mask_viability_from_right_contexts() {
    // Both 'a' and 'b' are live prefixes of this terminal, but only one can be
    // followed by 'x'. A mask-only observer must not imply substitution safety.
    let dfa = TraceDfa::from_expression(&parse_regex("ax|by", false)).unwrap();
    let p = PreparedTrace::new(&[dfa], PrepareOptions::default()).unwrap();
    let tokens = vec![b"a".to_vec(), b"b".to_vec()];
    let mask = analyze(&p, &tokens, EndpointPolicy::Mask, TraceAlgorithm::Projected);
    let strong = analyze(
        &p,
        &tokens,
        EndpointPolicy::Residual,
        TraceAlgorithm::Projected,
    );
    assert_eq!(mask.token_classes[0], mask.token_classes[1]);
    assert_ne!(strong.token_classes[0], strong.token_classes[1]);
}

#[test]
fn accepting_initial_residual_can_finish_before_the_first_byte() {
    let terminals = ["a", "b"].map(|r| TraceDfa::from_expression(&parse_regex(r, false)).unwrap());
    let p = PreparedTrace::new(&terminals, PrepareOptions::default()).unwrap();
    let accepting = (1..p.state_count() as u32)
        .find(|&s| p.is_accepting(s).unwrap())
        .unwrap();
    let observations = oracle(&p, b"b", EndpointPolicy::Residual);
    let (_, completed) = &observations[accepting as usize - 1];
    assert!(completed.contains(&(vec![1], Ending::Boundary)));
    let tokens = words(b"abc", 3);
    same_partition(
        &oracle_classes(&p, &tokens, EndpointPolicy::Residual),
        &analyze(
            &p,
            &tokens,
            EndpointPolicy::Residual,
            TraceAlgorithm::Projected,
        )
        .token_classes,
    );
}

#[test]
fn disconnected_live_roots_are_preserved_and_product_scope_change_is_rejected() {
    let dfa = TraceDfa::new(
        0,
        vec![false, true, false, true],
        vec![vec![(b'a', 1)], vec![], vec![(b'b', 3)], vec![]],
    )
    .unwrap();
    let p = PreparedTrace::new(&[dfa], PrepareOptions::default()).unwrap();
    let vocab = Vocab::new(vec![(1, b"a".to_vec()), (2, b"b".to_vec())]);
    let projected = p.request(&vocab).analyze().unwrap();
    assert_ne!(projected.token_class(1), projected.token_class(2));
    assert!(
        p.request(&vocab)
            .algorithm(TraceAlgorithm::Product)
            .analyze()
            .is_err()
    );
}

#[test]
fn sparse_ids_duplicates_dead_class_and_shortest_representative_are_exact() {
    let dfa = TraceDfa::from_expression(&parse_regex("a+", false)).unwrap();
    let p = PreparedTrace::new(&[dfa], PrepareOptions::default()).unwrap();
    let vocab = Vocab::new(vec![
        (u32::MAX - 1, b"a".to_vec()),
        (20, b"aaa".to_vec()),
        (80, b"a".to_vec()),
        (23, b"z".to_vec()),
        (29, b"zz".to_vec()),
    ]);
    let a = p
        .request(&vocab)
        .endpoint(EndpointPolicy::Mask)
        .analyze()
        .unwrap();
    assert_eq!(a.token_class(80), a.token_class(u32::MAX - 1));
    assert_eq!(a.token_class(23), a.dead_class);
    assert_eq!(a.token_class(29), a.dead_class);
    assert_eq!(a.token_class(999), None);
    assert_eq!(a.representatives[a.token_class(80).unwrap() as usize], 80);
    assert_eq!(a.token_ids.len(), 5);
}

#[test]
fn all_bytes_empty_domain_and_typed_budget_errors() {
    let dfa = TraceDfa::new(
        0,
        vec![false, true],
        vec![(0..=255).map(|b| (b, 1)).collect(), vec![]],
    )
    .unwrap();
    let p = PreparedTrace::new(&[dfa], PrepareOptions::default()).unwrap();
    let tokens = (0..=255).map(|b| vec![b]).collect::<Vec<_>>();
    assert_eq!(
        analyze(
            &p,
            &tokens,
            EndpointPolicy::Residual,
            TraceAlgorithm::Projected
        )
        .classes
        .len(),
        1
    );
    let empty = Vocab::new(Vec::<(u32, Vec<u8>)>::new());
    assert!(p.request(&empty).analyze().unwrap().classes.is_empty());
    let invalid = Vocab::new(vec![(0, Vec::new())]);
    assert!(p.request(&invalid).analyze().is_err());
    let v = Vocab::new(vec![(0, b"a".to_vec())]);
    let small = TraceBudget {
        max_reverse_columns: 0,
        ..TraceBudget::default()
    };
    assert!(p.request(&v).budget(small).analyze().is_err());
    assert!(TraceDfa::new(0, vec![true], vec![vec![]]).is_err());
    assert!(TraceDfa::new(0, vec![false], vec![vec![]]).is_err());
    assert!(TraceDfa::new(0, vec![false, true], vec![vec![(1, 1), (1, 1)], vec![]]).is_err());
}

#[test]
fn finite_horizon_does_not_justify_truncating_the_original_terminal() {
    // Truncating a{1,10} to a{1,2} because tokens have at most two bytes loses
    // valid right-context behavior from the original halfway residual.
    let long = TraceDfa::from_expression(&parse_regex("a{1,10}", false)).unwrap();
    let short = TraceDfa::from_expression(&parse_regex("a{1,2}", false)).unwrap();
    let long = PreparedTrace::new(&[long], PrepareOptions::default()).unwrap();
    let short = PreparedTrace::new(&[short], PrepareOptions::default()).unwrap();
    let advance = |p: &PreparedTrace, bytes: &[u8]| {
        bytes
            .iter()
            .fold(p.terminal_roots()[0], |s, &b| p.transition(s, b).unwrap())
    };
    assert_ne!(advance(&long, b"aaa"), 0);
    assert_eq!(advance(&short, b"aaa"), 0);
}
