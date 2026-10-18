use lexquot::{
    Analysis, AnalysisError, AnalysisRequest, Assurance, Backend, Budget, Expr, Lexer, Observation,
    Tokenizer, Vocab, lexer_from_expressions, refine_token_partitions, verify_refinement,
};

fn literals(patterns: &[&[u8]]) -> Tokenizer {
    lexer_from_expressions(patterns.iter().map(|p| Expr::U8Seq(p.to_vec())).collect())
}
fn vocab(tokens: &[&[u8]]) -> Vocab {
    Vocab::new(
        tokens
            .iter()
            .enumerate()
            .map(|(i, b)| (i as u32, b.to_vec()))
            .collect(),
    )
}
fn exact(lexer: &Tokenizer, vocabulary: &Vocab, observation: Observation) -> Analysis {
    AnalysisRequest::new(lexer, vocabulary, observation)
        .backend(Backend::Canonical)
        .analyze()
        .unwrap()
}
fn equal_partition(a: &Analysis, b: &Analysis) {
    for &x in &a.domain().token_ids {
        for &y in &a.domain().token_ids {
            assert_eq!(
                a.token_class(x) == a.token_class(y),
                b.token_class(x) == b.token_class(y),
                "tokens {x},{y}"
            );
        }
    }
}

#[test]
fn duplicates_and_sparse_ids_are_retained() {
    let lexer = literals(&[b"ab", b"ac"]);
    let vocabulary = Vocab::new(vec![
        (2, b"a".to_vec()),
        (17, b"a".to_vec()),
        (100, b"z".to_vec()),
    ]);
    for observation in [Observation::L1, Observation::L2P] {
        let result = exact(&lexer, &vocabulary, observation);
        assert_eq!(result.token_class(2), result.token_class(17));
        assert_eq!(result.token_class(3), None);
        assert!(result.token_class(100).is_some());
        assert_eq!(
            result
                .maps()
                .vocab_tokens
                .internal_to_originals
                .iter()
                .map(Vec::len)
                .sum::<usize>(),
            3
        );
    }
}

#[test]
fn l1_and_l2p_are_different_observations() {
    let lexer = literals(&[b"a", b"b"]);
    let vocabulary = vocab(&[b"ab", b"ba", b"zz"]);
    let l1 = exact(&lexer, &vocabulary, Observation::L1);
    let l2 = exact(&lexer, &vocabulary, Observation::L2P);
    assert_eq!(l1.token_class(0), l1.token_class(1));
    assert_ne!(l2.token_class(0), l2.token_class(1));
    assert_ne!(l2.token_class(0), l2.token_class(2));
}

#[test]
fn excluding_reset_from_initial_domain_keeps_reset_suffixes() {
    let lexer = literals(&[b"ab", b"c"]);
    let after_a = lexer.get_transition(lexer.initial_state_id(), b'a');
    let vocabulary = vocab(&[b"bc", b"bx", b"b"]);
    let result = AnalysisRequest::new(&lexer, &vocabulary, Observation::L2P)
        .initial_states([after_a])
        .analyze()
        .unwrap();
    assert_eq!(result.state_class(lexer.initial_state_id()), None);
    assert_ne!(result.token_class(0), result.token_class(1));
    assert!(result.stats().reset_suffix_scans > 0);
}

#[test]
fn missing_scope_is_not_the_dead_class() {
    let lexer = literals(&[b"ab"]);
    let vocabulary = vocab(&[b"z", b"q"]);
    let root = lexer.initial_state_id();
    let result = AnalysisRequest::new(&lexer, &vocabulary, Observation::L1)
        .initial_states([root])
        .analyze()
        .unwrap();
    assert!(result.state_class(root).is_some());
    let other = (0..lexer.num_states()).find(|&s| s != root).unwrap();
    assert_eq!(result.state_class(other), None);
    assert!(result.token_class(0).is_some());
}

#[test]
fn future_observations_are_not_recomputed_from_partition_alphabet() {
    let lexer = literals(&[b"acx", b"bcy"]);
    let root = lexer.initial_state_id();
    let a = lexer.get_transition(root, b'a');
    let b = lexer.get_transition(root, b'b');
    let vocabulary = vocab(&[b"c"]);
    let result = AnalysisRequest::new(&lexer, &vocabulary, Observation::L1)
        .initial_states([a, b])
        .backend(Backend::Canonical)
        .analyze()
        .unwrap();
    assert_ne!(result.state_class(a), result.state_class(b));
}

#[test]
fn terminal_local_projection_does_not_merge_terminal_identities() {
    let lexer = literals(&[b"a", b"b"]);
    let vocabulary = vocab(&[b"a", b"b", b"x"]);
    let all = exact(&lexer, &vocabulary, Observation::L1);
    let a = AnalysisRequest::new(&lexer, &vocabulary, Observation::L1)
        .terminals([0])
        .analyze()
        .unwrap();
    let b = AnalysisRequest::new(&lexer, &vocabulary, Observation::L1)
        .terminals([1])
        .analyze()
        .unwrap();
    let joined = refine_token_partitions(&[0, 1, 2], &[a, b]).unwrap();
    verify_refinement(&joined, &all.maps().vocab_tokens, "token").unwrap();
    verify_refinement(&all.maps().vocab_tokens, &joined, "token").unwrap();
}

#[test]
fn follow_restrictions_are_observed_and_typed_as_terminals() {
    let lexer = literals(&[b"a", b"b", b"c"]);
    let vocabulary = vocab(&[b"ab", b"ac", b"ax"]);
    let unrestricted = exact(&lexer, &vocabulary, Observation::L2P);
    let restricted = AnalysisRequest::new(&lexer, &vocabulary, Observation::L2P)
        .forbidden_follows([(0, 1), (0, 2)])
        .analyze()
        .unwrap();
    assert_ne!(unrestricted.token_class(0), unrestricted.token_class(1));
    assert_eq!(restricted.token_class(0), restricted.token_class(1));
    assert!(matches!(
        AnalysisRequest::new(&lexer, &vocabulary, Observation::L1)
            .forbidden_follows([(0, 1)])
            .analyze(),
        Err(AnalysisError::InvalidInput(_))
    ));
}

#[test]
fn empty_domain_is_a_valid_vacuous_quotient() {
    let lexer = literals(&[b"ab"]);
    let vocabulary = vocab(&[b"a", b"b", b"q"]);
    let result = AnalysisRequest::new(&lexer, &vocabulary, Observation::L2P)
        .initial_states([])
        .analyze()
        .unwrap();
    assert_eq!(result.state_class_count(), 0);
    assert_eq!(result.token_class_count(), 1);
    let empty = Vocab::new(Vec::new());
    let result = exact(&lexer, &empty, Observation::L2P);
    assert_eq!(result.token_class_count(), 0);
    assert_eq!(result.state_class_count(), 1);
}

#[test]
fn budgets_and_invalid_inputs_fail_closed() {
    let lexer = literals(&[b"ab"]);
    let vocabulary = vocab(&[b"a", b"b"]);
    let budget = Budget {
        max_table_cells: 0,
        ..Budget::default()
    };
    assert!(matches!(
        AnalysisRequest::new(&lexer, &vocabulary, Observation::L2P)
            .budget(budget)
            .analyze(),
        Err(AnalysisError::BudgetExceeded { .. })
    ));
    assert!(matches!(
        AnalysisRequest::new(&lexer, &vocabulary, Observation::L1)
            .initial_states([u32::MAX])
            .analyze(),
        Err(AnalysisError::InvalidInput(_))
    ));
    let empty = vocab(&[b""]);
    assert!(matches!(
        AnalysisRequest::new(&lexer, &empty, Observation::L1).analyze(),
        Err(AnalysisError::InvalidInput(_))
    ));
    let huge = Vocab::new(vec![(u32::MAX, b"a".to_vec())]);
    assert!(matches!(
        AnalysisRequest::new(&lexer, &huge, Observation::L1).analyze(),
        Err(AnalysisError::BudgetExceeded { .. })
    ));
}

#[test]
fn special_tokens_do_not_become_empty_byte_tokens() {
    let lexer = literals(&[b"a"]);
    let vocabulary = Vocab::new_with_exact_token_ids(vec![(0, b"a".to_vec())], [50]);
    let result = exact(&lexer, &vocabulary, Observation::L1);
    assert_eq!(result.token_class(50), None);
    assert_eq!(result.domain().token_ids, vec![0]);
}

#[test]
fn canonical_suffix_algorithm_is_iterative_for_long_tokens() {
    let lexer = literals(&[b"a"]);
    let vocabulary = Vocab::new(vec![(0, vec![b'a'; 512]), (1, vec![b'a'; 513])]);
    let result = exact(&lexer, &vocabulary, Observation::L2P);
    assert_ne!(result.token_class(0), result.token_class(1));
    assert!(result.stats().canonical_nodes >= 512);
}

#[test]
fn production_modes_report_their_actual_assurance() {
    let lexer = literals(&[b"a", b"b"]);
    let vocabulary = vocab(&[b"ab", b"ba", b"z"]);
    let p = AnalysisRequest::new(&lexer, &vocabulary, Observation::L2P)
        .backend(Backend::Production)
        .analyze()
        .unwrap();
    assert_eq!(p.assurance(), Assurance::FingerprintAssisted);
    let p = AnalysisRequest::new(&lexer, &vocabulary, Observation::L2P)
        .backend(Backend::Production)
        .verify(true)
        .analyze()
        .unwrap();
    assert_eq!(p.assurance(), Assurance::CanonicallyVerified);
}

#[test]
fn generated_literal_lexers_agree_with_production_partitions() {
    let mut seed = 7u64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        seed
    };
    for case in 0..120 {
        let mut patterns = Vec::new();
        for _ in 0..(1 + next() % 5) {
            let len = 1 + (next() % 5) as usize;
            patterns.push(
                (0..len)
                    .map(|_| b'a' + (next() % 3) as u8)
                    .collect::<Vec<_>>(),
            );
        }
        let lexer = lexer_from_expressions(patterns.into_iter().map(Expr::U8Seq).collect());
        let mut entries = Vec::new();
        for id in 0..20 {
            let len = 1 + (next() % 6) as usize;
            entries.push((
                id,
                (0..len)
                    .map(|_| b'a' + (next() % 4) as u8)
                    .collect::<Vec<_>>(),
            ));
        }
        let vocabulary = Vocab::new(entries);
        for observation in [Observation::L1, Observation::L2P] {
            let reference = exact(&lexer, &vocabulary, observation);
            let result = AnalysisRequest::new(&lexer, &vocabulary, observation)
                .backend(Backend::Production)
                .verify(true)
                .analyze()
                .unwrap_or_else(|e| panic!("case {case}, {observation:?}: {e}"));
            // Production is permitted to retain additional state or token
            // distinctions; it must not introduce a merge absent in the oracle.
            verify_refinement(
                &result.maps().vocab_tokens,
                &reference.maps().vocab_tokens,
                "token",
            )
            .unwrap();
            if observation == Observation::L1 {
                equal_partition(&result, &reference);
            }
        }
    }
}

#[test]
fn reference_verifier_rejects_an_incorrect_merge() {
    let lexer = literals(&[b"a", b"b"]);
    let vocabulary = vocab(&[b"a", b"b"]);
    let result = exact(&lexer, &vocabulary, Observation::L1);
    let mut bad = result.maps().vocab_tokens.clone();
    bad.internal_to_originals = vec![vec![0, 1]];
    assert!(matches!(
        verify_refinement(&bad, &result.maps().vocab_tokens, "token"),
        Err(AnalysisError::UnsoundMerge { .. })
    ));
}
