use lexquot::{
    AnalysisError, AnalysisRequest, Backend, Expr, Observation, PartitionSpec, PartitionedRequest,
    Vocab, lexer_from_expressions, verify_refinement,
};

#[test]
fn disjoint_vocabulary_families_keep_local_state_maps() {
    let lexer =
        lexer_from_expressions(vec![Expr::U8Seq(b"a".to_vec()), Expr::U8Seq(b"b".to_vec())]);
    let vocab = Vocab::new(vec![
        (0, b"a".to_vec()),
        (1, b"b".to_vec()),
        (2, b"ab".to_vec()),
        (3, b"ba".to_vec()),
    ]);
    let result = PartitionedRequest::new(&lexer, &vocab)
        .partition(PartitionSpec::new("single", Observation::L1, [0, 1]))
        .partition(PartitionSpec::new("crossing", Observation::L2P, [2, 3]))
        .analyze()
        .unwrap();
    assert_eq!(result.parts().len(), 2);
    assert_eq!(result.parts()[0].token_class(2), None);
    assert_eq!(result.parts()[1].token_class(0), None);
    assert_ne!(
        result.token_map().original_to_internal[2],
        result.token_map().original_to_internal[3]
    );
}

#[test]
fn overlapping_terminal_projections_refine_to_the_full_l1_relation() {
    let lexer =
        lexer_from_expressions(vec![Expr::U8Seq(b"a".to_vec()), Expr::U8Seq(b"b".to_vec())]);
    let vocab = Vocab::new(vec![
        (0, b"a".to_vec()),
        (1, b"b".to_vec()),
        (2, b"z".to_vec()),
    ]);
    let reference = AnalysisRequest::new(&lexer, &vocab, Observation::L1)
        .backend(Backend::Canonical)
        .analyze()
        .unwrap();
    let result = PartitionedRequest::new(&lexer, &vocab)
        .partition(PartitionSpec::new("terminal-a", Observation::L1, [0, 1, 2]).terminals([0]))
        .partition(PartitionSpec::new("terminal-b", Observation::L1, [0, 1, 2]).terminals([1]))
        .verify(true)
        .analyze()
        .unwrap();
    verify_refinement(result.token_map(), &reference.maps().vocab_tokens, "token").unwrap();
    verify_refinement(&reference.maps().vocab_tokens, result.token_map(), "token").unwrap();
}

#[test]
fn uncovered_ids_unknown_ids_and_duplicate_names_are_rejected() {
    let lexer = lexer_from_expressions(vec![Expr::U8Seq(b"a".to_vec())]);
    let vocab = Vocab::new(vec![(0, b"a".to_vec()), (1, b"x".to_vec())]);
    for specs in [
        vec![PartitionSpec::new("a", Observation::L1, [0])],
        vec![PartitionSpec::new("a", Observation::L1, [0, 1, 2])],
        vec![
            PartitionSpec::new("a", Observation::L1, [0]),
            PartitionSpec::new("a", Observation::L1, [1]),
        ],
    ] {
        let mut request = PartitionedRequest::new(&lexer, &vocab);
        for spec in specs {
            request = request.partition(spec);
        }
        assert!(matches!(
            request.analyze(),
            Err(AnalysisError::InvalidInput(_))
        ));
    }
}

#[test]
fn sparse_control_ids_cannot_trigger_a_legacy_dense_allocation() {
    let lexer = lexer_from_expressions(vec![Expr::U8Seq(b"a".to_vec())]);
    let vocab = Vocab::new_with_exact_token_ids(vec![(0, b"a".to_vec())], [u32::MAX]);
    // Exact-only control IDs do not enlarge Vocab's ordinary byte coordinate.
    let fast = AnalysisRequest::new(&lexer, &vocab, Observation::L1)
        .analyze()
        .unwrap();
    let reference = AnalysisRequest::new(&lexer, &vocab, Observation::L1)
        .backend(Backend::Canonical)
        .analyze()
        .unwrap();
    assert_eq!(fast.token_class(u32::MAX), None);
    assert_eq!(reference.token_class(u32::MAX), None);
    assert!(fast.maps().vocab_tokens.original_to_internal.len() <= 1);
    let sparse_bytes = Vocab::new(vec![(u32::MAX, b"a".to_vec())]);
    for backend in [Backend::Auto, Backend::Canonical, Backend::Production] {
        assert!(matches!(
            AnalysisRequest::new(&lexer, &sparse_bytes, Observation::L1)
                .backend(backend)
                .analyze(),
            Err(AnalysisError::BudgetExceeded { .. })
        ));
    }
}
