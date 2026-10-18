use lexquot::{
    AnalysisError, AnalysisRequest, Backend, Budget, Expr, Observation, Vocab,
    lexer_from_expressions, verify_refinement,
};

#[test]
fn verifier_rejects_inconsistent_coordinates_and_omitted_members() {
    let lexer =
        lexer_from_expressions(vec![Expr::U8Seq(b"a".to_vec()), Expr::U8Seq(b"b".to_vec())]);
    let vocab = Vocab::new(vec![(0, b"a".to_vec()), (1, b"b".to_vec())]);
    let result = AnalysisRequest::new(&lexer, &vocab, Observation::L1)
        .backend(Backend::Canonical)
        .analyze()
        .unwrap();
    let reference = &result.maps().vocab_tokens;
    let mut bad = reference.clone();
    bad.original_to_internal[1] = bad.original_to_internal[0];
    assert!(matches!(
        verify_refinement(&bad, reference, "token"),
        Err(AnalysisError::InvalidInput(_))
    ));
    let mut bad = reference.clone();
    bad.internal_to_originals.clear();
    bad.representative_original_ids.clear();
    assert!(matches!(
        verify_refinement(&bad, reference, "token"),
        Err(AnalysisError::InvalidInput(_))
    ));
    let mut groups = reference.clone();
    groups.original_to_internal.clear();
    verify_refinement(&groups, reference, "token").unwrap();
}

#[test]
fn legacy_transition_table_is_bounded_before_allocation() {
    let lexer = lexer_from_expressions(vec![Expr::U8Seq(b"abc".to_vec())]);
    let vocab = Vocab::new(vec![(0, b"a".to_vec())]);
    for observation in [Observation::L1, Observation::L2P] {
        let request = AnalysisRequest::new(&lexer, &vocab, observation)
            .backend(Backend::Production)
            .budget(Budget {
                max_table_cells: 1,
                ..Budget::default()
            });
        assert!(matches!(
            request.analyze(),
            Err(AnalysisError::BudgetExceeded {
                resource: "production flat transition cells",
                ..
            })
        ));
    }
}
