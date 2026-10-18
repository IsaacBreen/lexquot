use lexquot::{
    AnalysisError, Budget, ProjectedRoot, ResidualDfa, ResidualRequest, Vocab, verify_refinement,
};

fn chain(bytes: &[u8]) -> ResidualDfa {
    let mut rows = vec![Vec::new(); bytes.len() + 1];
    for (i, &b) in bytes.iter().enumerate() {
        rows[i].push((b, (i + 1) as u32));
    }
    ResidualDfa::new(rows).unwrap()
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

#[test]
fn all_residual_roots_survive_and_share_across_terminals() {
    let machines = vec![chain(b"ab"), chain(b"ab")];
    let roots = vec![
        ProjectedRoot {
            original_state: 0,
            terminal: 3,
            machine: 0,
            residual_state: 0,
        },
        ProjectedRoot {
            original_state: 1,
            terminal: 3,
            machine: 0,
            residual_state: 1,
        },
        ProjectedRoot {
            original_state: 2,
            terminal: 9,
            machine: 1,
            residual_state: 0,
        },
    ];
    let vocabulary = vocab(&[b"a", b"b", b"ab", b"z"]);
    let full = ResidualRequest::new(&machines, &roots, &vocabulary)
        .initial_states([0, 1, 2, 5])
        .analyze()
        .unwrap();
    let raw = ResidualRequest::new(&machines, &roots, &vocabulary)
        .initial_states([0, 1, 2, 5])
        .minimize(false)
        .analyze()
        .unwrap();
    assert_eq!(full.residual_stats.source_states, 6);
    assert_eq!(full.residual_stats.minimized_states, 3);
    assert!(full.analysis.state_class(5).is_some());
    assert_ne!(full.analysis.state_class(0), full.analysis.state_class(2));
    verify_refinement(
        &full.analysis.maps().vocab_tokens,
        &raw.analysis.maps().vocab_tokens,
        "token",
    )
    .unwrap();
    verify_refinement(
        &raw.analysis.maps().vocab_tokens,
        &full.analysis.maps().vocab_tokens,
        "token",
    )
    .unwrap();
    verify_refinement(
        &full.analysis.maps().tokenizer_states,
        &raw.analysis.maps().tokenizer_states,
        "state",
    )
    .unwrap();
}

#[test]
fn whole_token_state_equivalence_is_not_unbounded_dfa_equivalence() {
    let machines = vec![chain(&vec![b'a'; 100])];
    let roots = (0..101)
        .map(|state| ProjectedRoot {
            original_state: state,
            terminal: 0,
            machine: 0,
            residual_state: state,
        })
        .collect::<Vec<_>>();
    let vocabulary = vocab(&[b"a", b"aa", b"aaa"]);
    let result = ResidualRequest::new(&machines, &roots, &vocabulary)
        .analyze()
        .unwrap();
    assert_eq!(result.residual_stats.minimized_states, 101);
    assert_eq!(result.analysis.state_class_count(), 4);
}

#[test]
fn projection_can_preserve_multiple_residuals_for_one_terminal() {
    let machines = vec![chain(b"a"), chain(b"b")];
    let roots = vec![
        ProjectedRoot {
            original_state: 0,
            terminal: 0,
            machine: 0,
            residual_state: 0,
        },
        ProjectedRoot {
            original_state: 0,
            terminal: 0,
            machine: 1,
            residual_state: 0,
        },
    ];
    let vocabulary = vocab(&[b"a", b"b", b"z"]);
    let result = ResidualRequest::new(&machines, &roots, &vocabulary)
        .analyze()
        .unwrap();
    assert_eq!(
        result.analysis.token_class(0),
        result.analysis.token_class(1)
    );
    assert_ne!(
        result.analysis.token_class(0),
        result.analysis.token_class(2)
    );
}

#[test]
fn all_256_bytes_and_empty_queries_are_supported() {
    let machine = ResidualDfa::new(vec![(0..=255u8).map(|b| (b, 0)).collect()]).unwrap();
    let machines = [machine];
    let roots = [ProjectedRoot {
        original_state: 0,
        terminal: 0,
        machine: 0,
        residual_state: 0,
    }];
    let vocabulary = Vocab::new((0..=255u8).map(|b| (b as u32, vec![b])).collect());
    let result = ResidualRequest::new(&machines, &roots, &vocabulary)
        .analyze()
        .unwrap();
    assert_eq!(result.analysis.token_class_count(), 1);
    let empty = Vocab::new(Vec::new());
    let result = ResidualRequest::new(&machines, &roots, &empty)
        .analyze()
        .unwrap();
    assert_eq!(result.analysis.token_class_count(), 0);
    assert_eq!(result.analysis.state_class_count(), 1);
    let result = ResidualRequest::new(&[], &[], &vocabulary)
        .initial_states([0])
        .analyze()
        .unwrap();
    assert_eq!(result.analysis.token_class_count(), 1);
}

#[test]
fn malformed_and_budget_limited_residuals_are_rejected() {
    assert!(ResidualDfa::new(vec![vec![(b'a', 0), (b'a', 0)]]).is_err());
    assert!(ResidualDfa::new(vec![vec![(b'a', 1)]]).is_err());
    let machines = [chain(b"a")];
    let roots = [ProjectedRoot {
        original_state: 0,
        terminal: 0,
        machine: 0,
        residual_state: 5,
    }];
    let vocabulary = vocab(&[b"a"]);
    assert!(matches!(
        ResidualRequest::new(&machines, &roots, &vocabulary).analyze(),
        Err(AnalysisError::InvalidInput(_))
    ));
    let roots = [ProjectedRoot {
        original_state: 0,
        terminal: 0,
        machine: 0,
        residual_state: 0,
    }];
    let budget = Budget {
        max_byte_steps: 0,
        ..Budget::default()
    };
    assert!(matches!(
        ResidualRequest::new(&machines, &roots, &vocabulary)
            .budget(budget)
            .analyze(),
        Err(AnalysisError::BudgetExceeded { .. })
    ));
}

#[test]
fn random_residual_minimization_preserves_finite_token_observations() {
    let mut seed = 17u64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        seed
    };
    for case in 0..150 {
        let n = 1 + (next() % 15) as usize;
        let mut rows = vec![Vec::new(); n];
        for row in &mut rows {
            for byte in b'a'..=b'd' {
                if next() % 3 != 0 {
                    row.push((byte, (next() % n as u64) as u32));
                }
            }
        }
        let machines = [ResidualDfa::new(rows).unwrap()];
        let roots = (0..n as u32)
            .map(|s| ProjectedRoot {
                original_state: s,
                terminal: s % 3,
                machine: 0,
                residual_state: s,
            })
            .collect::<Vec<_>>();
        let vocabulary = Vocab::new(
            (0..30)
                .map(|id| {
                    let len = 1 + (next() % 8);
                    (id, (0..len).map(|_| b'a' + (next() % 5) as u8).collect())
                })
                .collect(),
        );
        let exact = ResidualRequest::new(&machines, &roots, &vocabulary)
            .analyze()
            .unwrap();
        let raw = ResidualRequest::new(&machines, &roots, &vocabulary)
            .minimize(false)
            .analyze()
            .unwrap();
        for (left, right) in [
            (&exact.analysis, &raw.analysis),
            (&raw.analysis, &exact.analysis),
        ] {
            verify_refinement(
                &left.maps().tokenizer_states,
                &right.maps().tokenizer_states,
                "state",
            )
            .unwrap_or_else(|e| panic!("case {case}: {e}"));
            verify_refinement(
                &left.maps().vocab_tokens,
                &right.maps().vocab_tokens,
                "token",
            )
            .unwrap_or_else(|e| panic!("case {case}: {e}"));
        }
    }
}

#[test]
fn product_trace_projection_matches_full_epsilon_lexer() {
    use lexquot::{
        AnalysisRequest, Backend, Observation, PreparedResiduals, lexer_with_terminal_residuals,
        parse_regex,
    };
    let expressions = vec![
        parse_regex("[a-z]+", false),
        parse_regex("[0-9]+", false),
        parse_regex("ab", false),
    ];
    for groups in [vec![0, 1, 2], vec![0, 0, 1]] {
        let lexer = lexer_with_terminal_residuals(expressions.clone(), &groups).unwrap();
        let prepared = PreparedResiduals::from_lexer(&lexer).unwrap();
        let vocabulary = vocab(&[b"a", b"ab", b"123", b"a1", b"x", b"z"]);
        let reference = AnalysisRequest::new(&lexer, &vocabulary, Observation::L1)
            .backend(Backend::Canonical)
            .analyze()
            .unwrap();
        let direct = prepared.request(&vocabulary).analyze().unwrap().analysis;
        verify_refinement(
            &direct.maps().tokenizer_states,
            &reference.maps().tokenizer_states,
            "state",
        )
        .unwrap();
        verify_refinement(
            &reference.maps().tokenizer_states,
            &direct.maps().tokenizer_states,
            "state",
        )
        .unwrap();
        verify_refinement(
            &direct.maps().vocab_tokens,
            &reference.maps().vocab_tokens,
            "token",
        )
        .unwrap();
        verify_refinement(
            &reference.maps().vocab_tokens,
            &direct.maps().vocab_tokens,
            "token",
        )
        .unwrap();
    }
}
