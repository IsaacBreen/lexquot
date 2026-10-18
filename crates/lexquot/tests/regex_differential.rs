use lexquot::{
    AnalysisRequest, Backend, Lexer, Observation, Vocab, lexer_from_expressions,
    lexer_with_terminal_residuals, parse_regex,
};

#[test]
fn excluded_query_roots_remain_available_as_byte_continuations() {
    let lexer = lexer_with_terminal_residuals(
        vec![
            parse_regex("[ab]{1,4}", false),
            parse_regex("(a|bc)+", false),
        ],
        &[0, 1],
    )
    .unwrap();
    let vocabulary = Vocab::new(vec![(0, b"abcdabc".to_vec()), (57, b"abc".to_vec())]);
    let starts = (0..lexer.num_states())
        .filter(|q| q % 2 == 0)
        .collect::<Vec<_>>();
    let result = AnalysisRequest::new(&lexer, &vocabulary, Observation::L1)
        .initial_states(starts)
        .backend(Backend::Production)
        .verify(true)
        .analyze()
        .unwrap();
    assert_ne!(result.token_class(0), result.token_class(57));
    for q in (0..lexer.num_states()).filter(|q| q % 2 != 0) {
        assert_eq!(result.state_class(q), None);
    }
}

/// Exercise repetition, overlapping alternatives, nullable terminals, epsilon
/// unions, scoped roots and terminal-follow filters together. Seed is fixed.
#[test]
fn regex_and_epsilon_families_verify_against_structural_observations() {
    let patterns = [
        "a+",
        "[ab]{1,4}",
        "(ab|a)c?",
        "b*",
        "(a|bc)+",
        "a?b?",
        "[a-c]+",
        "ab|ac",
        "[bc]{2,5}",
        "a+b*",
    ];
    let mut seed = 599515_u64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        seed
    };
    for case in 0..60 {
        let count = 2 + (next() % 4) as usize;
        let expressions = (0..count)
            .map(|_| parse_regex(patterns[(next() % patterns.len() as u64) as usize], false))
            .collect::<Vec<_>>();
        let lexer = if case % 2 == 0 {
            lexer_from_expressions(expressions)
        } else {
            lexer_with_terminal_residuals(expressions, &(0..count as u32).collect::<Vec<_>>())
                .expect("small epsilon-union fixture")
        };
        let vocabulary = Vocab::new(
            (0..24)
                .map(|id| {
                    let length = 1 + (next() % 7) as usize;
                    (
                        id * 3,
                        (0..length).map(|_| b'a' + (next() % 4) as u8).collect(),
                    )
                })
                .collect(),
        );
        let roots = (0..lexer.num_states())
            .filter(|&q| case % 3 != 0 || q % 2 == 0)
            .collect::<Vec<_>>();
        for observation in [Observation::L1, Observation::L2P] {
            let mut request = AnalysisRequest::new(&lexer, &vocabulary, observation)
                .initial_states(roots.iter().copied())
                .backend(Backend::Production)
                .verify(true);
            if observation == Observation::L2P && case % 3 == 1 {
                request = request.forbidden_follows([(0, 1)]);
            }
            request
                .analyze()
                .unwrap_or_else(|error| panic!("case {case}, {observation:?}: {error}"));
        }
    }
}
