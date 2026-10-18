# lexquot

Scoped model-token and lexer-state equivalence for constrained-decoding compilation.

This crate contains the projected single-terminal **L1** and multi-terminal **L2P** analysis implementations extracted from GLRMask. It also provides a checked public API, a collision-free structural reference backend, and a direct terminal-residual interface that does not require building a combined lexer.

It does **not** contain a parser, a Terminal DWA compiler, or a runtime mask engine. GLRMask uses the library through adapters and constructs its weighted automata separately.

## Status

This is a tested research release candidate, not a published crates.io release. The manuscript and raw research measurements are maintained in a separate private repository during author review. This public workspace includes four local supporting crates. crates.io publication requires a separate release decision.

For the separate stronger, all-completion vocabulary interface, see the
[trace guide](TRACE_GUIDE.md). Its substitution guarantee must not be inferred
for the historical L1/L2P modes described below.

## The three distinctions that matter

**Vocabulary partitioning is not equivalence.** Restricting the token domain can collapse initial-state rows, but does not on its own change equality of two retained token columns on the same state/terminal observation domain. Extra token merging requires a restricted observation, such as a selected terminal family or initial-state set.

**L1 and L2P answer different questions.** L1 observes terminals that remain live after the complete token without resetting inside it. L2P observes terminal completions, reset suffixes, pending terminal possibilities, and follow restrictions. A token crossing a terminal boundary cannot be routed through L1 merely because it is short. The host must establish which relation its consumer needs.

**An initial-state quotient is not a runtime lexer quotient.** A state class can be valid only at a whole-token boundary, for a finite vocabulary and selected observations. Do not apply it to arbitrary intermediate byte transitions. Likewise, token classes here are not a promise that replacing token bytes during commit preserves an arbitrary grammar language.

## Basic use

```rust
use lexquot::{
    AnalysisRequest, Expr, Observation, Vocab,
    lexer_from_expressions,
};

let lexer = lexer_from_expressions(vec![
    Expr::U8Seq(b"a".to_vec()),
    Expr::U8Seq(b"b".to_vec()),
]);
let vocab = Vocab::new(vec![
    (10, b"ab".to_vec()),
    (20, b"ba".to_vec()),
]);
let result = AnalysisRequest::new(&lexer, &vocab, Observation::L2P)
    .analyze()?;

assert_ne!(result.token_class(10), result.token_class(20));
assert_eq!(result.token_class(99), None); // outside this domain, not dead
# Ok::<(), lexquot::AnalysisError>(())
```

`Analysis` exposes read-only domain, maps, assurance, and statistics. Sparse original token IDs and duplicate byte spellings are preserved. Special/control tokens without ordinary byte spellings remain outside the analysis; they are not introduced as empty tokens.

## Direct projected residuals

A `ResidualDfa` is a deterministic **live-prefix** machine. Every explicit state is live/accepting; a missing transition goes to the implicit dead sink. The terminal identity belongs to `ProjectedRoot`, not to the internal residual state. This permits sharing equal residual structure across terminals without making the grammar terminals interchangeable.

```rust
use lexquot::{
    ProjectedRoot, ResidualDfa, ResidualRequest, Vocab,
};

let machines = [ResidualDfa::new(vec![
    vec![(b'a', 1)],
    vec![(b'b', 2)],
    vec![],
])?];
let roots = [
    ProjectedRoot {
        original_state: 4, terminal: 0,
        machine: 0, residual_state: 0,
    },
    ProjectedRoot {
        original_state: 9, terminal: 0,
        machine: 0, residual_state: 1,
    },
];
let vocab = Vocab::new(vec![(0, b"a".to_vec()), (1, b"b".to_vec())]);
let result = ResidualRequest::new(&machines, &roots, &vocab).analyze()?;
assert_ne!(result.analysis.state_class(4), result.analysis.state_class(9));
# Ok::<(), lexquot::AnalysisError>(())
```

Multiple memberships for the same `(original_state, terminal)` form an existential union, as required for projected epsilon-closed lexer configurations. All supplied residual roots are preserved; there is no pruning from one distinguished reset root.

`lexer_with_terminal_residuals(expressions, groups)` can retain exact component coordinates during GLRMask lexer construction. `PreparedResiduals::from_lexer(&lexer)` consumes that sidecar, and `prepared.request(&vocab)` performs direct analysis. This avoids reconstructing the raw-to-terminal correspondence through a second vocabulary scan. The lexer constructor is not a general resource-bounded grammar frontend: complex expressions may require a prepared or synthesized lexer supplied by the caller.

## Explicit partition families

```rust
use lexquot::{
    PartitionSpec, PartitionedRequest, Observation,
    Expr, Vocab, lexer_from_expressions,
};
let lexer = lexer_from_expressions(vec![
    Expr::U8Seq(b"a".to_vec()), Expr::U8Seq(b"b".to_vec()),
]);
let vocab = Vocab::new(vec![
    (0, b"a".to_vec()), (1, b"b".to_vec()),
    (2, b"ab".to_vec()), (3, b"ba".to_vec()),
]);
let result = PartitionedRequest::new(&lexer, &vocab)
    .partition(PartitionSpec::new("single", Observation::L1, [0, 1]))
    .partition(PartitionSpec::new("crossing", Observation::L2P, [2, 3]))
    .analyze()?;
assert_eq!(result.parts().len(), 2);
# Ok::<(), lexquot::AnalysisError>(())
```

Each part retains its own state map and observation domain. The combined token map is a common refinement of local token classes, including missing-coordinate distinctions. Overlapping terminal-observation families are supported. Uncovered byte tokens, unknown IDs, and duplicate partition names are rejected.

This API does not guess a grammar-dependent L1/L2P routing proof. The example explicitly chooses the consumer observations. In GLRMask, the host classifier can also route non-crossing cases of an L2P terminal family through a split-off L1 builder.

## Initial states and reset continuations

Use `.initial_states([...])` to restrict the queried token-start domain. States outside it receive no class. **Reset states still participate in L2P suffix computation**, even when they are not queried initial states.

Use `.terminals([...])` for a terminal-observation restriction. Follow restrictions are terminal-ID pairs, supplied with `.forbidden_follows(...)`; they apply to L2P. The caller must normalize any IGNORE-transparent policy required by its lexer semantics. L1 rejects follow input rather than silently ignoring it.

## Exactness and backend selection

| Backend | L1 | L2P |
| --- | --- | --- |
| `Auto` (default) | Exact projected analysis, canonical fallback when needed | Collision-free canonical trace graph |
| `Canonical` | Independent scalar whole-token observations | Structurally interned trace graphs and reset suffixes |
| `Production` | Extracted optimized projected kernel | Extracted fingerprint-assisted production kernel |

The inherited fast L2P implementation uses compact fingerprints in some equality decisions. No collision was observed in the validation, but a fingerprint is not a deterministic equality proof. Its result is marked `Assurance::FingerprintAssisted`. Use `.verify(true)` to check every returned merge against canonical keys and obtain `CanonicallyVerified` assurance. Verification may be expensive.

The exact claim concerns the **declared observation**, not necessarily the coarsest possible terminal-word-language or grammar-language equivalence. Canonical L2P uses the extracted positive-completion scan contract: latest reported positive match per terminal, pending endpoint observations, and reset/follow continuations. Zero-width grammar-control effects and commit destinations not represented by that contract require a different or stronger observation.

`verify_refinement` allows a candidate partition to be finer than the reference. For example, the host may deliberately keep reset separate. It rejects merges of distinguishable IDs and IDs outside the reference domain.

## Resource limits

`Budget` bounds token length, map sizes, structural nodes, scan steps, and materialized signature cells. Exact structural and direct-residual paths return `BudgetExceeded` rather than silently returning a partial quotient. Sparse ordinary-token coordinates are checked before allocating a dense ID map. Exact-only special IDs do not enlarge the ordinary byte coordinate.

The budget is **not** a universal allocator cap for every inherited production optimization or for constructing a lexer from a regular expression. A prepared lexer, application-level limits, and a process deadline remain appropriate for untrusted or very large inputs. The benchmark runner records budget failures and process timeouts rather than dropping them.

## Reproducibility

```sh
cargo test -p lexquot --all-targets
cargo test -p lexquot --doc
cargo doc -p lexquot --no-deps
```

The workspace's `research_bench` example accepts the recorded vocabulary format, several lexical fixtures, imported terminal-expression fixtures, explicit initial-state scopes, and alternate backends. The benchmark manifests record executable and input hashes. First invocation, warm repeats, lexer setup, and whole-process peak memory are separate fields.

The primary lexical fixtures and source-derived schemas are not a full JSONSchemaBench qualification. There is no measured CFGzip head-to-head comparison in this public source. The full experimental evidence is held privately during author review, and this repository makes no CFGzip head-to-head or end-to-end decoding claims.

## Implementation surface

The `l1`, `l2p`, shared coordinate types, and compatibility-policy modules contain extracted production implementation details. They are hidden from the main rustdoc navigation and are not the preferred stable API. GLRMask enables its workspace bridge and consumes these paths without duplicating the analysis algorithms. The checked request types above are the intended external interface.

## License

MIT OR Apache-2.0, matching the originating GLRMask implementation. See the bundled license files.
