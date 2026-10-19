# LexQuot

**Exact observation-scoped token and lexer-state quotienting for constrained-decoding compilation.**

LexQuot is an independently named Rust library and small workspace, extracted from the GLRMask compiler. It computes **vocabulary-token equivalences and lexer-initial-state equivalences** for a specified observation, without including GLRMask's parser or runtime mask engine.

The main Rust package is [`lexquot`](crates/lexquot/README.md), with four support crates vendored into this workspace under `crates/`.

## Grammar-aware vocabulary analysis

For a specific grammar, use [`lexquot::grammar`](crates/lexquot/GRAMMAR_GUIDE.md).
It retains the CFG, folds proved regular subgrammars, derives legal terminal
successors, and computes representative-safe byte-language classes. A wholly
regular grammar uses exact minimized-DFA token transformations. There is no
GLRMask runtime, parser-table, or CFGzip dependency. The original flat-terminal
`trace` API below remains available with its intentionally stronger all-CFG
observation contract.

## Exact all-completion vocabulary analysis

The additional `lexquot::trace` API computes collision-free vocabulary classes
from projected Boolean terminal residuals, preserving all completion positions
and (by default) unfinished-terminal right languages. Its stronger substitution
contract is distinct from the original observation-scoped L1/L2P interfaces.
See [the trace guide](crates/lexquot/TRACE_GUIDE.md) for semantics, limitations,
resource controls, and a minimal example. The `token_effect` module supplies a
structural-refinement alternative and a symbolic single-byte-class-run special
case. Neither new vocabulary interface computes an initial-state quotient.

## Main ideas

- **L1**: single-terminal live-prefix behavior, Boolean terminal residuals, retained raw-state projections, and reverse-preimage algorithms.
- **L2P**: multiple terminal completions, suffixes and reset continuations, pending terminal observations, and follow restrictions.
- **Scoped equivalence**: restricted initial states, terminal families, vocabulary partitions, and reconstruction of original token IDs/state IDs.
- **Checked API**: `AnalysisRequest`, `ResidualRequest`, `PreparedResiduals`, `PartitionedRequest`, a canonical structural reference backend, and optional canonical verification of optimized results.

A vocabulary partition is not an equivalence class. An initial-state quotient is valid only for the observation supplied, not for arbitrary lexer byte transitions or token replacement during a grammar commit. The inherited optimized L2P implementation uses fingerprints unless canonically verified; the default L2P API uses collision-free structural keys.

## All-completion vocabulary equivalence

The `lexquot::trace` interface retains every positive terminal completion and the
right language of any unfinished terminal. Boolean projected first-terminal
residuals share structure across terminals, while reset continuations retain
terminal labels. Canonical finite trace languages and exact reverse-column
interning avoid unchecked hash-equality decisions. This vocabulary-only path
does not compute a lexer-initial-state quotient.

Under ordinary CFG substitution of the supplied regular terminal languages,
`EndpointPolicy::Residual` supports grammar-representative substitution. Scanner
priorities, maximal munch, semantic predicates and other host policies require a
separate proof or a stronger observer. `EndpointPolicy::Mask` is weaker and must
commit original bytes. Neither computes the coarsest fixed-grammar congruence.

`token_effect` provides the complementary forward structural implementation,
partition-local factoring and an exact symbolic single-byte-class repetition
special case. The latter does not justify truncating arbitrary bounded regexes.
See the `trace_bench` example and independent `trace_equivalence`,
`trace_contexts` and `token_effect` tests. This extension is qualified on Rust
1.95.0; use that pinned toolchain for reproducing the current test run.

## Build and test

```sh
cargo test -p lexquot --all-targets
cargo test -p lexquot --doc
cargo doc -p lexquot --no-deps
cargo tree -p lexquot --edges normal
```

This repository includes only LexQuot and its supporting libraries, not the GLRMask parser, Terminal DWA construction, or full decoder. The original five-crate source before neutral package renaming passed **135 tests and three doctests**; see the tests here for the renamed tree. Rust 1.91.0-nightly was used for initial qualification. This package is **not yet on crates.io**.

## Research

The editable manuscript and experimental evidence are maintained in a **separate private repository** during author review. This repository contains no manuscript or unpublished experimental results. The examples provide reproducible grammar-aware and uniform-observer benchmarks. Scientific measurements are maintained separately during author review; vocabulary-construction timings do not imply an end-to-end model-serving speedup.

## Provenance and license

LexQuot's initial algorithms and support code were extracted from [GLRMask](https://github.com/IsaacBreen/glrmask), retaining the original copyright and dual-license terms. Its new Git history is independent. See [LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE), and [PROVENANCE.md](PROVENANCE.md).
