# Exact all-completion vocabulary equivalence

`lexquot::trace` is a separate, stronger interface than the inherited scoped
L1/L2P API. It computes vocabulary classes only; it does not compute an
initial-lexer-state quotient. It retains every terminal completion inside a
model token and, by default, the right language of an unfinished terminal.

```rust
use lexquot::{parse_regex, Vocab};
use lexquot::trace::{TraceDfa, PreparedTrace, PrepareOptions};
let terminals = [
    TraceDfa::from_expression(&parse_regex("[a-z]+", false))?,
    TraceDfa::from_expression(&parse_regex("[0-9]+", false))?,
];
let prepared = PreparedTrace::new(&terminals, PrepareOptions::default())?;
let vocab = Vocab::new(vec![(10, b"cat".to_vec()), (20, b"dog".to_vec())]);
let classes = prepared.request(&vocab).analyze()?;
assert_eq!(classes.token_class(10), classes.token_class(20));
# Ok::<(), lexquot::AnalysisError>(())
```

## Contract

With `EndpointPolicy::Residual`, equality is sufficient for token-byte
substitution in any context-free grammar over the supplied regular terminal
languages, under ordinary language substitution and nondeterministic lexical
segmentation. This is a **sufficient**, not necessarily coarsest, relation.
Terminal labels are retained. Longest-match rules, terminal priorities, semantic
actions and value-dependent constraints are not included implicitly.

A terminal DFA must recognize a nonempty language and reject the empty string.
For nullable regular terminals, first move the empty alternative into the
context-free grammar and supply the nonempty part. Do not clear a looping DFA
start state's accepting flag: nonempty revisits must retain their acceptance.
All declared live DFA states are possible initial observation roots, including
states disconnected from the distinguished reset root. The product comparison
backend rejects a domain whose declared roots it cannot cover.

`EndpointPolicy::Mask` deliberately forgets residual right languages. It is a
weaker current-token observation, **not a byte-substitution contract**; a host
using this mode must retain and commit the original token bytes. The inherited
L1 live-prefix API and latest-completion L2P API have their own narrower
contracts and should not be silently substituted for this observer.

Ordinary tokens are nonempty byte strings with original `u32` IDs. Sparse IDs
and distinct IDs with identical spellings are supported. EOS, added controls and
other non-byte events must be managed separately. An empty observation class is
globally *lexically* dead, not merely invalid in one parser context.

## Implementation and controls

Terminal DFA right languages are minimized as a Boolean-output disjoint union.
The first terminal's identity remains in a root projection. Every later reset
uses the entire labelled terminal family. A reverse prepend recurrence shares
complete observation columns, including columns reached by different suffix
strings. Trace languages are interned deterministic acyclic word graphs;
canonical union combines alternatives with identical terminal labels. Hash
maps compare full keys, so digest collisions cannot merge unequal observations.

`TraceAlgorithm::Product` is an exact same-observation reference using labelled
product roots. `PrepareOptions` controls physical minimization and cross-terminal
sharing. Endpoint labels remain canonical even when physical sharing is turned
off; those representation ablations do not weaken the requested observation.
`cache_transitions(false)` and `byte_classes(false)` disable two independent
work-sharing mechanisms. Each `analyze()` has fresh observation caches; reusing
`PreparedTrace` reuses only terminal preparation.

`TraceBudget` bounds states, cells, columns, language nodes, union work and token
length. A budget failure returns an error rather than a partial token quotient.
It does not bound an upstream regex compiler's allocations. Hosts should apply
appropriate frontend and process resource limits as well.

The separate `token_effect` module provides an exact structural-refinement
implementation with first-byte row factoring and collision-checked cross-shard
stitching. It need not return the same classes as canonical trace-language
union. Its `SymbolicByteRun` handles a single byte-class repetition language
without constructing a DFA proportional to a numeric repetition bound. This is
not a general rule permitting arbitrary regex repetitions to be truncated at
the longest token length.

The examples `trace_bench` and `token_effect_bench` are research entry points.
They report preparation and analysis with explicit cache lifetimes and preserve
original-ID class maps. They do not load language-model weights, sample output,
or measure end-to-end decoder throughput.
