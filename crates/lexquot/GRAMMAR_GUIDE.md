# Grammar-aware vocabulary equivalence

Use `lexquot::grammar` when the intended equivalence is for **one supplied byte
language**, rather than every possible grammar built from a flat lexical family.
This is a standalone analysis: it does not link GLRMask, build parser tables,
compile a constraint, or consume another engine's vocabulary classes.

```rust
use lexquot::{Vocab, parse_regex, trace::TraceDfa};
use lexquot::grammar::{Dfa, Grammar, Options, Symbol};
use Symbol::{Terminal as T, Nonterminal as N};

// A quoted string. Its character recursion is grammar structure, not an
// externally observable count of single-character terminals.
let quote = TraceDfa::from_expression(&parse_regex("\"", false))?;
let letter = TraceDfa::from_expression(&parse_regex("[ab]", false))?;
let grammar = Grammar {
    start: 0,
    terminals: vec![Dfa::from(&quote), Dfa::from(&letter)],
    rules: vec![
        vec![vec![T(0), N(1)]],
        vec![vec![T(0)], vec![T(1), N(1)]],
    ],
};
let prepared = grammar.prepare(Options::default())?;
let vocab = Vocab::new(vec![
    (7, b"a".to_vec()), (91, b"bb".to_vec()), (104, b"\"".to_vec()),
]);
let result = prepared.analyze(&vocab)?;
assert_eq!(result.partition.token_class(7), result.partition.token_class(91));
assert_ne!(result.partition.token_class(7), result.partition.token_class(104));
# Ok::<(), lexquot::AnalysisError>(())
```

## What is normalized

Input terminal DFAs are checked, restricted to their reachable byte languages,
and minimized. Nullable terminal languages are lifted into explicit optional
productions; positive loops through an accepting start are retained, not clipped.
Nonproductive branches and unreachable rules do not become observations.

A strongly connected component of nonterminals is folded only when all external
references are already regular and its productions are consistently right-linear
or left-linear. Empty productions and mutually recursive linear components are
supported. Acyclic regular productions and aliases are included. Exact bounded
NFA construction, subset construction and minimization produce the language of
each folded nonterminal. Nonlinear, mixed-direction, or state-budget-declined
components remain ordinary context-free grammar structure. A work-budget error
is reported rather than returning an uncertified partition.

The remaining grammar uses those regular fragments as terminals. Their old
internal character terminals are **not** kept as extra observational coordinates.
Equal positive terminal languages may be shared. Nullable wrappers remain in
the CFG so terminal adjacency accounts for epsilon paths without enumerating
all combinations of optional symbols.

## Two analysis paths

When the whole start language is certified regular, the default engine computes
exact token transformations on its minimized DFA. Equality over all reachable
DFA states is the two-sided syntactic congruence of that fixed regular language.
Original spelling and token ID do not determine the classes, and different token
lengths may merge when the grammar allows it.

When normalization leaves a context-free remainder, `trace::grammar` derives legal adjacent
terminal pairs using productivity, reachability, nullable, FIRST and LAST sets.
First-match coordinates combine a projected Boolean residual with its allowed
successor scope. Subsequent completions retain their terminal labels and exact
unfinished right languages. This is a sufficient substitution relation for the
supplied CFG, not generally its coarsest grammar-specific congruence.

`Options` exposes regular folding, successor scopes, the regular-DFA path and
transition caching separately for controlled experiments. Turning off a semantic
normalization can yield a finer relation; it is not an equal-compression runtime
ablation. The old uniform `trace` API and inherited L1/L2P contracts are unchanged.

## Safety and operational use

The guarantee concerns membership in the **byte language** obtained by ordinary
CFG substitution of regular terminal languages. It does not preserve parse trees,
terminal identities, captures, semantic actions, maximal-munch priorities or
value-dependent constraints. Such consumers need their own contract. `Dfa` is an
input record; `prepare` validates it before compilation.

Expand class masks to the original vocabulary before sampling. Preserve the
sampled original token and its bytes in the model context. A language-only grammar
checker may consistently use class representatives under the stated substitution
guarantee; this does not authorize replacing the model's original tokens.

Ordinary vocabulary entries must have nonempty bytes. EOS/control events are
outside this domain. Sparse original IDs and duplicate byte spellings are kept.
Every result contains complete membership lists, original-to-class coordinates,
representatives, an optional explicitly dead class, the selected algorithm,
preparation statistics and the guarantee string. No finite-vocabulary
lexer-initial-state quotient is computed. DFA minimization is ordinary
regular-language preparation, not a runtime lexer-state substitution claim.

Preparation may be reused for other vocabularies. Every `analyze` call has fresh
analysis caches. Timing comparisons should include normalization and engine
preparation when reporting complete vocabulary construction, and disclose any
external regex/grammar parsing or model-vocabulary setup.
