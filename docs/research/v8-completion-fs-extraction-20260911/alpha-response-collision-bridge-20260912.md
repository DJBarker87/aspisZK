# Alpha response collision and same-body parser bridge

## Result

This continuation closes one deterministic seam in the alpha-fork collector.
For two literal V8 response0/alpha-nonce absorb chains that reach the same
alpha candidate input, Lean now proves the following total alternative:

1. the two 96-byte response0 slices are equal; or
2. the response0 absorbs have distinct inputs and the same full 256-bit
   output; or
3. the following nonce absorbs have distinct inputs and the same full
   256-bit output.

No hash injectivity premise is used.  A second theorem proves that equal
response0 slices in two successfully parsed bodies determine equal values for
all six canonical QM31 fields consumed as relation response zero.  Its matrix
specialization obtains both parser witnesses from the actual successful
source-functional records; it does not accept a caller-supplied parsed word or
coherence certificate.

The new checked leaves are:

- `lean/FSV8AlphaResponseCollisionDichotomy.lean`
- `lean/Response0ParsedBridge.lean`

## Security implication and boundary

This removes `AlphaPrefixCompatible.response0_eq` as an independently
unexplained *byte-to-value* premise once the matrix producer supplies equal
literal alpha candidate inputs and no collision occurs.  It does not yet
construct the 29-by-4 matrix or place the two collision-producing calls in one
global chronological random-oracle execution.  Therefore no collision
probability is entered in the global ledger here.

The other two `AlphaPrefixCompatible` fields, equality of kappa and tau within
each gamma row, also remain chronology/source obligations.  Equality of a
configuration name or membership in a configuration list is not used as a
substitute.

## Focused replay evidence

Pinned toolchain:

```text
/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
```

Common invocation shape:

```sh
BASE_PATH="$(cd /Users/dominic/ZK/AspisFormal && lake env printenv LEAN_PATH)"
CACHE=/Users/dominic/ZK/.cache/v8-lean-union-432
env LEAN_PATH="$CACHE:docs/research/v8-completion-fs-extraction-20260911/lean:$BASE_PATH" \
  /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -j1 -M7500 TARGET.lean
```

Results:

| Target | Exit | Wall | max RSS | swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8AlphaResponseCollisionDichotomy.lean` | 0 | 87.83 s | 3,696,459,776 B | 0 | `propext`, `Classical.choice`, `Quot.sound` (the generic theorem does not use `Classical.choice`) |
| `Response0ParsedBridge.lean` | 0 | 73.09 s | 4,173,430,784 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |

Retained logs:

- `results/alpha-response-collision-lean-20260912.log`
- `results/alpha-response-parser-bridge-v2/lean.log`
- `results/alpha-response-parser-bridge-v2/exit-code.txt`

There is no `sorryAx` in either successful result.  The earlier
`alpha-response-parser-bridge-v1` evidence is retained as a failed compile: it
used the wrong namespace for `Script` and exited 1 before the corrected v2
run.

## Next decisive theorem

Construct the canonical gamma-row/alpha-column replay family from one legal
outer source execution.  For each row, prove that the four alpha continuations
share the source-produced pre-alpha prefix, hence kappa and tau, and share the
same literal alpha candidate input except for the programmed full output.
The result should produce `AlphaPrefixCompatible` or an explicit globally
represented collision/late-target failure.  Only that global scheduler result
can attach the collision term and feed the already checked recovered-matrix
theorems.

Global accepted-invalid-payment soundness, permitted-access payment
extraction, Fiat--Shamir probability composition and adaptive zero knowledge
remain open.
