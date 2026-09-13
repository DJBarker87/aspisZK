# Executable pre-alpha factorization and complete coordinate router

Status: **functional same-body factorization proved; complete ordinary-alpha
coordinates routed; cache-aware source coupling remains open**.

Base revision: `27bcc08eb92482c36424346a0440aa9cfc4e4dbc`.

## What is newly constructed

`FSV8ExecutablePreAlphaFactorization.lean` splits the selected source middle
at the exact boundary after the alpha nonce and before the ordinary alpha
candidate sampler.  The returned `PreAlpha` value contains only data produced
by that execution.  Its continuation is the complete ordinary sampler, so
zero alpha is legal and sentinel rejection can consume one through four
output/advance pairs.

For every body, tape and entry oracle,
`run_factoredMiddleScript_eq_middleScript` proves equality of the complete
result and final oracle state.  No success, freshness or decoding premise is
used.

`FSV8ExecutableWholeFactorization.lean` lifts that result through the exact
source/OOD/gamma prefix and the unchanged authenticated suffix.  Its endpoint
is:

```text
run tape (factoredWholeStagedScript ... body digest) oracle
  = run tape (wholeStagedScript ... body digest) oracle
```

Thus the functional same-body verifier may expose this boundary without
changing its result, cache, fresh-answer cursor or chronological log.

`FSV8AlphaCompleteCoordinateRouter.lean` attaches the existing V7 K15
history-sensitive relation-alpha router to the exact V8 exposure cursor.  The
result is an exact decomposition into all eight possible duplex coordinates
(four output blocks and four advance-answer ghosts) plus the residual master
tape.  The literal V8 alpha marker is proved to be round zero.

## Deliberately partial operational fork leaf

`FSV8ForwardAlphaForkCursor.lean` exposes the first output/advance pair after
executing the real prefix.  This is useful as an operational plumbing test,
but it is **not** the exact verifier continuation:

- it emits a fork pair without first classifying the actual request as cached
  or fresh;
- it stops after that pair rather than executing the remaining candidate,
  query/rho and authenticated suffix; and
- one successful ordinary alpha can require up to four pairs.

It must not be substituted for `FSV8ExactRootCursor.rootCursor` in a soundness
claim.

## Remaining exact bridge

Functional `run` equality does not by itself identify the V7
`OracleMachine`/scheduler history.  `FSV8CompileScriptAlgebra.lean` proves
that compilation erases only static call-budget padding and preserves script
composition.  `FSV8CompiledWholeFactorization.lean` then proves the stronger
premise-free result

```text
compileScript (factoredWholeStagedScript ... body digest)
  = compileScript (wholeStagedScript ... body digest).
```

This is literal `OracleMachine` equality, not equality inferred from completed
runs.  Rewriting it inside the exact root preserves scheduler normalization,
cache handling, query history and exposure traces.

`FSV8CompileScriptAlgebra.lean` supplies the structural compiler laws used by
that result: compilation erases static `promote`/`pad`, preserves `bind`, and
the target `OracleMachine` bind is associative.  These laws are proved by
induction over the actual scripts/machines, not inferred from interpreter-run
extensionality.

`FSV8FactoredExactRootCursor.lean` closes the intervening root-identity step.
It substitutes the factored compiled program into the adversary-returned-body
callback and proves literal equality with `FSV8ExactRootCursor.rootCursor`.
The body, entry oracle, actors, limits, fuel, dependent runtime value and both
final oracle states are unchanged.  Consequently its erasure is the existing
probability-visible exposure cursor.  This remains one monolithic scheduler
machine: it does not yet construct a cache-aware split callback or identify
which of the one-to-four alpha pairs were fresh.

After that bridge, the live execution must route each of the one-to-four
answer-dependent pairs as cached or fresh, run the incremental ordinary
decoder, and couple every fresh coordinate to the exact root scheduler's
uniform master tape.  The existing coordinate equivalence alone does not
prove freshness.

Only after those steps may the existing V7 complete ordinary probability
theorem be applied to the V8 alpha event.  The causal digest/cache target
event and algebraic bad-alpha event remain distinct and must be charged
separately.

## Focused NUC checks

Lean was `4.32.0` at toolchain commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.  Every check used one Lean
process under `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`,
`RuntimeMaxSec=600`, `-j1 -M8192`.  The V7/source dependency cache was reused;
this was not a fresh transitive source rebuild.

| Leaf | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8ExecutablePreAlphaFactorization.lean` | 0 | 3.59 s | 6,805,184 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8ExecutableWholeFactorization.lean` | 0 | 4.09 s | 6,787,908 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8AlphaCompleteCoordinateRouter.lean` | 0 | 3.24 s | 6,816,832 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8ForwardAlphaForkCursor.lean` | 0 | 2.99 s | 6,788,424 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8CompileScriptAlgebra.lean` | 0 | 3.06 s | 6,542,156 KiB | 0 | `Quot.sound` |
| `FSV8CompiledWholeFactorization.lean` | 0 | 3.16 s | 6,794,004 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8FactoredExactRootCursor.lean` | 0 | 2.66 s | 6,778,912 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |

The first failed focused runs are retained in the machine report as
elaboration/proof-normalization diagnostics.  No heartbeat or memory-cap
increase was used to repair them.

## Security implication

This milestone removes a retrospective boundary assumption: the pre-alpha
state is now the output of the actual source-shaped functional execution, and
both the functional result and compiled effectful oracle program are unchanged
by the split.  It also prevents a false first-pair uniformity argument by
routing the complete eight-coordinate ordinary attempt.

It does **not** yet supply a Fiat--Shamir probability term, replay extractor,
global soundness composition, Rust refinement, or a new security claim.
Grinding contributes zero bits.
