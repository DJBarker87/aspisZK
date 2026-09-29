# R76: exact runtime word and per-limb model correspondence

Base revision: `dd09920adb9dc1c49364345c1cff9f8c4d2e1424` (R75).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Proved boundary

`SamplerWordBridge` proves the runtime little-endian decoder equals the
retained `SamplerWords.word` integer formula for every block and each of its
eight word positions. The proof uses symbolic byte concatenation, an exact
four-byte slice lemma and integer bounds; it does not normalize large
concrete words or test selected examples. The source bit mask also equals
`SamplerWords.masked 31` exactly.

`SamplerLimbBridge.draw_exact` proves the source-side cursor draw equals the
value/cursor part of `QM31SamplerProgram.readRun` under R73's explicitly
constructed total hashv adapter for arbitrary deterministic `H`. Both cases
are covered: read the existing block or squeeze and read word zero on rollover.
The encoded next transcript includes the same adapter, so this result can be
used recursively without resetting or replacing the backend.

`limb_exact` establishes the bounded per-limb recursion's value, state, block
and cursor correspondence for every fuel length. `source_limb_exact` composes
it with R75's generated-loop theorem for the actual eight-attempt source
entry. Acceptance returns the model's limb, and exhaustion returns the prior
limb with `accepted=false` and the model's advanced cursor/state. The encoding
constructor is modular for arbitrary naturals, but all decoded-word and
masked-value uses have proved bounds, so this correspondence is not merely
equality modulo 2^32.

## What this does not prove

These theorems use the model run's **value/state projection**, not its trace
projection. A complete source observation/trace theorem remains open. The
adapter is explicit deterministic semantics, not a new random-oracle
independence assumption, a proof of concrete SHA ideality, or a concrete
backend refinement theorem. The four-limb deferred write-back and final QM31
assembly still need to be connected to the model's `limbsRun/challengeRun`.
No full privacy, complete sampler-observer or global soundness claim follows.

## Compilation and audit

Two Lean leaves compile with **13 theorem audits**. Twelve use only standard
Lean axioms. The final actual-source theorem additionally retains the cached
runtime's opaque `core.fmt.Formatter : Type`, as documented in R72. There are
no new axioms, admitted proofs or hiding assumptions; audit **PASS_SCOPED**.

Lean `leanprover/lean4:v4.32.0`, pinned NUC cache, `-j1 -M4500`. Actual cgroup:
High 5 GiB, Max 7 GiB, SwapMax 0, TasksMax 128. One final two-leaf replay reused
328 targets and checked 303 dependency pins.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Job swaps |
|---|---:|---:|---:|---:|
| `AspisV8R19/SamplerWordBridge` | 0 | 2.05 | 3,706,620 | 0 |
| `AspisV8R19/SamplerLimbBridge` | 0 | 2.02 | 3,706,252 | 0 |

The 29-artifact evidence manifest contains exact source/base pins, commands,
axioms, resource records and failed focused attempts. The first word proof
had one redundant tactic after the goal was already solved. The first bridge
needed finite-literal normalization and Boolean-branch simplification before
rewriting the masked value. Corrections passed at the original cap; no package
rebuild or higher-cap retry. Final logs have no `sorryAx`.

## First remaining proposition

Prove the actual mutable four-limb write-back and final QM31 reconstruction
match `QM31SamplerProgram.limbsRun/challengeRun`, using the exact source-limb
theorem. Then establish source observer/trace correspondence and compose with
the circle-map and outer retry proofs. Shared-oracle/seed/C2 justification,
complete joint-view simulation, visible failure/retry/publication accounting
and pre-beta quotient-pair extraction remain separate open obligations.

No runtime/protocol changes or new CU measurement. Retained complete CU:
**1,495,663 / 1,497,050**; both actual 1M-cap runs exhaust. Existing regressions
and unrelated work are preserved. No deployment or wallet operation.
