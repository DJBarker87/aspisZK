# R75: generated bounded rejection and mutable-limb loops

Base revision: `f832e5033d9fdfc9b6e59c15f5369feac73b4602` (R74).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Proved source boundary

`SamplerInnerLoop.loop_execution` proves the actual per-limb rejection loop
equals a finite recursion on the remaining U32 range length. The entry uses
exactly eight available attempts, stopping earlier on acceptance. A cursor
with index 0 through 8 records the reachable-state invariant. At index eight
the recursion calls the actual squeeze; otherwise it reads the current block.
R74's source-body theorem supplies the correspondence, not an assumed draw law.

The source-result invariant proves that every successful return from this
loop has cursor at most eight; an accepted limb is less than 2147483647; an
exhausted limb retains its prior value. Rejection recurses from the advanced
cursor/state, and acceptance stops. No hypothesis that hashing succeeds,
terminates or returns uniform independent values appears in these execution
theorems. Backend failure/divergence remains in the finite recursion.

`SamplerLimbLoop.loop_execution` proves the actual mutable-limb loop equals a
finite recursion on the iterator's remaining length, retaining the actual
per-limb call and deferred write-back closures. Its `entry_four` theorem
reduces the actual `challenge_qm31` entry to an initial actual squeeze,
four-slot finite iteration (with early error), and the original final-array
reconstruction. An error returns the advanced transcript state.

This is **not yet** an equality to `QM31SamplerProgram.challengeRun` or its
full observed oracle trace. The final write-back/value correspondence must
still be composed with the inner result. In particular, retaining the
actual per-limb call and final reconstruction in the limb theorem must not
be described as having already proved the complete decoded output model.

## Compilation, audit and resources

Two changed Lean leaves compile with **14 theorem audits**. Seven use only
standard Lean axioms, and seven additionally depend on the inherited opaque
`core.fmt.Formatter : Type` through source `unwrap`. This remains a documented
`PASS_SCOPED` result. No new axioms, admitted proofs or hiding assumptions.

Lean `leanprover/lean4:v4.32.0`, pinned cached NUC workspace, `-j1 -M4500`.
Actual cgroup: High 5 GiB, Max 7 GiB, SwapMax 0, TasksMax 128. The one final
two-leaf replay reused 326 targets and checked 287 dependency pins.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Job swaps |
|---|---:|---:|---:|---:|
| `AspisV8R19/SamplerInnerLoop` | 0 | 2.25 | 3,712,056 | 0 |
| `AspisV8R19/SamplerLimbLoop` | 0 | 2.25 | 3,709,964 | 0 |

The 34-artifact evidence manifest records target source hashes, base revision,
commands, dependency pins, resource settings, axioms and failed focused
attempts. The initial inner proof needed explicit Boolean-branch reduction
instead of a simplifier that converted scalar equality to natural-number
equality too early. The initial entry proof needed the same option-match
ordering as the source. Both were fixed locally; no cap increase or package
rebuild. The final logs contain no `sorryAx`.

## First remaining proposition

Prove runtime little-endian decoding of the selected four bytes equals
`SamplerWords.word`. Use R73's explicit shared-oracle adapter to connect the
bounded inner recursion to `QM31SamplerProgram.limbRun`; then prove deferred
four-limb write-back and final QM31 reconstruction match its `limbsRun` and
`challengeRun`, including state, failures and oracle observations. This is
the next source-to-model boundary before circle/outer composition.

Concrete backend/shared-oracle justification, seed/C2 laws, complete joint
view simulation, visible failure/retry/publication losses and pre-beta
quotient-pair extraction remain open. No full privacy or soundness claim.

No runtime/protocol change, no unchanged SBF rerun. Retained complete CU:
**1,495,663 / 1,497,050**, both actual 1M-cap runs exhaust. No deployment or
wallet operation. Existing negative regressions and unrelated work retained.
