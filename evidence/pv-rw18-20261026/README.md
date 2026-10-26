# rw17 resume: whole-loop context and data join

Base `c4eb7e74cb`, branch `codex/cx-prover-rw-20261023`.
Allocation: 100 Lean invocations, 20 Kani harness runs; Env-J IDs25900–26199.
No shipped source, wallet key, release pin, sibling worktree, or shared launcher is modified.
The target is not yet established.

## Stage 1 before / intended after

Before: rw17 proves the combined emitted transition's complete iterator loop
and arbitrary-slice compression equal the closed owned reference. The original
helper's full-source association and the live op223 join are absent.

The new inline-context declarations explicitly separate an arithmetic-inlined
for-loop context from the combined step's Boolean interface. The intended
induction retains all continuing accumulator/power state and projects only the
terminal accumulator. These declarations are **not** claimed to be an extraction
of the original helper. The sibling-owned source identity must still be supplied.
No endpoint or ledger row is discharged by introducing a context definition.

## Ownership and concrete model

Read-only `git grep -l op223 codex/pv-cb3-20261026 codex/pv-cb-20261026`
was run before stage1. pv-cb3's ROWS.md lists op223/V240 OPEN; no Op223Source
module was present. Its source law is reserved to that worker.

The read-only runjoin SourceConstructor/SourceBoundary modules expose a partial
runtime with world, policy, native inputs, disclosed/oracle projections and ideal
handler parameters. CanonicalFixtures proves mathematical nonempty fibres while
retaining the native public-record associations. They do not provide V163's
concrete source/model byte-and-audit comparison. Clarification on the intended
pinned instance is pending; no model is defined as the actual output merely to
make the equation reflexive.

## Validation discipline

Each focused local compile uses the retained pinned J object cache, Lean4.32
-M7000, and no dependency build. The immutable input/receipt pair records source
revision and hashes, imported object fingerprints, target, exit, wall, RSS, swap
and complete axiom reports. This is focused cached evidence, not a coherent
release replay. Failed elaborations and their error-generated sorryAx output
are retained as failures, never imported as accepted evidence.

25901 was a dependency preflight refusal; it invoked no compiler and costs zero.
KANI-PLAN.json lists all candidate harness names before any charge. Bounds2/3
cover loop-free/one-element contexts; bound18 exceeds the proved17 arity16
iterator evaluations and covers the finite16-element array conversion. Each
native run uses the existing host runner with6G/8G/swap0/Tasks64, one host scope
at a time, optimized Rust and unwinding assertions. Special-value gates retain
their restrictions and do not imply an arbitrary-input certificate.

Host admission004 refused at18:33:26.823899UTC (60,532,195,328 bytes
reserved;69,122,129,920 projected >59,055,800,320 safe). No scope/compiler
started. Retry004r1 was after18:36:26.823899UTC and was refused again.
Both are zero charged Kani runs; next retry waits at least180s from004r1.
The intermediate remote Python quoting error invoked no harness or scope.

## Stage 1 checked result

`ProverRw18ContextInduction.run` proves the inlined context equals terminal
projection of the emitted-step iterator for arbitrary slices, positions,
accumulators, powers, lambdas and primitive dictionaries, including all Result
branches. `ProverRw18ContextReference.compress` links that context to the indexed
extracted P6 reference without selected-arithmetic assumptions.
`ProverRw18ContextCompression.owned` then specializes to closed current arithmetic.
`ProverRw18ContextFuel.arity16` proves17 sufficient; `ContextTotal.paired_total`
proves inhabitance for any two typed16-tuples with no success hypothesis.
This last theorem has not yet identified the actual native fixture tuples.

The exact retained join obligations are visible in `ProverRw18ContextJoin.callback`:
`source_law : ops.op223 = extracted` and
`context_identity : extracted = @ProverRw18ContextCompression.compress _
(PV_CurrentScaleInstall.selected ops)`.
Neither is proved by the new theorem. V164's mathematical context is reduced;
its original-source association and V240 source law remain OPEN. V163 remains
OPEN with exactly its original whole-data premise. No endpoint/deployment
premise removed, renamed, weakened or silently bundled.

Validation through25913:13 charged Lean checks,10 passes/3 elaboration failures;
all accepted axiom reports are standard. 10/20 Kani gates pass so far, with
no failing comparison and no timeout. Full individual receipts are retained.
The final cached manifest/axioms audit will run once after the source stages.
