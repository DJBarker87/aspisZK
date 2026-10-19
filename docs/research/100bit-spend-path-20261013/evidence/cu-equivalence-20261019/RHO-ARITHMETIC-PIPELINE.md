# Candidate 12: arithmetic pipeline checked, source caller open

Highest-saving remaining candidate: 42,693–42,746 stage-1 CU plus
51,250–51,356 settlement CU. Gamma reuse is paused per the user's savings-first
priority; NEXT-GOAL.md records the goal and remaining measured order.
**Candidate 12 is not closed.** The closed replacement count remains one.
Production Rust stays at 39c2971dd16c95858a4cfd2c9ae35da052eacfa9.

The exact old coefficient RHS and complete CM31/QM31 mul_m31 bodies are freshly
emitted with the original strict reference producer. Their carriers are
compared to the original arithmetic carriers before reuse. M31.mul and
QM31.add bind directly to the original checked functions, never diagnostic
stubs. All three generated function bodies remain unchanged when promoted.

CuSavingsRhoReference.push_reference equates the actual old arithmetic to the
complete checked optimized push after canonical projection, retaining the
next-prefix overflow bound and actual four-term flush condition.
CuSavingsRhoVector.updates_success composes actual pushes through the Vec frame
across every fresh, nonrepeating valid coordinate. Good distinguishes rows
already updated from rows still at the previous prefix bound. The counter
stays fixed during that traversal. CuSavingsRhoQueryBatch.batch_success checks
its single increment afterward and resets Good when every row is covered.

CuSavingsRhoBatches.batches_eq composes up to 22 batches and the actual source
finish theorem, including arbitrary Result failure/divergence between batches.
initialized_eq consumes the existing canonical initialization list model.
Power/basis canonicality, valid unique full coordinate coverage and query count
are explicit local invariants, not candidate-equivalence premises. The actual
verifier source must still supply these invariants and this traversal.

Still required:

1. Actual BatchedWeights::new/zip correspondence to initialState, and
   allocation under sufficient resources. The assignment proof alone does not
   establish zip/allocation execution.
2. Actual accumulate_with_node source binding, including basis construction,
   coordinate enumeration and counter. Its local invariants are not assumed
   true merely because fixtures pass.
3. Actual tx1_finish/tx2/tx2_authenticated checkpoint/relation/observation
   composition, including diagnostic-log erasure.

One initialization emission with the original reference producer fails at
mutable zip context collapse. One focused full paired accumulation emission
fails at InterpBorrows.ml:2731. Both failures are retained and NOT_ADMITTED.
No compiler patch, disabled check, larger-memory retry or production algorithm
change was introduced. The arithmetic proofs do not import partial emissions.

| Target | Accepted receipt | Wall s | Peak RSS KiB |
|---|---|---:|---:|
| AspisR1RhoReference/Funs | rho-reference-step-funs-b | 2.405 | 2,623,892 |
| CuSavingsRhoReference | rho-reference-proof-c | 2.205 | 2,670,172 |
| CuSavingsRhoVector | rho-vector-c | 2.205 | 2,644,540 |
| CuSavingsRhoQueryBatch | rho-query-batch-b | 2.405 | 2,648,144 |
| CuSavingsRhoBatches | rho-batches-a | 2.205 | 2,656,232 |

All print only propext, Classical.choice and Quot.sound, with zero observed
process/cgroup swap. Exact commands/revisions/features/source snapshots/import
object pins and metrics are retained per receipt. User-authorized uncapped
NUC policy applies. No broad/unchanged Lean or runtime regression was repeated.
Strict source receipts: rho-reference-step-charon-b and
rho-reference-step-aeneas-b. The first a emission matched the wrong opaque
method spelling and emitted diagnostic panic stubs; it is not interpreted.
The first promoted compile had an import-placement error and was superseded.
rho-reference-proof-a stopped at missing-prerequisite preflight before Lean;
its launcher failure is not a formal run. Failed local proofs are retained.

check-rho-arithmetic-pipeline.py validates source kits, complete emitted-body
promotion, current successful source/receipt hashes, cross-target object pins
and standard axioms. RHO-ARITHMETIC-PIPELINE.json records the exact check and
candidate_complete=false, plus failed source admissions. No binary is included.

Re-pin inventory: the changed owners remain candidate 12's existing inventory.
New consumed source declarations are AspisR1RhoReference.field.CM31.mul_m31,
AspisR1RhoReference.field.QM31.mul_m31 and AspisR1RhoReference.step (old RHS).
Shared arithmetic is AspisR1Qm31ArithmeticProbe.field.M31.mul/QM31.add.
Existing AspisR1CuRho.verifier.BatchedWeights.push and
AspisR1CuRhoSource.verifier.BatchedWeights.finish are consumed directly.
The complete accumulation cuts have no admitted emitted declarations here.
