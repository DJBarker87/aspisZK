# R9: abstract two-transaction experiment and transport (2026-10-21)

Branch `codex/cx-r9-transport-20261021`, base `6302ea9d3`.
Paths below are relative to `docs/research/100bit-spend-path-20261013/`.
This additive model packet does not instantiate the frozen source or close R9.
Existing Lean modules, verifier/prover source, shared objects and keys are untouched.

## Stage 1: experiment and pointwise coupling

`lean/R9TwoTransactionExperiment.lean` defines a finite causal byte-oracle
program: run stage 1, retain its checkpoint and completed query tape, reject
if there is no checkpoint, otherwise run stage 2 with that exact checkpoint.
`eval_success` proves chronological concatenation of the two interpreter
traces. Both stages use one total byte oracle in `eval`, and one memo table
in `lazyMean`; there is no intertransaction reset.

The continuation returns a designated recorded view: its public statement,
messages, acceptance flag and the log consumed by the existing recorded
extractor. This is an abstract source observation/projection, not an invented
implementation of the frozen decoder or writer. Full source interpreter
calls can exceed that designated core log. The source refinement must prove
the projection correct for the actual experiment, including its same public
Rspend; arbitrary supplied recorded values do not establish this.

`failure` is successful continuation acceptance with extraction returning
`none`, for the same recorded view and independent private extractor coins.
`deployedMass` averages those coins. Source failure probability will average
this observation over the lazy source program. Rejection is retained rather
than conditioned away. The query tape is completed even on rejection;
unexecuted suffix draws are ghost padding whose source correspondence is owed.

`joint_inventory` consumes the exact common-carrier consistency and coverage
certificates supplied by LOG-TX2's separately compiled tx1/tx2 results.
It applies `RawDigestLogCarrier.append_consistent` and `append_covers`.
This avoids the known generated-package global-instance import collision.
It proves a consistent covering union, not chronological ordering. Chronology
comes from `experiment` and still requires actual-source correspondence.

`OrderedSourceRefinement` states a pointwise source-run equality off query
exhaustion. It preserves the complete designated log, exact public/messages
and acceptance, and therefore works for every extractor coin tape.
`pointwise_transfer` applies the existing QueryScan finite transfer theorem
for those tapes. It derives the failure inequality; no mass inequality is
assumed. The source law remains stronger than the current R10 inventories.

## Validation so far

Focused stage-1 compile: `R9TwoTransactionExperiment`, attempt 2, exit 0,
11.104 s, peak RSS 3,584,671,744 bytes, zero swaps, three standard-only axiom
audits. Attempt 1's ambiguous `State` namespace and consequent elaboration
errors are retained as failed evidence. No memory failure or cap increase.
Full commands, source snapshots, dependency hashes, revision, timing and
audits are under `evidence/r9-transport-20261021/manifest.json`.
