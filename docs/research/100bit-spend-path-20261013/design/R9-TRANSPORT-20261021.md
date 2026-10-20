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

## Stage 2: finite-source probability transport

`lean/R9QueryScanTransport.lean` defines `Tables source` as the answer tables
on the source program's finite potential support, including all branches.
`QueryWordCorrespondence source Residual` contains an explicit equivalence
between these tables and `(Fin 64 → Fin (2^18)) × Residual`, and a pointwise
equality identifying its first coordinate with the source's completed tape.
Residual is finite and nonempty. This is an exact equal-fibre requirement,
not an assumed failure probability, not fresh coins substituted for ROM
answers, and not something implied by R10's backend consistency.

`word_failure_mean` identifies the uniform tape event mean with the existing
`QueryScanModelFailure.failureProbability`. It is proved for symbolic N;
no concrete function-space enumeration or cardinal normalization is used.
`abort_mass` transports the equal-fibre correspondence through the existing
finite-support lazy-oracle law, `mean_equiv` and `mean_prod`.
`transport` puts source and model on the union of their potential supports,
applies the proved pointwise transfer, and derives exactly

```
lazyMean source emptyTable deployedMass
  ≤ lazyMean model emptyTable failureMass
    + QueryScanModelFailure.failureProbability (2^18).
```

The equal-fibre law is deliberately explicit. For example, a source returning
all-zero words certainly exhausts; a mere shared-hash/consistent-log premise
cannot certify the uniform model probability for it. The source work must
account for eight byte blocks, masking/word order, previously queried or
repeated addresses, adversary history and ghost completion. If unconditional
uniform completion is unavailable, this interface cannot be instantiated as
written. One must instead prove acceptance-preserving refinement without a
scan charge, or extend the coupling with separately justified bad events and
charge them. This packet does not assume such extra events have zero mass.

Stage-2 focused validation: `R9QueryScanTransport`, attempt 5, exit 0,
4.874 s, peak RSS 3,548,905,472 bytes, zero swaps, three standard-only audits.
Failed drafts are retained: namespace omissions, concrete cardinal reduction,
empty-table rewrite transparency, and higher-order matching in `mean_prod`.
An intermediate draft reached the default heartbeat limit while unfolding
concrete `fails` during equivalence matching; making that event locally
irreducible and supplying explicit arguments replaced that proof search.
No limit was raised. Attempt 4's compiler diagnostic was retained, but the
runner then failed to remove a shared lock directory which had become
nonempty. No foreign lock files were deleted. Its receipt is reconstructed
from its original command/source/log and rounded `/usr/bin/time` wall field,
explicitly marked as such. Later receipts preserve lock-cleanup errors rather
than losing compilation evidence. This was a failed target, never a rerun of
an unchanged passing source.
