# Proof-account route L1 closure — 2026-10-22

Status: work in progress; target not yet established.

Scope: D162 public proof-account nonce → `generate_for_mask_nonce` →
`prove_masked_retrying_with`, S2, native prover/r1p-check/private-leaf-salts.
The current frozen source retains TLS instrumentation. L1 includes its counts
and bytes; duration magnitudes remain L3. No shipped source changes.

## Stages

1. Define an ordered L1 record, with retained TLS state and exact error origins.
2. Prove retry ownership and conditional hazard identities without iid premises.
3. Audit the joint coupling interface and numerical charge; close only if the
actual source observations are covered.

## Trust and release boundaries

Retain E1, E2, P1, existing source refinement and TrustedStd/TLS boundaries.
No deployment binary/CPU pin is supplied by this proof-only task. D162 selects
a route; it does not certify a checked-in caller. No keys are created or removed.

Receipts: `docs/research/100bit-spend-path-20261013/evidence/sidechannel-l1-20261022/`.

## Stage 1 — record and retry-owner erasure

`R1Z/SideChannelL1AttemptRecord.lean` defines the ordered event carrier,
precise call/detail plus API error label, retained TLS bytes/check count,
attempt prefixes and returned count. It distinguishes callback Rejected
(abort) from attempt Rejected (retry). Partial underlying writes and errors
are represented individually, including interrupted writes; this is richer
than the previous logical-write environment model. Ledger contents/path
observations are public nonce/statement data, never private seed bytes.

J9865 passes: nine audited theorems, standard axioms only, wall 2.07s,
peak RSS 4,191,300 KiB, swaps 0. J9864 failed on an omitted list-length
simplification, fixed before rerun. J9800 was refused before compilation:
historical J9800–9863 receipts already existed. Only unused IDs are used.

Established: richer reference erases exactly to part-34 retry control,
retaining all state, with rejected/stopping/success prefixes and cap eight;
TLS append/count/retention semantics. **Not established:** every native
callee emits the declared record, honest-domain constant guards, or joint
privacy of this record. `source-map.json` is a manual source map, not a
source-refinement proof. It does not discharge those obligations.

## Stage 2 — conditional retry identities

`R1Z/SideChannelRetryLaw.lean` proves the rejection-prefix characterization,
callback-stop rule, cap-exhaustion execution and the audit's conditional
success/abort/entry identities for every `k : Fin 8` (human attempt k+1).
The finite carrier can retain the entire ROM, policy, ledger and seed tape;
no independence or stationarity premise is added. History-conditioned
identities and arbitrary failure-origin predicates use the same conditional
mass. Zero-mass prefixes are handled without excluding them.

J9867 passes: ten audited theorems, standard axioms, wall 1.79s,
peak RSS 4,169,768 KiB, swaps 0. J9866 failed because `prefix` is a Lean
syntax keyword; renamed the binder. The identities are exact for this
instrumented terminating reference. They do not supply any numerical
acceptance hazard or discharge native callee/event refinement.
