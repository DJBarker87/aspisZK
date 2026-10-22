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
