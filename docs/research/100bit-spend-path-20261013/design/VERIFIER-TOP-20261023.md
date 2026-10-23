# Verifier stage-entry assessment — 23 October 2026

Status: assessment in progress; S2 remains open. Branch
`codex/cx-verifier-top-20261023`. Receipts are at repository-root
`evidence/verifier-top-20261023/`.

## Frozen scope and intended claim

Assess actual `candidate::tx1`, `candidate::tx2_authenticated` and its
`tx2_common` continuation with cone top functions opaque. Successful extraction
is a prerequisite to source identity and the ordered cone decomposition;
no assumed callback identity will be reported as discharge.

The adapter theorem and the C5 checkpoint writer/resume endpoints are reused
only within their stated premises. No existing Lean module or shipped Rust
source is changed. Release pins and initial source hashes are in `target.json`.

## Validation and remaining obligations

Initial inspection only: zero Lean attempts, zero Kani runs, no new theorem,
no axioms audit, no release build. Target not yet established. Next deliverable:
an admitted capped extraction probe and its exact source/tool receipt, or a
minimal stage-glue restructuring proposal if the probe exposes an obstruction.
