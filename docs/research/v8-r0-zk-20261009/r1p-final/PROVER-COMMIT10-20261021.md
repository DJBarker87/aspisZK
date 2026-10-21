# Prover commitment continuation 10 — 2026-10-21

Branch `codex/cx-prover-commit10-20261021`, base `2d99cfc8a`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit10-20261021/`.

## Stage 1: fixed operational raw decoder

`ProverCommitOwnedDecoder.decoder` takes only the two finite block streams.
It runs the extracted early-return scalar caller for the fixed L₁/L₂ counts,
using an empty cache, counter zero, and the two shipped domain constants.
The callback decodes the counter frame and returns the indexed supplied block;
requests beyond the supplied stream fail. Both the sampler's Rust error and
Aeneas failure/divergence become `none`. No field sample is obtained from
`quotientDecoder` or `representativeDecoder`.

The raw arrays use the existing coordinate equivalence. The protocol builder
performs balancing downstream; this decoder does not claim that a balanced
Rust output is a raw tape. Successful array-length proofs ensure that the
total list lookup defaults are never used on a successful collected array.
Universal callback support is proved for both composed streams. This support
is confined to the extracted reference, not the complete shipped execution.

The finite-block cursor equivalence and the shipped outer producer transport
are still obligations. The definition alone does not prove CallerLaw.
