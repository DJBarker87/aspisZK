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

## Stage 2: operational-reference headline specialization

`PrivacyR1HeadlineOwned.privacy_headline_owned` specializes D112 to the fixed
operational decoder. `tapeOf_eq_owned` checks definitionally that the constructed
prover retains precisely that decoder. The simulator, experiment, error and
conclusion are inherited verbatim from D112. The existing endpoint is preserved.
The new theorem still explicitly asks for CallerLaw; no deletion is claimed
before its operational cursor law is proved. The new reference endpoint is not
a certificate of the shipped producer.

J8291 and J8294 check the decoder support/projection and successful-length
lemmas. J8303 checks both new endpoint theorems. Each passes with only a subset
of `propext`, `Classical.choice`, `Quot.sound`, zero swaps and the prescribed
6G/8G/no-swap/64-task scope. Exact targets, hashes, dependency fingerprints,
base revision, wall time, peak RSS, exit and full axioms/error lines are retained
in the per-attempt JSONL and verbatim logs. Excluded elaboration drafts are
retained, never treated as formal evidence. Only new worker-owned modules are
installed in the shared Env J source/object tree; their successive versions
are snapshotted by the launcher. No peer-owned source is replaced.

## Stage 3: finite oracle backend

`ProverCommitOwnedBackend` proves little-endian byte decoding by symbolic
induction on bit width, then proves that every extracted counter frame selects
exactly its indexed supplied oracle block. The last block is included and every
counter at or beyond the allocation fails. These statements do not unfold a
large counter, sample stream or tape. J8305 passes all four printed axiom audits
with the standard three axioms, zero swaps. Earlier backend elaboration drafts
are retained as excluded attempts. This closes counter-frame parsing, not yet
the state/cache position invariant or scalar-array fibre equality.
