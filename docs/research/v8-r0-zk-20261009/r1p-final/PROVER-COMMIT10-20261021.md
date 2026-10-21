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

## Stage 4: extracted owned collection

The proof-only Rust reference adds `collect_m31_owned`: ascending scalar
sampling with a fresh owned accumulator at every recursive call. Charon
succeeds (23.470 s, 677988 KiB RSS, zero swaps); Aeneas succeeds (0.453 s,
76736 KiB, zero swaps), with `has_errors=false`. Both run optimized in capped
scopes. The host source inventory verifies all 472 tracked Rust/Cargo inputs
against this worktree (the exact count is in `host-inputs-checked.json`).

Five generated dependency declarations are byte-identical to the already
adopted Step8 extraction. `extraction/shared-declarations.json` records each
literal definition hash. The new function is adopted verbatim under the
shared Step8 namespace and nominal types; raw generated Types/Funs are retained
as text. This port avoids duplicate nominal state/error carriers and adds no
opaque definition, theorem assumption or semantic edit.

J8306 checks the port. J8308 proves the whole extracted recursion equals its
finite owned fold, retaining allocation errors and partial error states.
J8311 proves that erasing the partial accumulator gives exactly the decoder's
sequential collection, in ascending order, under the explicit capacity bound.
All four new collection theorem audits use only the standard three axioms.
The finite collection theorem does not identify the shipped outer caller.

The sole Rust edit is under the existing proof-only module guard. After this
edit, all three frozen ELF builds and exact comparisons pass: default
`dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`
(1507400 bytes), devnet
`fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78`
(1507400 bytes), pool
`121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`
(605704 bytes). Walls are 2.261/2.214/0.407 s; peak RSS is
202212/202364/100116 KiB; all exits and swaps are zero. Complete build
commands/features, source pins and cgroup receipts accompany the comparison.
No ELF, LLBC, object, archive or key is committed. Caches and keys are retained.
