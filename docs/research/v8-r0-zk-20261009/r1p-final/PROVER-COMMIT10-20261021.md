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

## Stage 5: cursor accounting and the Kani composition boundary

`next_factor` factors the exact extracted next-word function without evaluating
any byte stream. `next_progress` proves that each successful next-word call
preserves the finite cursor invariant and advances exactly one word; the
64-bit counter bound excludes wraparound. Successful scalar sampling advances
strictly, so `samples_bound` bounds successful arrays by eight times their
block allocation.

`readBlock_total`, `next_total`, `scalar_total` and `collect_total` prove the
converse allocation property: with room for all remaining tries, these
reference computations cannot fail operationally or diverge. The full L₁/L₂
streams are instantiated at E₁/E₂ by `stream₁_total` and `stream₂_total`.
`rawArrays_failure` identifies failure exactly with a Rust error from one of
the two extracted collectors, rather than an extra backend-allocation case.
`accepted_word` proves that the extracted bit mask, comparison and field-value
conversion implement the fibre model's accepted-word predicate for every U32.
These are symbolic proofs; no large array, tape or recurrence is normalized.

Accepted focused attempts are J8314, J8315, J8317, J8318, J8320, J8322,
J8324 and J8325. Full axiom/error lines and all required resource/source fields
are in the receipts. J8323 hit the simplifier recursion limit while elaborating
the failure classification, not memory pressure. Its replacement J8324 keeps
counts/collect opaque and rewrites the two already-proved run equations first;
no recursion/heartbeat or memory cap is raised.

There is a concrete obstruction to treating the **existing local Kani
certificates** as the complete outer transport. The actual Rust expander ROM
has nine answers and asserts `index < 9`. `nine_block_source_none` proves that
**every** nine-block backend fails to produce the required 4096-limb second
raw array; `nine_block_decode_none` lifts that fact through the composed raw
decoder. At most 72 scalar samples can succeed from those nine blocks. A larger
unwind cannot repair that domain. This does not refute the fixed E₁/E₂ decoder:
it uses the full allocations. It does not refute a future compositional proof
with a retained global oracle and a proved window-rebasing invariant.

The new raw owned producer and cursor accounting remove additional reference
obstacles. They still do not establish the byte-load/cache-content identity
with `wordsE`, the complete shipped entry-point/outer-array transport, or the
all-family shipped runtime callback log. No new whole-program Kani/P6
certificate is claimed. No unchanged failed aggregate extraction, timed-out
whole-loop comparison or old regression is rerun. The missing outer transport
cannot be replaced by the new nine-block impossibility theorem.

## Verbatim before/after of the targeted premise

The pre-specialization D112 source is retained in `headline-original-v2.lean.txt`.
The complete operational-reference endpoint before/after the proposed premise
deletion is retained in `headline-specialized-before.lean.txt` and
`headline-specialized-after.lean.txt`. These files are identical and
`headline-deletions.diff` is empty. The fixed definition in both is:

```lean
abbrev ownedDecode := ProverCommitOwnedDecoder.decoder (K := PrivacyR1AcctBasis.K)
```

Before:

```lean
    (R_commit_caller : ProverCommitCallerInstance.CallerLaw
      (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)))
```

After:

```lean
    (R_commit_caller : ProverCommitCallerInstance.CallerLaw
      (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)))
```

D112 has no separately named universal shipped read-coverage binder. Both
execution joins and CallerLaw remain explicit. No single shipped-execution
join is claimed to have been constructed, and no source checklist row is
marked closed on the basis of the reference-only theorems.

## Final frozen audit and remaining work

`manifest.json` freezes 17 Rust/Lean sources, the exact next consumer and all
41 new theorem audit targets. `harness/validate.py --check` passes before the
single combined replay. **J8326**, target **R1Z.ProverCommit10Audit**, imports
the accepted continuation-9 cone plus every adopted continuation-10 module:
exit **0**, wall **1.69 s**, peak RSS **4106532 KiB**, **zero swaps**.
Source revision **d6bc1766c** contains all adopted predecessors; the additive
audit is pinned by its SHA-256 and literal attempted source snapshot.
The dependency fingerprint is retained in the receipt. All **41** printed
axiom results contain only `propext`, `Classical.choice`, `Quot.sound`, a
subset, or no axioms. This audit verifies the actual conditional endpoint;
it does not discharge its remaining hypotheses.

`harness/validate.py` passes after the replay: it checks the frozen source
identities, all attempted source snapshots and dependency fingerprints,
adopted module identities, extraction sharing against literal generated
bodies, the host Rust/Cargo input inventory, all capped host receipts,
the exact ELF comparisons, the empty deletion diff and the 41 final axiom
lines. This is evidence validation, not another Lean replay. Assigned attempts
are consumed through **8326**; next available **8327**.

Completed: a fixed operational-reference decoder and corresponding D112
specialization, extracted owned scalar-array production, exact finite backend
framing, successful array lengths, reference callback support, symbolic cursor
and retry-budget accounting, full reference allocation/error classification,
and the machine-word accepted-value law.

**Not completed:** CallerLaw for that decoder, the full shipped entry-point
and outer raw-array transport, and universal all-family shipped callback
coverage. The next mathematical consumer is a cache-content/byte-load
refinement to `wordsE`, followed by the sequential fibre law; the source
consumer is the complete entry-point-to-producer execution transport with a
consistent global oracle across local proof windows. The retained nine-block
Kani certificates cannot directly fill that source obligation. The local-ROM
obstruction does not show that the full E₁/E₂ reference refinement is false.

No peer-owned SourceIdentification, RustRuntimeJoin or PrivacyR1FinalRelease
file is edited. No push, merge, deployment or wallet cleanup is performed.
