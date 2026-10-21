# Checkpoint bytes fourth packet

Branch `codex/cx-ckpt-bytes4-20261022`. Additive Lean and task tools only.
Work in progress; no complete source instance or source-stage closure claimed.

The lead's C3-BIN addendum (2026-10-22 03:00) fixes the requested form:
AcceptedRunJoin. Successful source resume outputs and six ordered digest
reads must equal strictStage/dV_frozen2. Every source Err, including Allocation,
is rejection. This is the success-conditioned join form, not a new premise.

## Section kernel refinement

`CheckpointBytes4Sections.read_k_identification` identifies the complete
reference-decoder Reader Result with a C5 decoder over the actual 16-byte
array. No bounds, canonicality or allocation hypothesis. Raw reader failure
is retained. `read_list_identification` and `weight_loop_identification`
transport this equality through short-circuit section reads and the imported
mutable iterator next/writeback operations. `read_list_length` proves every
successful section has its requested length. These are operation/content
results; the mutable loop still needs its full output-content theorem and
adoption into the concrete ResumeOps callbacks.

Accepted attempt Sections-2: exit 0, wall 5.6593031249940395 s, peak RSS
3673571328 bytes, swaps 0. Standard axioms only; exact revision, hashes,
commands and every #print axioms line in manifest.json and receipt.
Sections-1 is a retained failed elaboration attempt; recovery sorryAx is
not accepted evidence. All compiles use private objects and the shared
mkdir lock, -j1 -M4400 -DElab.async=false. No host env J range is used.

## Remaining

1. Concrete ResumeOps, semantic/weight source-loop refinements.
2. Consume the concrete instance with successful_fields.
3. AcceptedRunJoin through reached_stage/strictStage, decision_observation
   and dV_frozen2, retaining exactly S2S10CallerBinding and
   S1S7S8StateProvenance without hiding observation equality in either.

No shipped source, existing Lean module, session A candidate, shared object,
wallet or key changed. No frozen ELF rebuild trigger. No release replay,
release/security claim, push or merge. The final requested theorem is not yet
proved, so no unverified statement is presented as a proved theorem.
