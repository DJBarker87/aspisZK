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

## Initial remaining inventory (superseded by the final handoff below)

1. Concrete ResumeOps, semantic/weight source-loop refinements.
2. Consume the concrete instance with successful_fields.
3. AcceptedRunJoin through reached_stage/strictStage, decision_observation
   and dV_frozen2, retaining exactly S2S10CallerBinding and
   S1S7S8StateProvenance without hiding observation equality in either.

No shipped source, existing Lean module, session A candidate, shared object,
wallet or key changed. No frozen ELF rebuild trigger. No release replay,
release/security claim, push or merge. The final requested theorem is not yet
proved, so no unverified statement is presented as a proved theorem.

## Concrete callback-content record and successful_fields consumer

`CheckpointBytes4Ops.ops reserved` is a closed ResumeOps record: explicit
variant constants, generic element-wise comparison, shared-iterator header
scan, bounded raw reader, K/E reference decoder reader, ordered query
validation, zero K, fallible filled, ten unrolled semantic reads and mutable
weight iteration. There is no abstract ResumeOps callback parameter.
`semantic_identification` and `weights_identification` identify the complete
helper Results with the same ordered operations driven by C5 K decoding,
including all short-circuit rejection outcomes. `successful_fields` applies
OraclePortCkptAbiSourceFields.successful_fields to this concrete record;
`successful_reservation` derives reserved=true from that execution.

Important trust boundary: this is the source-shaped callback **content
model**. The separately pinned native gates validate Reader and helper
implementation content, not a kernel extraction theorem for physical Rust.
The record's comparison/header/query ports are explicit implementations;
no claim of their unproved full frozen-source adoption is made. The C5
helper identification is operation-by-operation; adoption to the flat C5
checkpoint decoder still needs every field/cursor and namespace transport.

`CheckpointBytes4Weights.loop_success` proves exact mutable writeback through
actual imported next/back for arbitrary prefix/suffix, initial slots, source
reader and successful ordered reads. It retains all decoded values and the
ending iterator index, without vector assignment or allocator assumptions.

Accepted Weights-2: exit 0, wall 5.431434332858771 s, peak RSS 3670884352
bytes, swaps 0. Accepted Ops-2: exit 0, wall 23.49622887512669 s, peak RSS
3672702976 bytes, swaps 0. All six theorem reports standard; exact source
revision and commands in receipts. First attempts are retained elaboration
failures, never accepted evidence. No full replay or shipped change.

## Flat semantic and weight section contents

`CheckpointBytes4ReaderFields.k_success` / `e_success` recover exact flat C5
slice decodes, source namespace values, cursor and backing from any bounded
successful reader. `CheckpointBytes4FlatSections.list_success` joins the
operational short-circuit decoder to `OraclePortCheckpointAbiC5.decodeKs`,
with every value and exact cursor/backing; induction is symbolic in section
length, never normalization of checkpoint bytes.

`CheckpointBytes4SemanticFields.semantic_fields` inverts the exact ten
unrolled reads. `CheckpointBytes4WeightFields.loop_fields` inverts the actual
std mutable next/back loop on arbitrary initial values and prefix/suffix.
`CheckpointBytes4SectionContents.semantic_contents` and `weights_contents`
consume these facts with the flat C5 join, identifying **all** returned
semantic/weight values and their exact ending cursor. No output equality,
canonical-input fixture or allocation availability is assumed. Bounds only
assert that the section bytes are present; full checkpoint cursor composition
must derive them from the checked 1768-byte layout.

Accepted current attempts: ReaderFields-1 (4.584296790882945 s, 3666132992 B),
FlatSections-3 (4.620009125210345 s, 3668557824 B), WeightFields-3
(4.876395749859512 s, 3669622784 B), SemanticFields-4 (4.543316458817571 s,
3676241920 B), SectionContents-2 (4.679313125088811 s, 3663544320 B).
All exit 0, swaps 0 and standard axioms. Ops-3 is now current (the generic
comparison explicitly checks equal lengths before element comparison),
4.653885749634355 s, 3681533952 B, exit 0, swaps 0, standard axioms.
Dependent SemanticFields was rebuilt once after that source change.
Failed attempts and exact hashes, source revisions and axiom lines remain
in manifest.json and per-attempt receipts. No failed recovery proof counts.


## Complete successful output adoption

`CheckpointBytes4SuccessfulFields.successful_saved_fields` now consumes the
concrete callback instance through successful_fields and proves agreement of
all returned Prepared/Accumulator components with authentic C5 saved bytes,
including all 22 queries and the next cursor. It derives reserved=true.
There is no canonicality, decoded-output equality or allocation-availability
premise. Input `encoding` is saved-state/byte provenance. `next` is supplied
by the existing saved-ten recurrence theorem at the reached model boundary.
`BodyMatches` states explicit component agreements, not an opaque wrapper.

`CheckpointBytes4Comparison.ne_sound` discharges byte comparison soundness;
`successful_calls` consumes the existing source authentication-call theorem
with the concrete callbacks and comparison, producing all three digest call
witnesses and exact proof/public/checksum byte comparisons. No hash-collision
or digest correctness assumption enters the output theorem.

Verbatim established output theorem (this is **not** the requested final
source-stage observation theorem):
```lean
theorem successful_saved_fields (reserved : Bool) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (ck proof public1 : Slice U8) (hash : Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State) (stored pub : Bytes) (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K E)
    (encoding : bytesOf ck.val = encode H stored pub pm am) (next : am.next = 10)
    (success : verifier.resumeWithOps (ops reserved) D ck proof public1 .S2 hash = ok (.Ok (p,a))) :
    BodyMatches p a pm am ∧ a.next.val = am.next ∧ reserved = true
```

Accepted SuccessfulFields-1: exit 0, wall 14.171271875035018 s, peak RSS
3651141632 bytes, swaps 0, standard axioms. Accepted SavedFields-2: exit 0,
wall 6.228315291926265 s, peak RSS 3678453760 bytes, swaps 0; all four reports
standard. Accepted Next-5: exit 0, wall 5.123275457881391 s, peak RSS
3662970880 bytes, swaps 0, standard axioms. Further supporting targets and
all failed attempts have exact AGENTS.md formal-workflow section 6 fields
and full axiom lines in manifest.json. Failed diagnostic/elaboration results
are retained and excluded from accepted evidence.

## Final handoff: closed and remaining

Closed at the source-shaped/P6 callback-content boundary: a concrete
ResumeOps record, arbitrary-byte semantic and weight kernel refinements to
flat C5 decoding, emitted cursor composition, successful_fields consumption,
and complete successful returned-field adoption on authentic saved bytes.
The independent native scalar/semantic/weight/allocation/resize/Box content
gates from the preceding packet are reused; their source/harness audit
passed read-only in this packet. No native gate became a Lean axiom.
The actual frozen Rust/carrier/toolchain interpretation remains that explicit
P6 boundary; this packet is not a whole Rust extraction certificate.

**Item 3 is not established.** There is no proved final checkpoint source
stage theorem with exactly S2S10CallerBinding and S1S7S8StateProvenance, so
there is no honest verbatim final statement to report as proved. Neither
named premise has been manufactured or defined to carry observation equality.
The lead's success-conditioned AcceptedRunJoin ruling remains unchanged.

Concrete interface obstruction: `verifier.resumeWithOps` returns
`Result (core.result.Result (Prepared × Accumulator) Error)`, without an
oracle event trace. `Tx2ResumeDigests.Calls` certifies three callback calls and
their bound inputs/results, but its type has no event list or exhaustiveness
field. In contrast, `OraclePortCkptAbi5Stage.reached_stage` compares `eval` of
`Program Bytes State (Option (QueryAccumulator.State K E))` values, including
the complete ordered log. Thus successful_saved_fields/successful_calls
cannot be applied directly as its missing source observation. This is an
unproved effect/caller interpretation, not a counterexample to the desired
source theorem or a new cryptographic/availability premise.

Exact next deliverable/consumer: reify the source writer/resume's executed
Digest32 binds into an ordered oracle program, prove its successful trace
is exactly the writer's three calls followed by the resume's three calls,
and use successful_saved_fields for the returned-state transport. Bind source
proof/public/carrier identities through S2/S10 and authentic saved-ten state
through S1/S7/S8; then consume OraclePortCkptAbi5Stage.reached_stage through
strictStage and OraclePortCkptAbi5Decision.decision_observation to dV_frozen2.
Do not use an output-equality theorem as a substitute for that trace proof.

Only additive Lean and task tools/receipts changed. No shipped file, existing
Lean module, session A candidate, shared object, wallet or key changed. No
ELF rebuild trigger, host env J attempt, large build, full release replay,
push, merge, or 100-bit/security closure claim. No JSON >5 MB is included.
