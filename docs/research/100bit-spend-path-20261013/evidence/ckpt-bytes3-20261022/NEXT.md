# Next checkpoint source consumer

Closed: exact-width extracted scalar Result identification with C5 (K=16,
E=32), all successful outputs and canonicality rejections; explicit source /
reference Prepared and Accumulator transport; bounded raw/decoder reader
composition; typed fallible allocation content. Five independent native
operation gates pass for semantic reads, 64-weight reads, filled, resize and
boxed Prepared content. See STATUS.md, manifest.json and kani/ receipts.

Not closed: the concrete complete AspisR1Stage2.ResumeOps source instance,
its kernel semantic/weight content refinement, application to
OraclePortCkptAbiSourceFields.successful_fields, or source adoption through
OraclePortCkptAbi5Stage.reached_stage / strictStage into
OraclePortCkptAbi5Decision.decision_observation / dV_frozen2.

Resolve the final source theorem's error scope: actual successful resume can
derive allocation success, whereas authentic source Allocation failure has
no matching branch in strictStage. Do not assume physical availability from
Kani's --no-malloc-may-fail content checks, or hide an observation equality
inside S2S10CallerBinding / S1S7S8StateProvenance. An explicit two-premise
source theorem still must be written and checked; no final statement has
been manufactured for reporting.

Exact next deliverable: construct the operation instance using
CheckpointBytes3Reader, the checked semantic/weight source helpers and typed
allocation outcome; prove section content using C5 decoder identification;
apply successful_fields with CheckpointBytes3Namespaces; then make the
source-stage join preserving all six ordered digest reads.

Recheck without replaying any proof:
python3 -B tools/ckpt-bytes3-20261022/audit.py

No shipped source changed; no frozen ELF rebuild trigger. No host env J
attempt, push, merge, local target, wallet cleanup or release claim.
