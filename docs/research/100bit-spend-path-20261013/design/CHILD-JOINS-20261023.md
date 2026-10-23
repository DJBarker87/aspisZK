# Child join instantiation audit — 23 October 2026

Status: requested premise removal is obstructed by the actual interfaces.
Target not yet established. Branch `codex/cx-child-joins-20261023`, initial
revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. No shipped files changed.
The rule to stop an ill-typed or false item applies; no replacement assumptions
are silently installed. Receipts: repository-root `evidence/child-joins-20261023/`.

## Stage 1: checkpoint

Requested before: remove `CheckpointWriterConeJoin` and
`CheckpointReaderConeJoin` from `S2W_D189Consolidation.accepted_run`, retaining
`S1S7S8StateProvenance`. This removal is not established.

Actual writer fields (`S2W_AuthenticatedInputs.lean`): for every successful
`AdapterRw.first_decoded ops semantic pub proof split`, the returned bytes have
length 1768 and `decode bytes = some (H proofBytes,H publicBytes)`.
Actual reader field: successful `ops.op11 ... pub proof checkpoint () none`
implies that same header equation on its input checkpoint. `decode` is an
arbitrary `Bytes → Option (State × State)` parameter of accepted_run's returned
continuation. Neither concrete serialization nor child lowering is installed.

`CheckpointBytes5Join.success_conditioned_checkpoint_stage_join` instead
consumes successful execution of its own `stage`: writer then resume, same
proof/public arguments, explicit prepared/accumulator provenance. It produces
an ordered observation and interpreted returned state. It mentions neither
adapter `ops.op11` nor `HeaderDecode`. `CheckpointBytes5Decision.decision_success_join`
then inserts that observation into the reached model decision; its additional
parser/query/input/view/guard/batch-success context remains explicit. It does
not prove either adapter header field.

The caller binding really is discharged *once facts exist* by the existing
`S2LeadInterface.checkpoint_binding`, using `proofBytes`, `publicBytes`, and
`checkpoint_oracle` from the total oracle law. `S1S7S8StateProvenance` remains
named and unchanged. This downstream discharge supplies no upstream adapter
child instance: accepted_run itself needs both checkpoint joins to derive
those facts (via authenticated_inputs and P2Prime).

`ChildJoin_CheckpointObstruction.reader_none` and `.writer_none` retain an
actual successful invocation and prove that choosing `decode := fun _ => none`
precludes the corresponding join. Thus even perfect saved-state provenance
cannot imply the requested joins for the presently unconstrained decoder.
This is an interface obstruction, not a shipped checkpoint counterexample.

Validation: `ChildJoin_CheckpointObstruction.lean`, attempt lean-001, exit 0,
2.252 s wall, 4,386,668 KiB peak RSS, zero swaps. Both theorem axioms are exactly
`[propext, Classical.choice, Quot.sound]`. Exact command, source hashes, selected
object hashes, source revision and cgroup settings are in its receipt. Historical
cached imports were reused; this was not a coherent H5 dependency rebuild.
