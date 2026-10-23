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

## Stage 2: multiproof and S8

`MultiproofConeFrozen2Stage.both_batches` takes six byte-view equations and a
total digest-oracle law, and returns success-conditioned equality of both
batch observations. It does not return `S2Y_OwnedChildren.NodeRanges`, the two
fields of `S2W_ChildJoins.MultiproofConeJoin`. These fields quantify actual
checked Slice.index calls with bounded start/end, on each proof carrier.
The consumer direction is `internal_geometry` → nodeViews → both_batches.
Reversing this direction would require an independent source range theorem.

`ChildJoin_Geometry.batches_from_facts` explicitly applies exactly
`MultiproofConeFrozen2Stage.both_batches`; it discharges the six view equations
and total digest law from `facts.nodeViews` and `facts.oracle`. This is a
valid downstream observation theorem, not an upstream cone instantiation.
The stronger callback-aware theorem is already `S2LeadInterface.multiproof_join`:
it retains the named `MultiproofConeP6Frozen2Stage.P6Boundary` and replaces only
its oracle field from facts. Total oracle interpretation and P6 physical
lowering are still trust/refinement obligations of the actual source; neither
is established by proving a physical input view equation.

`S2W_ChildJoins.S8StageConeJoin` contains only `Y1Range`: length ≥7495 and the
actual Slice.index result at [7031,7495). It has no EbyKDot or finish field.
`S8JoinFrozenScan.parsed_y1` returns scan success on a constructed segment;
`S2Y_ChildGeometry.y1_scan` consumes the actual range call to identify y1 with
that segment. `ChildJoin_Geometry.scan_short` proves the join impossible for
short inputs; `scan_unique` proves its y1 argument uniquely determined by the
physical call. The arbitrary `y1` quantified in accepted_run cannot be filled
from a field arithmetic theorem.

The separate arithmetic endpoint `S8P6ReturnedFinish.stage_observation` retains
`Caller` (returned raw/destination storage representation), and its final dot
is explicitly a field reference. Its source comment states that adoption of
finish_query_dot/finish_relation is open. It supplies no EbyKDot source
certificate and no physical slice index. Therefore neither this theorem nor
the model finisher laws can instantiate this S8StageConeJoin.

Validation: attempt lean-002 failed at type elaboration because the digest
namespace was not open; its error-generated sorryAx is excluded evidence.
Source changed by opening AspisR1Stage2. Attempt lean-003 passed: exit 0,
2.077 s wall, 4,385,932 KiB peak RSS, zero swaps; all three new theorems use
exactly `[propext, Classical.choice, Quot.sound]`. No unchanged retry occurred.
