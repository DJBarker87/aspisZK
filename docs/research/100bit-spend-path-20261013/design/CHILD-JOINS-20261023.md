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

## Stage 3: current source pins and composition boundary

`source-pins.json` compares eight relevant current files with S2's recorded
snapshot `544d40b596017f5b1d9644dd19acab0cb5f98a7d`.
`function-pins.json` records 269 declaration spans with before/after hashes,
line locations and changed flags (duplicate method names use occurrence ordinals).
These are source inspections, not source-to-model proofs.

Unchanged files: compact.rs, multiproof.rs, verifier.rs and the SDK adapter
r1_pool_adapter.rs. Thus the inspected checkpoint, resume, scan and multiproof
bodies have no direct H5 delta against that snapshot; transitive dependencies
still require assessment. Changed files: weights.rs, fast_pairing.rs,
state_only_prefix.rs and owned adapter require_zero. Every changed declaration
is explicitly marked in the machine-readable inventory. No source theorem
from the old snapshot is asserted to bind all of H5.

Current canonical Q::from_limbs destructures [a,b,c,d], checks four ordered
strict bounds, and returns Some(Self([a,b,c,d])) or None. It is unchanged
against the post-S4 S2 snapshot. The historical freeze b2727acd instead uses
x.iter().all and Some(Self(x)); that old body cannot be re-pinned by name.
The isolated S4 checked-q source-cut also differs textually in its returned
array expression and formatting, so no byte-identical extracted source claim
is made here. Current checked_q uses explicit match on this constructor (H5
changed the former ok_or call). EbyKDot::push and EbyKDot::finish themselves
are unchanged against the S2 snapshot; canonical Dot::push/Dot::finish, raw,
reduce and reduce_pair are changed reachable bodies. Current EbyKDot::finish
constructs E from eight reduced limbs and unwraps; the existence of a model
finisher theorem is not its H5 arithmetic or panic-freedom certificate.
`state_only_statement_points` changed to explicit complement writes. The owned
adapter's require_zero changed to a tail loop; all other inspected owned
adapter function spans are unchanged. Existing scanner equivalence is reusable
only under its exact source/extraction qualifications, not as whole-caller closure.

The requested stronger theorem would be:

> Under native/runtime/trust admission and the remaining child premises,
> an accepted native wrapper pair yields one execution-indexed observation
> with S2CallerFacts AND the checkpoint, multiproof and S8 joins.

This is **not proved**, and no Lean declaration claims it. The exact currently
available theorem remains `S2W_D189Consolidation.accepted_run`:

> accepted wrappers + SDK/std/extraction/runtime/oracle/event admission yield
> cuts and one execution, whose continuation takes writer, reader, protected
> checkpoint history, P2Prime, first-entry parser, physical node-range and
> physical y1-range joins, then yields parsed and S2CallerFacts on that observation.

The new downstream batch theorem can be applied after that continuation;
checkpoint_binding then discharges S2S10CallerBinding. Neither removes an
input needed to construct the facts. Before/after quantifiers, carriers and
success conditioning are unchanged in the proved downstream theorem; no
premise-removal claim is made.

Remaining named work:

- Lead-owned actual writer serialization/header parser and resume digest-check
  correspondence for the fixed ops calls, including writer length; independent
  physical node and y1 range observations for the actual reached calls.
- S1S7S8StateProvenance for the checkpoint stage; reached model context and
  success of that stage must be tied to the same actual calls.
- Session A's FirstEntryVerifierConeJoin. FullForestAcceptedRoundtrip remains
  a separate session A source theorem, but is **not a premise of accepted_run**:
  its comment explicitly says the stronger authentication route avoids it.
  Do not add it to this theorem or claim it discharged.
- S2TrustedSdkBorrow (all named fields), TrustedStd copy semantics,
  AeneasExtraction, Allocator, both RuntimeEntrypointAdmission instances,
  RuntimeSyscall, P1, P2Prime and CheckpointVersionBinding; ChildConeJoin erasure
  and FirstMarks/SecondMarks; P6 total oracle/callback/lowering and P7/compiler,
  runtime/ABI/allocator and current source-to-ELF correspondence.
- H5 actual EbyKDot/finisher arithmetic and constructor/dependency binding;
  full frozen headline/security experiment composition, including rejected
  oracle-query prefixes. No 100-bit conclusion follows from this packet.

Next concrete deliverable: a fixed-invocation actual checkpoint codec/header
parser and ops lowering theorem, proved without S2CallerFacts, followed by
physical range theorems on the same child calls. Then feed these into
accepted_run; only afterwards consume facts in checkpoint and batch stage joins.

## Validation, frozen target and resource receipt

Final focused union: `ChildJoin_Audit.lean`, lean-004, exit 0, 2.195 s wall,
4,378,464 KiB peak RSS, swap 0. It imports both new modules, audits all five
new top theorems, and prints the actual required/consumer statements. All five
final axiom sets are exactly `[propext, Classical.choice, Quot.sound]`.
Budget consumed: **4/100 Lean compile attempts, 0/60 Kani runs**. One elaboration
failure retained/excluded, three green attempts. No timeout or memory kill.

Every attempt used `lake env lean -j1 -M4400 -DElab.async=false` on the host,
in its own scope with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, plus populated-scope reservation below 55 GiB and the shared global
Lean lock (the observed time was outside the 14:00 UK parallel window).
Own objects live only in the isolated child-joins host directory; inherited
caches were read, not overwritten. Full command, toolchain binary hash,
selected import object hashes, exact dirty-source hashes, source revision,
wall/RSS/swap/limits and full axioms output are committed per attempt.

No Rust/Kani/ELF build ran; no shipped source changed. Therefore the conditional
three-ELF rebuild trigger did not fire. Requested historical pins remain
recorded as default d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0,
devnet 2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922,
Pool 121f3e29…; these were **not rebuilt or re-confirmed for H5**. Current
H5 adoption/source and historical compiled artifacts remain distinct. No
wire/parameter/feature/security-contract change was introduced (stored suffix
57607 bytes, checkpoint 1768 bytes, y1 [7031,7495), two batches of three slots).
No existing Lean module, session A candidate or other worktree was edited.
No whole frozen manifest or release-security replay was warranted by these
obstruction/model-only modules. `git diff --check` passed.

## Lead continuation: fixed C5 decoder

`ChildJoin_Decoder.checkpointHeader` now fixes the digest header interpretation
to C5 byte fields `[16,48)` and `[48,80)`, each decoded as a 32-byte State.
It deliberately decodes those two fields only, as required by HeaderDecode;
frame/checksum validation remains the executed reader's responsibility.
`encoded_header` proves its result on every `OraclePortCheckpointAbiC5.encode`.
`ChildJoin_Accepted.accepted_run` specializes the complete native accepted-run
theorem to this decoder, including the full Required14 conclusion. The original
module is untouched (new-modules-only rule); consumers should use the new
entry point. All other quantifiers, success conditions and remaining child
premises are unchanged. This closes the free-parameter item, not a child
source-refinement obligation.

Validation: lean-005/006 were local theorem-elaboration failures (retained,
excluded); lean-007/008 pass. Each host attempt uses lake env lean, -j1 -M4400,
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Receipt JSON contains
exact target, revision, source/dependency hashes, wall/RSS/swap and complete
axiom lines. New top theorems use standard axioms only. Historical imports are
reused, not claimed to be a coherent H5 release replay. No shipped source or
artifact changed.
