# P-B batch port

Branch codex/cx-port4b-20261023; starting revision
986dc0bd7daf04ecd14cd0459585855277fef937. S2 OPEN.

Read the security/proof discipline, shared/local Lean rules, S2 ownership,
lead plan/diagnosis, route-B ruling, lead interface, PORTS3 row table and
VERIFIER-TOP. Paths without a root are under
`docs/research/100bit-spend-path-20261013/`; PORTS3 is at root design/.

Stage 1: inspected current batch Rust and installed emitted parent. The
emitted loop's nonzero-padding, excessive-count and verify-false paths return
`done (..., none)`; its wrapper maps none to Aeneas panic. Actual Rust returns
Parse or Merkle. This is a candidate error-lowering obstruction to exact
full-Result transport, not a shipped vulnerability and not a refutation of
an accepted-run-only port. Next isolate the error path in a small checked
module and retain the independent S2CallerFacts node-view/P6 construction.

No shipped changes; no ELF trigger. Inherited pins default f8c0ec72…,
devnet 63ad3e9c…, Pool 121f3e29… are not newly reproduced. No keys touched.
Host launcher has private Port4B objects, global lock (night window elapsed),
6G/8G/Swap0/Tasks64, 180-second timeout and aggregate reservation admission.
Budgets at stage 1: Lean 0/100; Kani 0/60. No release replay.

Stage 2: `Port4B_Rejection` proves that the two local padding-return
carriers differ and their shared emitted decoder gives panic versus Rust
Parse. `source-audit.json` pins the exact corresponding branches in current
Rust and emitted source. This is a local branch obstruction, not a proved
reachable complete native counterexample. Corrected full-error port requires
repair/re-extraction of those branches; accepted-only transport must separately
prove native child/effect/argument correspondence and retain rejected-query
prefixes in the surrounding security experiment. P6 sourceBatch returns Bool
and cannot retain the Parse/Merkle distinction without an additional carrier.

Attempt001 is EXCLUDED: an overlarge whole-parent normalization hit a kernel
memory ceiling after elaboration failed (exit1,11.684145461s,4507840KiB,
swap0). No cap was raised and it was not rerun unchanged. Replacement002
isolates only the pending-return branch: exit0,3.342520367s,4413180KiB,
swap0; all three theorem audits standard axioms. This does not give proof
credit to the failed whole-parent theorem or its recovery axiom.

Budget after stage 2: Lean2/100, Kani0/60. Exact targets, source revisions,
source/dependency hashes, limits, full errors and axioms are in lean-*/.

Stage 3: `Port4B_CallerViews.physical_views` derives all six physical views
and byte length bounds from the existing S2CallerFacts field.
`callerP6` retains the named three parent gates/leaf gate and installs
facts.oracle; `source_rows` gives complete log/Boolean equality to the
retained sourceBatch for either batch index. These do NOT identify native
op5 with that program. `Port4B_Cuts` derives batch0 from the SAME accepted
TX1 prefix and batch1 from SAME accepted authenticated TX2; TX2's p is
explicitly the SAME resume return. `Port4B_PhysicalCalls.tx1_slots/tx2_slots`
instantiate the ONE Port3_Parents dictionary and derive the three native
returns with original p.queries, p.roots[0/1], folded argument, and ordered
scratch threading, without an independently assumed batch success.

Final accepted stage3 targets006(cuts),007(views),009(physical calls):
exit0; wall5.317299104/5.377760920/4.706138669s;
peak4449116/4371040/4412584KiB; swap0; standard axioms only.
003 is an excluded missing-namespace elaboration;004 was the intermediate
views version before the helper's explicit axioms audit;005 is an excluded
reserved-identifier parser error. Full receipts retain every failure.
No theorem identifies Prepared roots/queries with parsed/model roots/queries;
that remains the exact S1/caller gate, as do native leaf/slot/verify effects.

Stage 4: `Port4B_NativeReject` now checks the ACTUAL installed loop body.
`missing_count` proves that a physical prefix read followed by node_count=None
is discarded as a missing pending return. `nonzero_padding` proves the same
for the actual nonzero-padding branch, from its precise local prefix/count/
slot/capacity/multiplication/suffix/chunks/any reads. `exit_loop` proves a done
branch is the whole emitted loop return, with no suffix calls. Together with
`Port4B_Rejection.padding_result_differs` and the literal Rust branch audit,
this identifies the exact erroneous error-lowering branch, rather than merely
comparing unrelated simplified models. It does not assert that the local
premises were derived from a complete admitted TX1/TX2 execution.

Accepted013: exit0,wall3.467134033s,peak4416680KiB,swap0; all3 audits standard
axioms.008 had a redundant tactic after completion;010/011/012 are excluded
parser/change/reduction failures, fixed by restricting unfolding to the actual
local branch and explicit reads. None timed out or hit a memory ceiling.
No failed recovery axiom is imported into a final module.

The requested exact FULL error-preserving native/candidate/P6 identification
is not available: the installed emitted branch differs from Rust and
sourceBatch's Bool carrier itself erases Parse/Merkle/failure distinctions.
Corrected forms: (a) repair/re-extract the explicit error returns and use an
error-preserving effect carrier for a total port; or (b) state accepted-only
native→sourceBatch log/true transport, with the named P6Boundary and exact
physical Prepared/query/root bindings. (b) remains UNPROVED here; rejected
query prefixes still require explicit treatment in the security experiment.
The checked independent batch cut and caller-node work above is retained.

Final focused union audit014: exit0,wall2.889572630s,peak4393552KiB,swap0;
all13 printed theorem axiom sets contain only propext/Classical.choice/
Quot.sound. No release claim or full frozen manifest replay. Final budget
14/100 Lean,0/60 Kani; no active proof job remains from this packet.
The one memory-ceiling attempt was isolated/replaced, never rerun unchanged.
The final static manifest checks source hashes against accepted receipts,
allowed axioms, fixed caps and absence of changed shipped/existing modules.

Assumptions: native leaves are still explicit Ops; P6Boundary parent/leaf
gates retained by name, and its oracle populated by facts.oracle. The caller
node-view premises are discharged FROM Required14, not a construction of
Required14 itself. No new axiom/trust item, whole-batch equality premise or
independent successful batch was added. Runtime/allocator/std/extraction and
source-to-artifact boundaries are inherited unchanged, not newly verified.

Remaining deliverable: repair the emitted rejected-return lowering (or state
an explicitly accepted-only port), then derive local native opening/packed-key/
leaf/dedup/count/padding/verify effects and physical Prepared/query/root
bindings to P6 from this same stage execution. Apply both_batches only after
that bridge; this packet's source_rows is deliberately not that bridge.
Target not yet established. No push, shipped change, ELF rebuild, key cleanup,
other worktree edit or other cone candidate change occurred.

Continuation ruling: the lead explicitly adopts accepted-only transport;
the panic/Parse rejection mismatch is outside AcceptedRunJoin's accepted
class. No total error-preserving transport or repair is pursued.

Stage 5: Port4B_AcceptedTail.verify_call inverts the ACTUAL installed
terminal loop iteration. It derives the successful native verifier return
on the SAME root, idx/val/d, counted index prefix and physical node prefix;
count, slot, capacity and prefix-range reads come from that iteration.
It introduces no independent successful verifier or model/log equality.
This is a local cut, not the full native-to-P6 row transport.

Accepted019: exit0,wall6.539460549s,peak4429032KiB,swap0,standard axioms
only.015–018 are excluded parser/elaboration failures; none timed out or
hit a memory ceiling. Budget19/100 Lean,0/60 Kani. All exact commands,
source revisions/SHA/dependency pins, caps and audits are in lean-015..019.
The night window has elapsed (clock21:42UTC); serialized host admission
continues, with6G/8G/Swap0/Tasks64. No shipped change or ELF trigger.

Stage 6: Port4B_Opening.opening_exact proves the source opening expression
with its release wrapping multiplications/additions and actual checked
range returns the exact832-byte physical opening on the admitted57607-byte
proof. selected composes packed_opening with that physical return for both
batch indices, including equal keys, without a separate successful view.
No op2 implementation or Parsed.wire provenance is silently inferred:
the explicit source expression and wire equality are in its statement.
Accepted020: exit0,wall4.014771419s,peak4398032KiB,swap0; both audits
standard axioms. Budget20/100 Lean,0/60 Kani.

Stage 7: Port4B_LeafCode proves exact physical leaf components, result and
one ordered digest read on every prefix log for an832-byte opening.
Port4B_LeafInstall fixes op2/op6 to these concrete local implementations;
selected_call binds the hash result and log to the SAME selected P6 leaf
address. Port4B_LeafStep proves the native post-hash duplicate/write control
agrees with extracted reference.leaf_step, including immediate duplicate
rejection and arbitrary untouched suffixes, under the local derived-room
obligation n<16. No duplicate-consistency assumption is used.

This is explicitly the existing P6 local leaf lowering, not new Charon
extraction: salt array-copy erasure is part of that cut. The static
leaf-source-audit pins opening/batch_leaf/private_leaf_hash bodies identical
to b2727acd3; it is not alone a source-refinement proof.
Accepted023/024/030: exits0,wall4.322253995/2.951521529/3.555093491s,
peak4395496/4413732/4437360KiB,swap0; all7 theorem audits standard axioms.
021's syntactic Code equality was false (pure step nodes remain in Code);
replacement023 proves erasure AND run observations instead.022 and025–029
are excluded elaboration failures;025 exposed shadowed do-binder codegen,
repaired with fresh names. No cap rise, timeout or memory kill.
Budget30/100 Lean,0/60 Kani. Full native-loop induction and terminal P6
count/padding/verifier carrier/effect transport remain before both_batches.

Stage 8: Port4B_NativeLeaf.active/step connect the proved post-hash updates
to the ACTUAL emitted body. Port4B_KeyDecode proves physical wrapping-shift,
cast and low-byte rebasing equal the packed-model projections. LeafCut.iteration
then binds the actual native body's return to the exact P6 referenceLeaf
result and SAME physical one-read leaf Code, with no whole-row equality input.
LeafLoop.accepted symbolically composes the native traversal: on acceptance
the entire P6 leaf fold succeeds with exact ordered reads (duplicates kept)
and leaves a success of the SAME native terminal call. Its key-stream and
wire equations remain explicit physical caller/child gates, not discharged.

TreeCuts.keys derives the raw builder, sorter and loop returns from the
accepted tree itself; terminal derives the actual done body from the same
terminal loop success. SortInstall fixes op5 to the P6 owned insertion sorter;
key_stream derives every sorted physical array read from its actual returned
array and the raw packed prefix. This remains P6 owned-control lowering, not
new source extraction or complete native batch transport.

Accepted032/038/039/042/045/048: exits0,swap0,standard axioms only; exact
wall/RSS/revisions and all theorem audits in their receipts.031,034,035,037,
040,041,043,044,046,047 are excluded elaboration errors (034's recursion-depth
simp was replaced by direct symbolic bit-vector/natural projections; no
options or resource caps changed).033/036 were admission failures before
Lean started, not attempts. Host checker now waits for other workers' Lean
processes under the existing capped serialized launch instead of aborting
admission. Actual budget46/100 Lean,0/60 Kani. No shipped changes or ELF trigger.

Stage 9: AnyFalse.all_chunks proves a false native any-scan reached EVERY
chunk and returned false from each actual predicate call. ByteWord proves
symbolic little-endian zero decoding; PaddingWord applies it to the ACTUAL
emitted padding closure and checked original bytes. Padding.native_zero
composes the actual chunks_exact iterator with these cuts, deriving zero
bytes for the complete divisible-by-eight suffix. No total scan/error
transport, fixed oracle answer, concrete large enumeration or memory-cap
change is used. CountInstall supplies a visibly named P6 count-lowering
adapter and derives well-formedness, exact binary recurrence and count≤288
from its accepted return; it is not a new extraction of shipped node_count.

Accepted052/059/060/063/064: exits0,swap0,all9 theorem audits standard.
Exact wall/RSS/revision/dependency/source fields are in their receipts.
049–051,053–058,061–062 are excluded local elaboration/proof errors;
none timed out or hit memory ceilings. The endian replacement uses one-bit
projection and casts, never normalizes arbitrary generated words.
Actual budget62/100 Lean,0/60 Kani (033/036 never entered Lean).
Whole terminal count/padding/verifier composition, concrete key builder,
Prepared/model provenance and final accepted batch join remain unproved.

Stage 10: SlotInstall.physical/caller bind the installed P6 slot-offset
lowering to exact proof ranges and then to the SAME Required14 node buffer.
TailReads.reads derives the complete native count/capacity/suffix/chunks/
scan/prefix/verifier sequence from its accepted terminal body, including
returned arrays and no independent scan success.
VerifyInstall normalizes the P6 owned verifier to its exact extracted
wrapper; wrapper_success derives height success and every root/cursor guard.
VerifyRun.accepted then derives the complete physical/P6 source return and
SAME arrays from the installed owned verifier's success, retaining the named
P6Boundary. SliceReads derives native prefix bounds/contents and exact live
indices; Capacity.read checks the six physical table entries.

These new adapters are explicitly P6 local source/library/control lowering,
not a claim of fresh extraction of shipped slot/count/verifier functions.
The requested enclosing native batch/sourceBatch join still is not claimed.
Accepted066/068/071/075/077/078: exits0,swap0,all15 audits standard axioms;
exact wall/RSS/revision/dependency fields in receipts.065/067/069–070/
072–074/076 are excluded local parser/elaboration errors, no timeout or
memory kill. Actual budget76/100 Lean,0/60 Kani. No shipped edits/ELF trigger.

Stage 11: TailRun.accepted composes ALL actual terminal reads, accepted-only
padding, exact count/slot/prefix carriers and P6 verifier return into the
complete P6 tail on the SAME scratch. TreeJoin.accepted composes the native
leaf traversal and terminal tail, retaining ordered leaf requests followed
by every verifier request and the same output arrays. No whole-tree success/
observation agreement is assumed. PackedKeys is a VISIBLE remaining LOCAL
raw-builder gate; root/wire provenance is also explicit. This conditional
tree result does NOT discharge the concrete batch row.
Prepared.roots/query_value project exact physical root arrays and canonical
query words from existing SAME-Prepared BodyMatches, with no modulo weakening
of raw queries. Existence of that provenance from the accepted TX1/TX2 cuts
is still an upstream binding obligation. Bounds checks actual split and
slot arithmetic symbolically.
Accepted080/083/085/086: exits0,swap0,all7 audits standard; exact command,
revision, wall/RSS/source/dependency fields in receipts.079/081–082/084
are excluded local parser/elaboration errors. No resource failures, no cap
changes. Actual budget84/100 Lean,0/60 Kani;033/036 never launched Lean.
No shipped file, key, ELF, other worktree or sibling cone was changed.

Stage 12: BatchJoin.accepted composes the THREE native slot returns into
sourceBatch with exact ordered logs, physical roots/queries and scratch.
KeyInstall supplies the explicit CANONICAL REACHED P6 owned-key lowering;
queries_bound derives canonical numeric binding from the SAME BodyMatches,
and packed discharges PackedKeys for that installation. Install.leaves fixes
EVERY child; installation proves no free base child survives the native
parent's Std installation. These remain named P6 source/control/library
lowerings, not newly extracted shipped helper bodies.

CallerJoin.accepted instantiates nodeViews, proof length and oracle directly
from Required14, consumes the actual physical Prepared/model fields and
applies P6 both_batches. FoldedCut.tx1/tx2 derive the original native folded
range/copy and batch success from the SAME accepted TX call; model discharges
the folded-root model input without hash equality or another read.
PrepareCut.tx1 additionally preserves the SAME prepare success and zero
input. StageRows.tx1/tx2 connect these same-execution cuts to the row, keeping
only explicit S1 PreparedBinding on that actual prepare/resume return, plus
caller parser/model provenance and the named P6 boundary. No independent
successful batch, reader, root, height or observation equality is assumed.

CRITICAL SCOPE: the concrete S1 PreparedBinding instance is NOT proved here.
It is a source-refinement obligation, not a cryptographic assumption, and
must be instantiated on the actual native prepare/resume children before
claiming the requested unconditional concrete row or global AcceptedRunJoin.
Likewise, explicit P6 source/library/control lowering is not a new Charon
extraction or ELF refinement. Target not yet established.

Accepted087/088/089/090/092/098/101: exits0,swap0,all16 theorem audits standard;
exact target/revision/source/dependency/wall/RSS fields are in receipts.
091,093–094,096–097,099–100 are excluded parser/elaboration attempts.
095 was voluntarily stopped on a non-progressing tactic branch: exit143,
37.060865915s,peak5332780KiB,swap0; source was changed to guarded single
pair decomposition and split helpers before the successful098. No cap was
raised, and no timed-out/memory-killed job was rerun unchanged.
Actual budget99/100 Lean,0/60 Kani (033/036 never started Lean).

lowering-audit.json statically pins six unchanged local Rust cuts and the
inherited successful cone4-keys-1 receipt. No Kani replay, source adoption or
new ELF measurement is inferred from body identity. No shipped files changed;
inherited default f8c0ec72…/devnet63ad3e9c…/Pool121f3e29… remain historical.
No keys, other worktrees, sibling candidates, source features or parameters
were changed. All substantive stages are committed locally; no push.

Final focused union102: Port4B_Final.lean, exit0,wall3.313747665s,
peak4402668KiB,swap0,source revision6c5d5298b2 (full revision in receipt).
All16 final top-theorem audits use only propext/Classical.choice/Quot.sound.
The final log also prints the exact installed leaves, PreparedBinding,
CallerJoin and both StageRows statements, so the remaining premises are
reviewable. All40 final module source hashes match successful receipts.
No frozen release manifest, adversarial/runtime suite or ELF rebuild was run.

STOP:100/100 ACTUAL Lean compile attempts exhausted;0/60 Kani runs.
Reserved033/036 never launched Lean and are not counted. The one voluntarily
stopped search095 was source-changed before replacement; no resource cap was
raised. Every actual attempt has its exact command/source/dependency/revision,
exit/wall/RSS/swap/cgroup/axiom record. All accepted modules contain no proof
holes or nonstandard axioms. No active job remains from this continuation.

Final handoff: use Port4B_StageRows.tx1/tx2 with the fixed Port4B_FoldedCut.install
batch-related caller leaves and Port4B_Install.leaves batch children. Their
prepare/resume source contract must establish PreparedBinding for the SAME
returned p; wireStored and model roots also remain explicit caller/S1
provenance. Existing P6 source/control/library adoption stays named, with
owned canonical key/count/slot/verifier lowerings clearly distinguished from
fresh native extractions. Instantiating those concrete source bindings is the
next deliverable. This packet does not construct global AcceptedRunJoin or
establish the security/release target. No push or shipped/artifact/key changes.
