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
