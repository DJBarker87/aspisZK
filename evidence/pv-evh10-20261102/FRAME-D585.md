# D585 — concrete FRAME interface and consistency

Base c1841dddedf6a01ccfdf314a7d06b751fa3cb676, same worktree and branch.
Label: **binary-structural (adopted binary), plus V370 compiler-cohort**.
Adopted SHA256 da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0.
This formalizes the FRAME slice. It neither defines nor imports OWNER.
No new T field, source implementation change, or whole-client L3 claim.
D584's correction is accepted: stack lifetimes/activations are not Vec/RawVec
allocator ownership. D583's OWNER-only reduction stays withdrawn.

## Concrete interface

`PV_EVH_PhysicalFrame.Frame` has data fields for sp, activation, retry,
iteration, phase, slotTable, offsets, lifetimes, activeFrames, request, answer.
`SlotId` distinguishes six entropy slots and mask/Result storage in each of
eight retry frames. Each Slot carries its address, extent and activation /
iteration lifetime. Different slots have distinct identities even when their
lifetime metadata agrees. Retired bytes and registers are not erased or
removed from physical observation by ending a lifetime.

`Grant` gives a post-answer interval, nonwrapping bound and writable predicate.
`StackAnswer` retains pending, granted and exhausted-with-actual-Fault.
`ResourceReply` carries before/after source/native State and ordered events.
`FrameWorld.resolve` requires its before State equal this prefix's State and
passes its after State/events onward verbatim. Exhaustion returns that Fault
and stopped phase; pending does not enable the initializer. Grant is resource
readiness, not entropy success or a promise of all future accesses.
The public stack limit is request data, not an always-grant premise. Enforcement
and actual mapping/resource transitions remain the world's resource semantics.

## Physical and source correspondence

| Component | Lean interpretation | Adopted binary/source binding |
|---|---|---|
| Entropy reservation | 232 bytes at actual sp | six pushes/sub232; initializer 0x1457ef |
| Original | inner0: [sp,sp+64) | four zero SIMD stores; existing sourceOriginal |
| Field / seed | inner1/2: [64,96),[96,128) | sourceField/sourceSeed; first/second original halves |
| Return staging | inner3/4/5: [128,160),[160,192),[192,224) | D581 interleaved return staging; no erasure inferred |
| Current caller mask | mask0: [sp+304,sp+336) | c=sp+288; retry c+16 |
| Current Result | result0: [sp+352,sp+449) | retry c+64; 97 success-initialized bytes |
| Older retry slots | add 336*i | two outgoing pushes + return8 + saved48 + local264 |
| Callback | no added frame | inlined 0x5c9bb..0x5ca02; entered increment |
| Retry chain | k+1, k<8 at entropy | source ATTEMPT_CAP=8; recursive Rejected edge |
| Entropy backedge | iteration increment, same activation/sp | 0x1458e1..0x1458f1; limit16 |

The Result extent is the success-store footprint, not inferred allocation
padding or a claim that every Err initializes 97 bytes. The numeric table is
an envelope: its separation theorem covers even inactive/uninitialized slots.
`PhysicalFrame.live` is a conservative phase summary, NOT an exact source
live-list decoder for older caller Results. In particular, its caller indices
must not be used to infer which earlier Result bytes are initialized. The
source bridge below relies on the stronger all-table geometry and does not
use that coarse predicate. Exact per-path Result tags/liveness and register /
spill correspondence remain in the paired source/machine interpretation.

`FrameSource.EntryView` is an interface projection of the fixed
ActualEntropyEntryPrefix, **not a newly fabricated actual-run domain**.
Its physicalMemory is the same State.memory; no second memory or empty heap
is invented. `source_slots` identifies the prospective original/field/seed
admission descriptors with the physical table; beforeInit does not assert
that their secret lifetimes are already initialized/admitted.

`FrameSource.Correspondence` explicitly takes ActualEntropyEntryPrefix as its
carrier parameter, with the SAME base/heap/box/ops binders. It carries the
source State/mask/retry/limit selectors and equations binding State, retry,
limit16 and mask bytes at sp+304. `sourceBody` indexes the original extracted
loop body at EXACTLY opsNative (rawBase base) heap box ops. It supplies no
helper Result or success continuation. No field assumes slot separation.
This is an implemented, typechecked interface, not an implementation of the
full actual source/machine prefix producer or an inhabitant of Correspondence.
Those equations must be supplied by that producer; they are not discharged
by naming the interface or by OWNER. Actual-domain non-emptiness is unproved.

## Checked consistency and preservation

`offsets_separate` proves all distinct table slots disjoint, symbolically;
`table_separate`, `live_nonoverlap`, `shape_consistent` and `entry_consistent`
derive consistency without a separation field. `retry_prefix_shape` proves
frames=k+1 and k<=8 on the structural rejection history. Its entropy guard
implies <=8 retry frames; cap-check k=8 has nine and cannot call entropy.
The named active spine including plan+entropy has <=10 activations at the
initializer. The eight bound does NOT mean eight total client frames.
`spine_displacement` proves 2976 below plan / 24184 below plan entry.
`chain_frames_separate` proves disjoint retry reservations.

`iteration_preserves` / `iteration_fresh` preserve geometry/active chain while
changing local lifetimes at reused numeric addresses. `callback_preserves`
proves the inlined callback's call/return frame projection does not grow the
stack and increments entered. It does not prove callback value semantics
(the allocator/callback slice remains separate).
`rejected_lifetimes` joins the backedge to existing checked source cleanup's
key-freshness theorem. `FrameWorld.nextEntry` consumes that cleanup's actual
post-State, resets the pending resource answer and retains sp/chain/slot
addresses; `next_entry_preserves` proves its source-key freshness and separation.
`preserved_spine` checks loop/callback invariants simultaneously.
The cleanup's native write/barrier history is retained by the existing source
law; this frame projection does not assert these operations silent.
Temporary zeroize leaf calls, signals, other threads and older client callers
remain in the full machine history; no global stack-footprint theorem follows.

## Evidence and exact remaining boundary

Focused compile receipts and all #print axioms are in frame-D585.json.
Axioms are **SUMMARY-BASED**, only propext/Classical.choice/Quot.sound in
accepted modules; no raw/full-data release audit or coherence claim.
The immutable D581/D583 disassembly certificate is reused and checked once
for the new Lean correspondence; no new binary/native run. No full manifest
or unchanged regression replay. Failed sources/receipts are retained without
credit and were changed before retry.

The actual producer must still provide Correspondence over the unchanged
paired full-entry domain, including all resource/fault/divergent prefixes and
exact mask/state equations. It must also bind all source live slots and
active identities to the same process history (including spill/copy channels),
then combine FRAME with the separately supplied allocator interface. This
resume does not claim actual_frame_entry for all actual prefixes, all heap /
old-live exclusion, full advancing entry, or five-projection installation.
Endpoint/deployment rows removed NONE; T unchanged; target not established.
V370/L3, same-prefix kernel/world association, V400, D520/U/D524,
NativeObstruction62/op132 and L1/L2/L3 remain. This is concrete interface and
local stack proof progress, not premise-removal credit for an uninstantiated
actual correspondence. No keys/accounts/funds operation.
