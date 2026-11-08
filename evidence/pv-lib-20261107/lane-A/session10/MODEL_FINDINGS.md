# Session10 — destructor/count composition support; PARTIAL

Base 0f651b565341f0dba8390dbbe234ce523d74f080. Requested completion is NOT
achieved. Target not yet established. Endpoint premises removed0/added0,
new T fields0, row closures0 and slot-status changes0. No implementation,
frozen spec, ledger, checker, row consumer or Lane B file was changed.

## Checked unit-construction obstruction and replacement

DestructorValues10.original_unit_missing proves that the original entry carrier's
DIRECT aggregate operation cannot construct unit. WeakOwnerFree10.original_poll_gap
therefore proves the session9 poll is undefined on that carrier, independently
of whether allocator/backing exists. This is a MODEL gap, not a Rust defect.
Session9's abstract-carrier poll lemmas remain valid, with their stated unit
premise; they did not establish an original-carrier free call.

DestructorValues10.carrier reuses PV_THR2_AggregateCompletion.carrier, the SAME
fallback already used by the original source Execution. WeakOwnerFree10.step
makes it available at native destructor/Cell/free boundaries as well. Pointer,
field, replacement and constant operations are unchanged. Existing literal thin
metadata stays null. This is source-value interpretation, not initialization of
physical memory. All old modules are retained, not edited.

WeakFreePoll10.graph gives the actual original-carrier poll with no extra unit
existence/success premise: allocator absence and backing absence remain explicit
gaps; otherwise every free-resource answer goes to the old exact sourceReceive.
last_step composes the source decrement and that poll once, locally. It still
requires local selection/begin facts; it is not a completed last-strong theorem.

## Actual584/661 source prefixes and borrowed allocator

WeakGuardBuild10 checks each of584's first8 instructions. Its guard is read from
the ACTUAL node7 aggregate: [Arc.ptr, reference(Arc.field2)], with its actual type
metadata. Source Arc values use the provider's THREE-field
PV_THR2_Packet315SourceReturn.value, and its allocator uses the existing
PV_THR2_Packet218ReturnData.allocator. WeakGuardBuildRun10 derives the borrowed
Global allocator read from that value and the generated guard, rather than
assuming allocator/read/count facts at683.

WeakGuardSource10 calculates all6 instructions of661 up to ISSUING683. It checks
both the saved request and exact source-store writes, and frames roots outside
the661 and fresh683 activations. WeakGuardCorrected10/WeakGuardPrefix10 and
WeakGuardBuildRun10/WeakGuardBuildPrefix10 compose these prefixes on the repaired
OWNER-aware free step. DestructorStep10 uses the existing OWNER registration,
operator and intrinsic neutralities BY NAME; resources and intrinsic stack stay
identical. FetchSubPrefixes10 revalidates BOTH prefixes on the latest snapshot
machine. It does not transport across an unresolved native action.

Qualifications: these are destructor-entry LOCAL results. The actual original
caller reaching each entry, its provider value and the local root/activation
inequalities still have to be derived in the full486/584/payload history. No
such read/inequality was inserted in a row Pre, MachineSpec or endpoint. Arbitrary
T is retained in the prefixes, but its destructor/callback effects are NOT proved.

Payload24810 reads584's ACTUAL23232 call and resolves the SpawnHooks
specialization to nonempty608 with the same pointer/action/cleanup. That is one
checked specialization, NOT arbitrary-T or dynamic callback adequacy. No-op
replacement of unresolved T remains forbidden.

## Source Weak pointer, both count branches and write-definedness

WeakCount10 uses the provider's exact ArcInner aggregate kind and
PV_FN_THREAD_f360Outcomes.atomicValue. Its read_count and write_count DERIVE
numeric reads and nested write-definedness, preserving every sibling and tag;
no desired-write or post-Store premise is used. The payload is arbitrary, so it
need not be a still-initialized T. allocated calculates the wrapped subtraction
and selects deallocate iff old=1, otherwise done (zero/underflow is retained).
GuardWeakBegin10 derives this same begin graph from584's generated guard and the
source NonNull pointer. Its LOCAL source-root/pointer facts still need the
actual constructor and payload frames in the complete history.

This does not finish the SOURCE/OWNER correspondence through arbitrary payload
Drop. Existing ProviderBacking9, FreeLifetime9 and registry/frame lemmas are
reused only as their qualified local results, never as a full adequacy claim.

##581 returned old value and pending snapshot

The earlier table subtracts the source count but delivers the backend's
arbitrary success payload. That alone cannot identify486's last-strong branch.
ArcDropBinding10.corrected_old_one checks the local obstruction: old1 versus
arbitrary backend2 choose different Ne branches. It is NOT a shipped-code
counterexample or a claimed complete original-machine execution.

ONE new named interpretation is
PV_LIB_A_FetchSubReply10.PV_THR2_LibrarySemantics_FetchSubValue581:
AtomicUsize::fetch_sub returns the pre-subtraction value. The pinned Rust1.94.1
core source is session5/core-src-sync-atomic.rs.xz, raw SHA256
66a878ab38a69f39375cf52e0f4f2c62a03fe487b4baa6ebecf3e30f87d904b2;
method3261–3264 calls atomic_sub(self.v.get(),val,order), and its preceding
contract says it returns the previous value. The exact emitted581 token is read
from486/21732. This is a thread16/library P interpretation for Recount14,
NOT a T field, endpoint premise or Rust intrinsic/compiler correctness proof.
Those existing compiler/source-association obligations remain retained.

The interpretation fixes ONLY the successful returned value. Failure/divergence/
fault/pending, world and events are retained. FetchSubSource10.same_write proves
it cannot change the source subtraction on ANY answer. Source readOld uses the
actual addressed AtomicUsize.v.UnsafeCell.value, before sourceStart.

FetchSubMachine10 adds an ephemeral (original waiting request, old count)
CONTROL snapshot. Initial selection is exact581, with emitted inline bodies
excluded by sourceSelect. Pending retains the snapshot; retries validate the
same wait/action and use the saved old value WITHOUT another source read or
subtraction. Missing/mismatched snapshots are gaps, never arbitrary successes.
FetchSubRetry10.graph/pending/begin check the full retry/initial graphs. The
ordinary/source-prefix agreement is symbolic and preserves the identical OWNER
free/resource channel. It does not establish full arbitrary native effects.

StrongCount10 derives the strong-field read, write and snapshot from the
provider AtomicUsize/ArcInner representation and ties selection to actual21732.
The local native program-table classification must be discharged from the
actual resolver when composing the full486 run. ArcDropCompare10.delivery uses
the old source return administration to write that old count into actual local3;
compare calculates actual21735 Ne into local2; source_branch retains both
actual21826 alternatives. Numeric Ne is a source builtin interpretation, not a
native effect. ArcDropBinding10 pins both destinations to the actual nodes.
No counter equality across a callee interface is asserted.

## Import surface and remaining order

Import PV_LIB_A_StoreActionTable10 for v2DestructionPrograms10,
v2DestructionStep10, v2DestructionEntry10 and DestructionState10. The named
originalDestructionCarrier10 adds the numeric comparison to the existing entry
carrier. Legacy PV_LIB_StoreActionTable.v2 stays unchanged/importable. This new
surface is PARTIAL, not a declaration that D984 or any caller row is complete.

FIRST continue the complete486/584/248/661 composition: actual222/320 entry and
full return; initial581 source subtraction/value capture/delivery; both486
branches and fence; actual584 payload248 effects and nonempty/dynamic T cleanup;
implicit guard entry; source/count/borrowed-allocator/backing frames through
those effects; both683 branches and every free reply on the SAME registered
physical pointer. Unknown/custom allocators and unsupported dynamic cases stay
gaps. Generic layout and sparse source/byte correspondence remain open.
THEN callbacks/collect4/remaining wrappers. THEN Range93/f6/OwnInit caller histories.
None of those histories was promoted through the remaining gaps.

All170 slot records and statuses remain unchanged:118 qualified INSTANTIATED,
35 MISSING,12 WAITING,5 SPEC-ERROR. No endpoint hypothesis was removed, added or
changed; the original endpoint statement is untouched.

D991: ZERO allocation byte images defined. No total initialization is reused or
re-credited, no value is invented for an unwritten byte, and no observational
forgetting of stale bytes is assumed. Source aggregates are not byte images.
No keys were created, destroyed or removed.

## Verification class

Focused cached-cohort host checks only, one capped6G/8G/swap0/Tasks64 scope at a
time, Lean-M7000 and standalone STREAMB_SLOTS=3 turn/admission before EACH ID.
44 focused scopes:23 support modules plus a driver accepted;20 failed inputs
retained compressed.55046 hit the default200000 heartbeat limit, not a memory
kill; replacement per-instruction proofs passed without raising any limit.
Every retry changed source. No infrastructure refusal/stop, unchanged failed
rerun, cap increase or ID exhaustion is claimed. No runtime/Rust/Aeneas/release
or full frozen-manifest replay ran. Summary #print axioms is labeled summary-
based. ONE strict raw audit follows; see RAW_AUDIT.json and VALIDATION.json.
