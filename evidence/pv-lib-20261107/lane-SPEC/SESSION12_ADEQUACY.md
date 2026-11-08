# Session12 — exact achieved scope and unfinished target

Continued966c928151970c37c0c4187255a3e3d3cffa66ba, on the SPEC branch.
The requested task is **NOT complete**. No successful continuous original-entry
history through callback/cut92 and ThreadInit14756, no full OwnInit joint witness,
and no negation of its complete existential are proved. No row is proved or
endpoint premise removed. The local findings below are not full contradictions.

## Native/resource/value binding work

`NativeMemory12` is the last operational assembly in this session. It layers
initialized-TLS122 and physical Thread-clone214 qword effects over SourceNative12
(finite physical callback), NativeBindings12 (constructors and absent-name213),
and NativeBoolRuntime (the corrected ScopeData codec). Its `Cut` contains finite
physical frame data and the native TLS slot. It is NOT an inhabitant of the old
full machine specification or an adequate original-entry native snapshot.

`SuccessSchedule12` supplies source-site/size-bound malloc replies:
4963/40->2048 (ScopeData),4963/48->4096 (Packet),12290/48->6144 (implicit
Thread::new),13923/56->8192 (callback),14756/24->12288 (ThreadInit).
Its native122/452 replies are fixed DATA; constructor success triggers use
null only as an ignored marker, replaced by source-derived values. Other
unknown operations stay pending. `entry` proves the complete retained entry
Pre with this environment choice, by actual reference/capture proof, not by
silently identifying environments. This is still ENTRY-only evidence.

NativeConstructors supplies f123 numeric0/1 inside Atomic/UnsafeCell<u8>,
f455's exact Packet UnsafeCell result wrapper and f456's MaybeDangling wrapper.
NativeRecheck12 extracts the actual source tokens and checks the constructor
values and callback capture projection. NativeKinds has the LLBC result tags;
its unused initial boolCell tag was incorrectly UnsafeCell<bool>, not an
extracted field (AtomicBool is opaque). That historical tag is retained and
NOT consumed by the constructor. NativeConstructors.boolCell is u8. The
source/metadata correction is recorded explicitly in FINDINGS(SPEC-C9).

ThreadNewNative installs the implicit48/8 allocation for the absent-name
branch, using the named malloc/attempt/backend model and retaining all resource
answers, including null->abort with exact allocator-abort event suffix. Id
comes from the actual request; the initial Scope option comes from f361's
still-live source argument local4. Canonical nonzero id/pointer checks are
partial computations, not hypotheses in a row. Native213 Some(String) remains
the historical fallback: CString conversion/allocation is NOT newly proved.

ELF fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558:
e045e copies scope r9 into r14;17be53's absent-name branch skips assignment
of r14;17beef nevertheless stores r14 at offset32. Thus absent-name length
is the SOURCE scope pointer here, not invented0. ThreadNewRecheck12 checks
successful reply and ALL actual sparse stores;44..47 remain allocator bytes.
This is the reused adopted disassembly in SESSION10_ABI_BINARY.txt plus the
existing V370 compiler-cohort boundary, not compiler correctness.

ThreadWords12 reads actual initialized physical qwords with the existing
bounded codec. Initialized current_or_unnamed reads TLS Inner, subtracts16,
and increments the ArcInner count (17c498/17c4a1/17c4ac). Thread::clone obtains
Thread VALUE through its actual source reference/store, then increments its
physical count (e0629/e062d/e0631). The increment's signed JLE test is explicit;
no absence of overflow is assumed. All non-success native answers are retained.
ThreadWordRecheck12 proves exact LOCAL TLS/count words and count1->2, using the
named word-image inverse. `prepared` is only a local WORD snapshot: no native
Thread allocation metadata/liveness or original TLS initialization is proved.

## SPEC-C9 and affected rechecks

The old WordThreadArc requires boolean false in AtomicBool.v.value. Rust
1.94.1 atomic.rs530-531 stores `v as u8`; the actual retained lane-A v2 load129
also expects numeric0/1. AtomicBoolGap checks rejection for EVERY Thread value.
NativeBoolArc accepts canonical numeric0 (and retains legacy false), with
named scope_image_u8 and ordinary ownership/sparse/frame laws. NativeRecheck12
checks the actual40-byte local request and unchanged Packet full reply.
AtomicRecheck12 applies the ACTUAL v2 boolean load to both new constructor
values and proves that the same zero is accepted by the ScopeData image.
No lane-A source or object was modified. Latest read-only lane-A797dff893c3f
has ALL20 relevant source pins identical to session11; the same import-only
W3 private replay is reused. The supplied v2 remains PARTIAL. Values remains
an independent VALUE-only parameter and full TableAdequacy is not discharged.

## SPEC-C10 and physical stack correspondence

Frozen.References allows initialized source STACK cells without OWNER heap
registration. StackReferenceGap12 gives an exact local valid typed reference
activation7/local50, with initialized pointee and no registered receiver;
the old capture codec returns None for EVERY k. PhysicalStack12 adds a finite
source/native frame map, checks frame activation, exact source address and
initialized source pointee, and retains heap resolution for other references.
Packet still resolves its registered allocation independently. No arbitrary
Store/image transformer or successful-decoder law is accepted.

The no-hooks native branch e0550/e0559/e0562/e0565 actually stores ALL32 bytes
at rsp+0x38: cap0,pointer8,len0,hooksNone0. installDefault/default_snapshot
and copies_default check that snapshot and its exact e0614/e0619 copies.
StackCallback12 uses the new source/physical projection with the session11
byte suffix and full resource answers. StackRecheck12 closes a LOCAL callback
poll with computed registers32768/8192/112/k. Its8192 backing is a projection
fixture borrowed from the historical local callback allocation; it is NOT
claimed to be a typed Packet allocation or an original-entry predecessor.

The finite frame is NOT constructed from the actual original-entry history.
The no-hooks source453/454 reply/branch is NOT bound or installed by proving
these binary store helpers. Live generated &run's type/provenance and physical
slot still have to be derived on that same history. C10 is repaired at the
local codec interface; full physical/source adequacy is still OPEN.

## What still blocks the requested full result

1. Bind source TLS/native leaf values along the entire actual root prefix,
   including127/129 and the TLS helper path; supply valid initialized native
   Thread/TLS backing, the real452 counter, hooks453/454 and constructor
   provenance. The fixed data/pending environment and local word fixture are
   NOT a complete successful native environment.
2. Derive ONE actual native physical stack/frame from source pushes and the
   real generated &run, and execute the selected hook stores there. The finite
   map parameter and installDefault helper are not a reachability proof.
3. Construct the SAME continuous original-entry history through the five
   allocations, callback/cut92,registration113 and14756. MemoryHistory12.original
   only preserves source-issued origins/arguments at every finite prefix; it
   proves no successful milestone or byte/source adequacy.
4. Apply allBridged and nonvacuous SourceInitBoxOwnership THERE. Historical
   LocalOwnership/LocalInitMemory exports retain their local/vacuous limits.
5. Rebind the eighteen whole statements and composition to the adequate
   operational runtime and discharge the complete joint witness, or prove a
   contradiction of its complete premises. Those statements and
   Cut92Composition.Witness remain historical targets, not silently changed
   to NativeMemory12. None of these five obligations is a new Pre/T field.

## Validation boundary

Focused compilation receipts carry exact source revisions, hashes, target,
exit, wall,RSS,swap and printed axioms. Failed elaborations are retained and
changed before retry. No full manifest, Rust/Kani/SBF/extraction suite or
unchanged old audit was rerun. One strict NEW-root audit is the final gate;
its exact result is in SESSION12_RAW_AUDIT.json after completion. No shared
launcher/provider/package/ledger/implementation/key edits, push or merge.
