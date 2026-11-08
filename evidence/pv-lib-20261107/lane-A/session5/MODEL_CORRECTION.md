# D984 correction and limits

Base: bbb785242b876aa943e9627aa46a7ffa350a860a. D981's five-writer
OWNER-aware step misses writes through pointers into BoxNew/Arc blocks.
SPEC-C3 at codex/pv-lib-spec-20261107@f2798a4fac4, module
PV_LIB_SPEC_F361ArcMachineGap (49735), witnesses the actual12950/f360 gap.
Its local mismatch does not prove original-entry reachability.

The source projection layers now extend OwnInitInterpreterBridged, retaining
registration14320, operator bindings and bridged allocation/resource dispatch.
StoreDispatchV2 adds11 native source projections; ScopeDispatchV2 adds457/611.
OwnerStoreV3 corrects transparent Cell641 and bool-only Cell504. DropDispatchV2
adds Option369 and the source-selected nonlast486/683 branches. Away and finite
neutral-trace agreement are against the OWNER-aware base. Expanded bodies are
not also intercepted as native leaves. Actual replies, worlds/events, failure,
pending and abort prefixes are retained in the supported action graphs.

**This is a PARTIAL candidate, not complete D984 adequacy.** Arbitrary-T Cell
set, last/dangling Arc/Weak, typed Drop, join, parker/TLS, iterator/callback and
formatting effects still lack complete source/native bindings. Unsupported
specializations may become undefined; this behavior is not credited as a
faithful whole-function model. Adding nested primitive tokens cannot discharge
an enclosing opaque boundary. STORE_ACTIONS.json lists every inventoried
candidate, with null meanings for unsupplied facts rather than placeholders.

Source review corrected three drafts. PrimitiveV2.AtomicBoolStore646 stored a
Data.boolean; AtomicBool's UnsafeCell<u8> instead holds numeric0/1, as now used
by StoreAtomicV2, AtomicReadsV2 and AtomicBoolNewV2. StoreAtomicV2.CellSet504 and
CellTakeV2.CellTake641 assumed wrapper fields[0,0]; that is incompatible with
the adopted transparent Cell payload view used by CellReplace289/ACTIVE.
CellSourceV2 supersedes both. Cell::set drops the old T after replacement;
only bool504 has a full direct source projection here. Its generic prefix is
never installed as a complete arbitrary-T action. Cell641 moves the old
SpawnHooks and constructs its own source Default(first=None), without Drop.
The old mathematical definitions remain reproducible/audited but receive no
source-semantic credit. A successful axiom audit does not validate a model.

New lower facts for loads127/129/528, AtomicBool::new123 and Cell::new371 are
named definitions, not axioms or T fields; their actual backend instances remain
open. Existing AtomicUsize::new121 facts at4933/4945 supply constructor counts.
CloneCountV2 derives the defined source count1->2 write from the SAME literal124
return, preserving weak and Packet; ClonePrologueV2 proves five source steps on
V3. ArcPollV3 proves the actual native12950 dispatch. These do not bind the
selected original constructor entry or complete f361/Builder270 histories.
CloneIssuedV2's Valid is a store projection: the saved native request keeps the
PRE-issuance counter. No fact is instantiated at a reconstructed wrong counter.
The later DropDispatch overlay has OWNER agreement but the V3 prologue is not
silently promoted to a complete all-writer machine history.

RangeHistoryV2/RangeTraceV2 establish source local7 and the first93 write via
actual165's named returned-value law; their continuous predecessor run is
explicitly ORIGINAL interpreter. Corrected-machine and later-loop histories
remain open. F6DeliveryTransportV2 uses the existing single induction at f6's
literal PrefixIdentity, without a finite-delivery witness or post-delivery
agreement. Concrete original table/handler agreement remains open. Numbering
and registry results are local; allocation coherence remains open.

Frozen specs, package branches, row consumers, ledger, endpoint premises,
implementation and trust fields are unchanged. No complete row or endpoint
result is claimed. One strict raw audit47490 passed118 new roots with only
propext, Classical.choice and Quot.sound; this is proof hygiene, not release
adequacy. Exact receipts and compressed failed sources are retained.
