# Session10 exact result and recheck dispositions

Full successful original-entry history through13923/cut92 and14756: OPEN.
Full OwnInit joint witness: OPEN. Negation of its complete existential: NOT
PROVED. Checked contradiction: SPEC-C7 is a LOCAL native-image contradiction,
with its exact scope in FINDINGS.md. No row or endpoint premise is closed.

## Per-site images, from actual types and adopted stores

SESSION10_ABI_SOURCE.json contains frozen N95807 source/type hashes, field
orders and the complete adopted ELF hash; SESSION10_ABI_BINARY.txt retains
fresh read-only disassembly and relocations of that same ELF. Evidence class:
binary-structural (adopted binary), plus V370 compiler-cohort. This is not a
proof of compiler correctness or original-entry reachability.

AllocationImages defines five different operand-indexed images; AllocationSites
attaches each to its actual native site, layout and exact support. `mask`
proves support for EVERY operand, `stores_within_layout` bounds it, and
`retains_tail` proves each unwritten address keeps pre-memory:

| Site | Object | Layout | Stores / no-store tail |
|---|---|---|---|
| fa099 | ArcInner<ScopeData> | 40/8 | qwords0/8/16/24, byte32; tail33..39 |
| e058a | ArcInner<Packet> | 48/8 | qwords0/8/16/24; tail32..47 |
| e05e8 | callback Box | 56/8 | actual stack bytes0..31, qwords32/40/48; no tail |
| e064b | ThreadInit Box | 24/8 | qwords0/8/16; no tail |
| 17be96 | ArcInner<thread::Inner> | 48/8 | qwords0/8/16/24/32, dword40; tail44..47 |

The fifth site was absent from the earlier three-site schedule. Source361's
call12290 to f213 corresponds to e0541 -> GOT1b3758 -> Thread::new17be40.
Layout helper1a6720, reached through GOT1b41c0 with8/32, gives8/48. It is not
Packet's image despite having the same width. Source Inner field order is
name,id,parker; native order is id,name,parker. In the absent-name branch the
store at32 STILL occurs from r14; no zero length is fabricated. Current-thread
TLS's existing-handle branch allocates nothing; its uninitialized branch calls
this same Thread::new. A successful prefix has not yet proved which branch it
uses or excluded name conversion, hook or uncached environment allocations.
No total image for those unbound branches or Vec spare capacity is supplied.

A callback copy must distinguish no destination store from copying an unknown
source byte. Image is `Nat -> Option (Option Nat)`: outer none means no store;
some none copies an unknown source byte. `callback_copy` retains exact source
bytes even on overlap, because snapshot precedes the writes. The actual stack
snapshot, native rsp and scalar operands still require SAME-history source/
native binding before this local binary image is installed. An arbitrary
image/Store transformer or chosen initialized padding is not a replacement.

## Accepted SPEC-C6 operational repair

SiteArc.classify uses the actual DATA operand's ScopeData/Packet tag at the
shared BoxNew4963 token. It does not infer layout from field count or erase
source type. shape selects40/8 or48/8. Partial pointer codecs resolve through
source wrappers and registered physical addresses; missing backing/invalid
fields remain None. Initial ScopeData uses counter0 and panicfalse, with its
physical current Thread pointer. This local representation codec does not
prove that opaque Thread122/AtomicBool123 native replies actually have that
representation. That caller binding remains OPEN, not a new success premise.

Resources are queried for the selected layout on all branches, before success
value decoding. Null/abort, failure, fault, divergence and pending keep the
named provider reply. returned_owned rechecks ownership, backing/pointer and
both stored-byte and no-store laws for both layouts. SiteArcRecheck.scope_handler
uses the actual40-byte successful resource DATA from the old counterexample;
its result is the exact threadWord graph, including None. It is not a claimed
nonvacuous original-entry success or an assumed decode. packet_reply proves
all-answer equality to the existing sparse Packet reply at Packet's OWN type.

SiteRuntime installs that selector in the native assembly and rechecks every
ordinary full-answer ghost frame. SiteV2Runtime uses the actual lane-A v2 step,
not an arbitrary FullStoreActionTable. SESSION10_LANEA_INPUT.json pins latest
read-only head757cd4318ea and checks all ten v2 surface sources unchanged from
the session9 compatible replay. No provider/cache mixing, source write or new
cohort rebuild occurred. Existing VALUE-only Values remains a parameter;
complete store-table/native-value adequacy is NOT established. SiteHistory
original rechecks source origins/arguments at every finite prefix in this
runtime; it establishes no successful reachability.

## Disposition of every prior affected result

- NativeRuntime, ResourceHistory, BoundRuntime/History, ControlRuntime/History,
  SparseRuntime/History and V2Runtime remain historical definitions/results
  about their own machines. There is NO whole-world transport from their
  Packet-only or total-image executions. The new SiteRuntime/SiteV2Runtime/
  SiteHistory provide the replacement native frame and actual-origin facts.
- SparseArc and SparsePacketHandler's Packet-local image/ownership facts remain
  valid at Packet operands. packet_agreement and packet_reply provide actual
  full-memory/all-answer comparisons. Their use on ScopeData is rejected by
  the old C6 diagnostics and replaced by the explicit new type selector.
- ArcImageGap's total-image obstruction and ScopeAllocationGap/PollGap/
  RuntimeGap remain valid negative facts about old definitions. They are not
  silently relabelled as failures of the corrected SiteRuntime.
- InitImageRecheck.memory_agreement/initPost_memory prove that the named
  ThreadInit three-word initializer ALREADY matches the adopted24-byte image
  on EVERY pre-memory and all pointer words. Both stored bytes and the complete
  outside frame agree. Thus that initializer needs no sparse byte repair.
- ClosureBoxAllocation and local callback ownership/backing/pointer facts never
  claimed initialization. They remain valid ownership-only facts. The native
  byte association is FALSE at the explicit local C7 world; CallbackNativeGap
  proves the actual assembled handler still omits that suffix, for every
  native Environment and source captures. The new callback IMAGE exists but
  is not installed or source-bound. CallbackImageGap.unknown_copy rejects a
  known-byte serializer for unknown copied padding.
- LocalOwnership.applied/LocalInitMemory.successful remain applications on their
  historical LOCAL world only. Their byte-independent OWNER predicates are
  preserved by AllocationImages.receiver_frame/owned_frame, but no new actual
  allBridged/SourceInitBoxOwnership application on a corrected continuous run
  is claimed. The absent local39 receiver/vacuity finding remains in force.
- ConcreteEntry.pre and the capture/entry facts contain no allocation image;
  they retain their entry-only credit. JointPremises/HistoryJoint/BoundJoint/
  ControlJoint's old pending-model machine clauses gain no SiteRuntime credit.
- The18 historical full statements, Cut92Contract and Cut92Composition are
  retained. Their full source/runtime rebinding remains unproved. In particular
  AllocationWitness's world equation uses the ownership-only callback reply;
  an eventual initialized callback reply must be propagated explicitly rather
  than silently equated to it. C7 records the issue; no unapproved new frozen
  witness clause is adopted. No full existential contradiction is inferred.
- No prior Thread::new initialized-byte theorem was consumed. Its new image
  is a local native store-cut model; native allocation/backing/source-cell
  initialization and its opaque return representation remain open.

## Exact next work

Bind Thread122/AtomicBool123 and ThreadNew213 values/backing, and the callback
snapshot/rsp/Packet/capture operands to actual source/native states. Install
each named image/action, retaining every resource answer. Supply the remaining
concrete value facets and resource schedule, then carry ONE original-entry
history through ScopeData, f213, Packet, callback13923/cut92, registration113
and ready129/14756. Apply allBridged and the nonvacuous ownership export on
THAT history, then satisfy all eighteen universal contracts jointly or prove
a contradiction of their COMPLETE premise set. A local image mismatch or an
entry-only/pending instance is not that alternative deliverable.
