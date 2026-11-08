# Lane A session5 handoff — partial, not complete D984 adequacy

Branch `codex/pv-lib-20261107`; start `bbb785242b876aa943e9627aa46a7ffa350a860a`.
No push/merge. Prior handoff preserved in session5/INHERITED_HANDOFF_SESSION4.md.
All source changes are own `lean/PV_LIB_A_*`; evidence is own lane plus the
shared PLIB_MAP.json and REMAINING.md. Lane B and package/consumer/ledger files
are unchanged. Current support source hashes are in session5/SUPPORT.json.

## What passed

28 new small modules,118 roots. Source actions now follow BoxNew/Arc pointers;
Arc360, atomic351/581/557/646 and CAS530/555, ptr308/364, mem442, scope457/611,
transparent Cell641, bool-only504, Option369 and nonlast486/683 have named source
projections. Original five are retained. Final partial candidate:
PV_LIB_A_DropDispatchV2.step, based on OWNER-aware OwnInitInterpreterBridged.
Away/neutral-trace agreement and full native effects are compiled.

CloneValidityV2/CloneIssuedV2 derive Valid/count1 from SAME literal CLOSED124
return and existing actual4933/4945 facts. CloneCountV2 derives a defined
BoxNew count1->2 source write preserving weak/Packet. ClonePrologueV2 proves
the actual five source steps17->24->issued360 on V3; ArcPollV3 proves12950's
full-reply graph. No independent count/root/alias/write-definedness premise.
The selected original constructor cut and complete f361/Builder270 history
are still missing. Issued Valid is a store projection; the request keeps its
PRE-issue counter. Do not reconstruct its request at the new store counter.

RangeHistoryV2/RangeTraceV2 establish local7, first93 write and continuous
ORIGINAL prefix via actual165's named returned-value law. Corrected-owner and
later iterations remain open. The complete74-module f6 cone is now cached:
68 exact pinned replays46320–46387, no source edits. F6DeliveryTransportV2
uses the existing SINGLE induction at literal PrefixIdentity, no finite
cutoff or post-delivery agreement. Actual resolver/handler agreement is open.
Local source counter/numbering and native registry framing are compiled;
complete OwnInit numbering/resource-environment coherence remains open.

## First work to resume

Finish D984 before crediting caller histories as complete: exact last-strong
Arc payload destructor/implicit Weak guard, last/dangling Weak and deallocation,
Packet result/scoped decrement composition, typed builtin Drop dispatch,
arbitrary-T Cell504 old-value Drop, join, parker/TLS, iterator/callback and
formatter effects. Primitive tokens do not discharge an opaque native wrapper.
The final candidate fails closed on unsupported specializations; it is NOT a
faithful complete row implementation. The V3 prologue is not silently a proof
of complete final-overlay/caller history.

Inventory v2 includes75 installed LEAFs,340 raw thread leaves, all three slice
emissions,458 ledger Drop sites and raw typed destructor metadata.111 entries
are conservative source-writer/callback candidates; eight installed wrappers
still require review. No RefCell function is emitted, but Cell/UnsafeCell can
point into boxes. STORE_ACTIONS.json lists all installed and unsupplied meanings.
No null entry is a proved fact. SPEC-C3 witness is f2798a4fac4/49735 at12950.

Read session5/MODEL_CORRECTION.md before using the modules. Wrong draft
PrimitiveV2.AtomicBoolStore646 and wrapped Cell504/641 are explicitly withdrawn
from source-semantic credit. Corrected byte646 and transparent Cell meanings
are installed on V3. Cell::set's destructor is modeled only for bool. Named
load127/129/528, bool-new123 and Cell-new371 value facts are LOWER obligations,
not axioms/T items; their actual backend instances remain unproved.

## Verification and IDs

116 focused attempts:97 pass (28 modules,68 cache replays,one driver),19
repaired elaboration failures. Every failed input is compressed by exact
index-blob/source hash. COMPILES.json and each receipt record target,exit,wall,
peak RSS,swap,source revision and printed axioms. One strict raw47490 passed
118 roots: exit0,9.60s,peak6705204KiB,swap0, revision
901669d3323d82be61520a58eae32979827f125e. Only propext/Classical.choice/Quot.sound;
unresolved0,summary mismatches0. Unchanged strict walker/collector; only arrays
changed. Graph archive+SHA/manifest retained. No rerun and no full release claim.

Spent46300–46399 and47400–47415; next unused47416. Remaining focused47416–47489,
raw47491–47499. No ID exhaustion claim. Own focused-host-s5.py changed only the
allowed463xx/474xx guard ranges. Each attempt used standalone STREAMB_SLOTS=3,
allowed admission,6G/8G/swap0/Tasks64/-M7000 and own host directory. No new proof
or full regression is needed merely to reread this handoff. No live task scope.

Map retains170 statuses:118 qualified INSTANTIATED,35 MISSING,12 WAITING,
5 SPEC-ERROR; session5/MAP_DELTA.json adds15 support records without closures.
Endpoint premises removed0/added0,new T fields0. Frozen specs unchanged. No
runtime/Kani/Rust/SBF/Aeneas/full-manifest replay or endpoint result claimed.
The task remains PARTIAL because the semantic/composition obligations above
are unproved, not because IDs or compute were exhausted. COMMITS.txt records
all proof/replay/driver commits through901669d3323; final metadata commit follows.

Session6 from9e72b836054: focused47417 supplies the import surface `PV_LIB_StoreActionTable.v2` in `PV_LIB_A_StoreActionTable`. It consolidates the22 supplied projections, with explicit bool/nonlast/unpark coverage tags. This is PARTIAL, not completed D984 adequacy. Attempt47416 repaired a namespace doc-comment syntax error; exact failed source retained. No caller closure claimed.

Focused47418: `PV_LIB_A_StoreActionMachine` installs the supplied table directly on the OWNER-aware base. One symbolic agreement and neutral-trace transport compile; `native` exposes the exact all-answer graph and its undefined arm. No adequacy or caller closure follows from these graph identities.

Focused47419: checked `PV_LIB_A_ActionAdequacyGap` shows aggregate504 is unsupported although its same transparent source replacement prefix is defined; `aggregate_delivery_undefined` shows the candidate drops the reply status on that arm (including pending/fault). Count1 Arc/Weak is rejected; seven installed wrappers have no table entry. These are model/coverage counterexamples, not source failures. Full-answer/source adequacy remains open.

Focused47420: `PV_LIB_A_ReplyAdequacyGap.pending_not_retained/panic_not_retained` compare the unsupported aggregate504 result directly with the pinned full-reply rule. Raw emitted specialization metadata for all six504 sites is in session6/CELL504_SPECIALIZATIONS.json. The supplied table is not ready for source-adequacy credit.

Focused47422: `PV_LIB_A_ActionAnswers` proves exact whole delivery for weak spurious CAS failure and both CAS variants pending/fault branches, not just world/event frames. Strong/weak Result::Err leaves source cells unchanged. Attempt47421 repaired let/conjunction parenthesization; failed source retained. These branch facts do not fix unsupported Cell/Drop/wrappers.

Focused47423 compiled RawAudit6: same strict driver/walker as session5, only the five runtime-module and29 root arrays changed. Final raw47491 is next; no raw rerun planned.
