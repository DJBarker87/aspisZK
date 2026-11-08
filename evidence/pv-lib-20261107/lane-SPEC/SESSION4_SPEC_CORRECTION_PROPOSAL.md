# SPEC-C3: source-memory effects of Arc clone at12950

Proposal only. COMMON revision2/D981 and the frozen files are unchanged.
This is a model/source mismatch at a real emitted native boundary. It is not
an original-entry reachability proof, full joint-premise contradiction, or
proof of f361. It blocks treating the existing f361 component as complete.

Before: COMMON revision2 selects SourceStoreLibrary's five concrete meanings
(CellReplace289, RangeNext93, IntoIterNext9, VecPush167, VecAppend10); away from
those native polls, it uses OwnInitInterpreterBridged. At native f36012950,
that machine updates native arguments/return slots but leaves older source
cells unchanged. It never reads Input.changes. Input.changes is retained by
the old package comparison only.

Required after: retain the OWNER registration/operator/allocation layers and
all five writer meanings; additionally interpret the actual source-selected
Arc clone's strong-count update at native f36012950. Use the existing
ArcClone.Valid/countAddress/OutsideCount representations, SAME actual issued
operands/store/world, source fetch_add and MAX_REFCOUNT guard, and complete
reply/event/footprint behavior. No arbitrary Store delta or successful-write
hypothesis is allowed. Native source-effect inventory must also be checked
for other f361 leaves before declaring the machine complete.

Witness: PV_LIB_SPEC_F361ArcMachineGap.native_poll/count_unchanged/
increment_impossible, focused49735. At actual fn63 (function360), &local17,
return23, remaining F361.live.body.drop64, successful delivery preserves an
older initialized count n, hence cannot produce n+1. The statement quantifies
actual reply success, native resolution, older source address and issued
counter; it does not assert their reachability from a full valid f361 entry.

Source authority: W3 revision41e76d01fdead952101594b8b0f36a7561d180f2,
PV_THR2_LibrarySemantics_ArcClone (Rust1.94.1 sync.rs2360–2411 and SHA retained
there), f361MetadataEffects.entry360/effects/delivered, and f361Statement.Run.native.
Its concrete native rule applies ArgumentEffects.afterEffects before deliver.
The corrected machine's native_poll instead has no such count action. The
Thread clone214 operator acts at14535 and does not cover this Arc clone.

Affected consumers: full f361 MachineSpec/reference/Post, f270 and all callers
through OwnInit, and any same-history transport from the D877 package trace.
A graph declaration or arbitrary full reply cannot supply the missing write.
The old package is retained read-only. No statement is weakened, no new trust
item is introduced, and all full-contract completion counters remain zero.
