# PV CB3 handoff

Branch `codex/pv-cb3-20261026`; base `09df2340e24cdcc86fe4ef272eed9994562fcda9`.
Stopped on 100/100 Lean compile attempts and 20/20 Kani attempts. Reservation
refusals are not charged. No checked counterexample against shipped source.
No crate/program code or release pin changed; no keys created or destroyed.

Recount2 baseline plus this worker: OPEN110→106, independent OPEN51→47,
CLOSED-ON-CANDIDATE40→44. Endpoint premises removed:0. Deduplicate V246
against the later sibling proof. Other sibling changes are excluded from these counts.

|op|row|status|current composed theorem|receipt|
|---:|---|---|---|---|
|246|V254|ROW-DISCHARGED(candidate)|R1Z.PV_CB3_CallbackBundle.op246_source|24701.json;24766.json|
|229|V246|ROW-DISCHARGED(candidate)|R1Z.PV_CB3_CallbackBundle.op229_source|24705.json;24766.json|
|225|V242|ROW-DISCHARGED(candidate)|R1Z.PV_CB3_CallbackBundle.op225_source|24711.json;24766.json|
|120|V219|ROW-DISCHARGED(candidate)|R1Z.PV_CB3_CallbackBundle.op120_source|24754.json;24766.json|

The composed dictionary uses one concrete extracted afterstate carrier and
leaves all unrelated callbacks arbitrary. Full Result equations retain all
outcomes and have no desired-output premise. Op225's reverse payload adapters
are arbitrary data and the result is independent of them.

**Correction:** op51 remains OPEN. Its checked selected-to-reference equation
is not enough: the native harness passes through canonicalizing WideExact::new,
so arbitrary extracted-carrier source correspondence is not yet established.
No canonicality premise was added to claim closure.

The frozen39-module callback/helper manifest passed, with dependency object
hashes verified against receipts. Final audit24800: exit0,1.083600232s,
peakRSS2672128KiB, swap0, revision3e4bedd4bb; accepted axioms are only
propext,Classical.choice,Quot.sound. Exact targets and full revisions are in
numbered JSON receipts. This is not the whole privacy endpoint replay.

Supporting results connect the extracted scalar word step to exact quotient,
remainder, word-vector shape and arithmetic; the typed sampler recurrence has
the rank formula. These do not discharge op249's source/library cuts.
Full sampler, polynomial, product-cell and1024-row helper native gates timed
out without verdicts. The iterator Kani witness passed optimized native replay;
it is a Kani/native discrepancy, not a checked shipped-source counterexample.

Original host paths disappeared. The unchanged repository capped runner and
a retained read-only Aeneas object cache were reused. A separate retained
extractor probe was identified as ProverRwRngExtractor006 and refused structured
Drop; it supplied no accepted source-law closure and its guard was not bypassed.

Next: establish op51 correspondence over the whole extracted carrier using a
direct source proof or cfg(kani)-only in-module full-field construction; then
resolve remaining pure callback source/library extraction obligations. E1/E2,
RunJoin, L1/L2/L3, client-route and full dependency-closure obligations remain.
No simulator or observer was weakened. Privacy target not yet established.
