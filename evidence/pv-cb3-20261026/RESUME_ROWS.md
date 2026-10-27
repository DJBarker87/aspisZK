# Resumed callback source-law table

This worker: 4 → 5 ROW-DISCHARGED(candidate). Recount2 plus this worker:
candidate44 →45, OPEN106→105, independentOPEN47→46, excluding live sibling
changes. V246/op229 is a duplicate of the later sibling proof; count it once globally.
Endpoint premises removed:0. Target not yet established.

Only V195 gained row credit in this resume. Owned-reference and typed-kernel
results for V256 do not replace its missing native source association. Native
effects below are assigned to pv-runjoin; no value/source law is thereby
claimed. The observer and simulator are unchanged.

|op|row|status|theorem|receipt|
|---:|---|---|---|---|
|258|V264|OPEN: direct extraction obstructed; P6 pending|—|aeneas-source-op258-005/collected-receipt.json|
|253|V260|OPEN: structured Drop guard in changed built-MIR graph|—|aeneas-source-op253-built-resume|
|252|V259|OPEN: direct extraction obstructed; P6 pending|—|aeneas-source-op252-001/collected-receipt.json|
|251|V258|OPEN: direct extraction obstructed; P6 pending|—|aeneas-source-op251-001/collected-receipt.json|
|249|V256|OPEN: staged reference source/typed kernel checked; native association absent|—|35620.json;35630.json;35681.json;35686.json;35701.json|
|246|V254|ROW-DISCHARGED(candidate)|R1Z.PV_CB3_CallbackBundle.op246_source|35701.json; RESUME_FINAL_MANIFEST.json|
|230|V247|OPEN: bounded copy-helper native gate timed out|—|kani-helper-sum1024-002/collected-receipt.json|
|229|V246|ROW-DISCHARGED(candidate)|R1Z.PV_CB3_CallbackBundle.op229_source|35701.json; RESUME_FINAL_MANIFEST.json|
|228|V245|OPEN: borrow-processing failure; P6 pending|—|aeneas-source-op228-001/collected-receipt.json|
|227|V244|OPEN: builtin-copy extraction failure; P6 pending|—|aeneas-source-op227-001/collected-receipt.json|
|226|V243|OPEN: branch-context extraction failure; P6 pending|—|aeneas-source-op226-004/collected-receipt.json|
|225|V242|ROW-DISCHARGED(candidate)|R1Z.PV_CB3_CallbackBundle.op225_source|35701.json; RESUME_FINAL_MANIFEST.json|
|224|V241|OPEN: sibling extraction failure reused; P6 pending|—|op224-reused-obstruction.json|
|223|V240|OPEN: escaping-reference loan validation guard|—|aeneas-source-op223-built-resume|
|222|V239|OPEN: sibling extraction failure reused; P6 pending|—|op222-reused-obstruction.json|
|219|V238|OPEN: pinned extraction executable unavailable|—|charon-source-op219-001/collected-receipt.json|
|217|V237|OPEN: extracted skeleton retains generic-array default cut|—|—|
|216|V236|OPEN|—|—|
|215|V235|OPEN|—|—|
|212|V234|OPEN|—|—|
|209|V233|OPEN|—|—|
|208|V232|OPEN|—|—|
|205|V231|OPEN|—|—|
|134|V230|OPEN|—|—|
|133|V229|OPEN|—|—|
|132|V228|OPEN|—|—|
|121|V220|OPEN: native whole/cell gates timed out; extraction refused structured Drop|—|aeneas-source-op121-001/collected-receipt.json|
|120|V219|ROW-DISCHARGED(candidate)|R1Z.PV_CB3_CallbackBundle.op120_source|35701.json; RESUME_FINAL_MANIFEST.json|
|79|V201|OPEN|—|—|
|51|V195|ROW-DISCHARGED(candidate)|R1Z.PV_CB3_Op51Arbitrary.op51_source|35603.json; kani-wide-arbitrary-001/collected-receipt.json|
|36|V187|DEFERRED(native effects → pv-runjoin); source/value law remains OPEN|—|compile-free native-effect review|
|35|V186|OPEN: standard-library alignment-to-NonNull transmute unsupported|—|aeneas-source-op35-default-resume|
|34|V185|OPEN: Vec layout rejected; opaque Vec cannot be expanded for field read|—|aeneas-source-op34-method-resume|
|33|V184|OPEN|—|—|
|32|V183|DEFERRED(native effects → pv-runjoin); source/value law remains OPEN|—|compile-free native-effect review|
|31|V182|DEFERRED(native effects → pv-runjoin); source/value law remains OPEN|—|compile-free native-effect review|
|30|V181|DEFERRED(native effects → pv-runjoin); source/value law remains OPEN|—|compile-free native-effect review|
|29|V180|OPEN|—|—|
|28|V179|OPEN|—|—|
|26|V178|DEFERRED(native effects → pv-runjoin); source/value law remains OPEN|—|compile-free native-effect review|
|25|V177|OPEN|—|—|

Native-effect reasons (all remain obligations):

- op26: Allocating Path/OsString join: platform carrier and native allocation/OOM/lifetime outcomes; no filesystem I/O is claimed for join.
- op30: Native String capacity/allocation/OOM-abort and allocator representation are absent from the logical string carrier.
- op31: String growth/reallocation, capacity and abort/destruction effects need the real heap/owner interpretation.
- op32: Vec reserve exact changes native capacity and has allocator failure outcomes beyond payload-only Vec; preserve the complete Result.
- op36: Successful Vec-to-array conversion transfers owners and disposes of the vector buffer; allocator/deallocation/Drop interpretation remains.
