# NJM retained failing step

Target not yet established. NJM_E001 consumed the sole extraction allowance for the owned safe TX1:129 reference. Charon exit0; Aeneas exit2. No Lean definition was emitted. Exact diagnostic: reference r1_semantic.rs lines326:4–330:1 (the safe three-row loop/boxing continuation), compiler interp/InterpReduceCollapse.ml:1880, add_shared_borrows.update.update_avalues, “Internal error, please file an issue”. Full source, compressed LLBC, source SHA and tool pins are committed. The reference passed the optimized-profile Rust check L030 before extraction.

Wall66.60060545499437s, peakRSS538612KiB, swaps0; standard caps, no timeout or memory kill. Frozen lock sha5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef before/after. Reference scratch bytes unchanged. No retry or extraction credit. Exact extraction commands/tool hashes/NCO-equivalent pins are NJM_EXTRACTION_PINS.json and E001 receipt. The reference allocates one Claims element (1392 bytes) rather than three row elements; no allocator equivalence is inferred from geometry alone.

Next extraction would require a new allowance and a changed/split borrow shape; this job will not rerun the shape or repair the extractor. Independent Lean work on133/134/142 continues. Native129 windows alone cannot replace the missing emitted-reference side.

Earlier Lean elaboration errors are retained with source snapshots and excluded. Successful successors have standard-only #print axioms; no failed-draft sorryAx result earns credit.

K009 unrestricted full-row allocation-plus-data window TIMED OUT at the existing90s solver bound (scope94.0167027800344s, peak2806556KiB, swaps0). No credit and no unchanged rerun. K010 control of that shape is deliberately not launched. L081 splits allocation from the data operation: the exact native ptr::write receives &mut MaybeUninit<Claims>, with fully arbitrary decoder-row limbs and an independent safe buffer view. Separate K006/K007/K008 covers Box value/identity. Original harness names and assertions are unchanged. K011/K012 are the changed, allocation-free data-borrow shape, not a retry of K009.

L091 coherence scan exited1 because NJM_prepare_audit.py omitted Lean's implicit Init from each of36 newly authored expected-import rows. The complete scan had no dangling references or incompatible declarations. The own generator now explicitly prepends/deduplicates Init; the checker was unchanged. L097 passed the full15,630-module scan. No theorem, trust interpretation or compiled combined import changed; no extra combined compilation was run.

No remaining raw-axiom failure: all eight fixtures and77 roots pass L092–L096. The final concrete same-call proofs do not discharge E001's unsafe129 reference extraction failure, allocator/cleanup/owned-carrier association, or sibling256's root. Those remain explicit blockers.
