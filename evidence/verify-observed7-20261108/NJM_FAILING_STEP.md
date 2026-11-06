# NJM retained failing step

Target not yet established. NJM_E001 consumed the sole extraction allowance for the owned safe TX1:129 reference. Charon exit0; Aeneas exit2. No Lean definition was emitted. Exact diagnostic: reference r1_semantic.rs lines326:4–330:1 (the safe three-row loop/boxing continuation), compiler interp/InterpReduceCollapse.ml:1880, add_shared_borrows.update.update_avalues, “Internal error, please file an issue”. Full source, compressed LLBC, source SHA and tool pins are committed. The reference passed the optimized-profile Rust check L030 before extraction.

Wall66.60060545499437s, peakRSS538612KiB, swaps0; standard caps, no timeout or memory kill. Frozen lock sha5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef before/after. Reference scratch bytes unchanged. No retry or extraction credit. Exact extraction commands/tool hashes/NCO-equivalent pins are NJM_EXTRACTION_PINS.json and E001 receipt. The reference allocates one Claims element (1392 bytes) rather than three row elements; no allocator equivalence is inferred from geometry alone.

Next extraction would require a new allowance and a changed/split borrow shape; this job will not rerun the shape or repair the extractor. Independent Lean work on133/134/142 continues. Native129 windows alone cannot replace the missing emitted-reference side.

Earlier Lean elaboration errors are retained with source snapshots and excluded. Successful successors have standard-only #print axioms; no failed-draft sorryAx result earns credit.
