# Findings and failed attempts

NJR_K001 exited 1 before verification: staged NHR transport lacks tools/r1-builder-reference/tree.rs, required by the frozen statement crate under cfg(kani). Own input repair: supply the unchanged, already retained NJJ tools/r1-builder-reference sources. No verdict/no credit; retry is a changed-input attempt. No shared infrastructure modified.

NJR_K002 exited 1 before verification: missing cfg(kani) include of the exact KMX_stubs.rs at the scratch crate root. Own staging omission repaired by the same include retained by NJJ. No semantic verdict. K003 includes that repair and the new M05/M09 declarations.

NJR_K003 exited 1 before verification: exact KMX generic Vec helper requires allocator_api in the scratch crate. Added cfg_attr(kani,feature(allocator_api)), identical to predecessor setup. This is a changed-input compile repair, no proof verdict.

NJR_K011 (full receiver64 plus mutable weights64, all payload/frame assertions) timed out at the unchanged 90s harness timeout, exit1, 95.141s wall, 3586148KiB RSS, swap0. No credit. Never rerun unchanged. Replacements split the full immutable receiver/selected-slot window from the actual enumerate/index destination/full mutable-vector frame. No timeout or cap increase. Controls K012/K013 in the original queue were not launched.

NJR_K025 same-payload fresh-allocation control timed out at90s, exit1,96.730s wall,6349348KiB RSS,swap0; excluded. Replaced its full symbolic clone64 shape by a zero-payload witness at width64. The allocation is still different and every payload byte is equal; the original harness name is retained. No unchanged rerun, cap or timeout increase. Subsequent queue3 jobs were not launched.

Lean own-input repairs: L002 used reserved identifier `at` (fixed as `pos`); L004 omitted the explicitly logged length equation from omega's context (added it); L011 selected legacy Op4P_Install and hit duplicate Phase ownership (replaced the import by the coherent RPz7_Op4P_Install already in the selected closure); L014 needed zeta reduction before rewriting the actual filled call; L017 introduced a let-bound Accumulator as the port variable (fixed with dsimp only before intro). Failed elaborations carry temporary sorryAx placeholders and are excluded; only successful final-module axioms are selected. No existing proved module or shared infrastructure changed.
