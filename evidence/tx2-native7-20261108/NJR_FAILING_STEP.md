# Findings and failed attempts

NJR_K001 exited 1 before verification: staged NHR transport lacks tools/r1-builder-reference/tree.rs, required by the frozen statement crate under cfg(kani). Own input repair: supply the unchanged, already retained NJJ tools/r1-builder-reference sources. No verdict/no credit; retry is a changed-input attempt. No shared infrastructure modified.

NJR_K002 exited 1 before verification: missing cfg(kani) include of the exact KMX_stubs.rs at the scratch crate root. Own staging omission repaired by the same include retained by NJJ. No semantic verdict. K003 includes that repair and the new M05/M09 declarations.

NJR_K003 exited 1 before verification: exact KMX generic Vec helper requires allocator_api in the scratch crate. Added cfg_attr(kani,feature(allocator_api)), identical to predecessor setup. This is a changed-input compile repair, no proof verdict.

NJR_K011 (full receiver64 plus mutable weights64, all payload/frame assertions) timed out at the unchanged 90s harness timeout, exit1, 95.141s wall, 3586148KiB RSS, swap0. No credit. Never rerun unchanged. Replacements split the full immutable receiver/selected-slot window from the actual enumerate/index destination/full mutable-vector frame. No timeout or cap increase. Controls K012/K013 in the original queue were not launched.
