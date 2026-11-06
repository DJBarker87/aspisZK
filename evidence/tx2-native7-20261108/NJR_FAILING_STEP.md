# Findings and failed attempts

NJR_K001 exited 1 before verification: staged NHR transport lacks tools/r1-builder-reference/tree.rs, required by the frozen statement crate under cfg(kani). Own input repair: supply the unchanged, already retained NJJ tools/r1-builder-reference sources. No verdict/no credit; retry is a changed-input attempt. No shared infrastructure modified.

NJR_K002 exited 1 before verification: missing cfg(kani) include of the exact KMX_stubs.rs at the scratch crate root. Own staging omission repaired by the same include retained by NJJ. No semantic verdict. K003 includes that repair and the new M05/M09 declarations.

NJR_K003 exited 1 before verification: exact KMX generic Vec helper requires allocator_api in the scratch crate. Added cfg_attr(kani,feature(allocator_api)), identical to predecessor setup. This is a changed-input compile repair, no proof verdict.
