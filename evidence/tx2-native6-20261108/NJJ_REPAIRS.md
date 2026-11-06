# Own input repair

K001 stopped at compilation: NHR staging omits tools/r1-builder-reference/tree.rs, reached under cfg(kani) in incremental_merkle.rs. No proof ran. K002 includes the identical frozen revision file (committed as NJJ_tree.rs.txt), and revalidates the same frozen graph and lock; no timeout or verdict is bypassed.

K002 exposed the analogous missing records.rs path. All frozen Rust sources in tools/r1-builder-reference are now committed in NJJ_FROZEN_TOOLS.json and staged together; no proof or model property changes.

K003 stopped before proof because the scratch crate did not include supplied KMX_stubs.rs. The cfg(kani)-only include is now identical to the predecessor; exact KMX hashes are still checked.

K004 stopped before proof: supplied KMX functions require allocator_api. Added the same cfg_attr(kani, feature(allocator_api)) used by NJC_, with no non-kani change.
