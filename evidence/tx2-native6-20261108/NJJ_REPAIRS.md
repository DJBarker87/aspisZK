# Own input repair

K001 stopped at compilation: NHR staging omits tools/r1-builder-reference/tree.rs, reached under cfg(kani) in incremental_merkle.rs. No proof ran. K002 includes the identical frozen revision file (committed as NJJ_tree.rs.txt), and revalidates the same frozen graph and lock; no timeout or verdict is bypassed.

K002 exposed the analogous missing records.rs path. All frozen Rust sources in tools/r1-builder-reference are now committed in NJJ_FROZEN_TOOLS.json and staged together; no proof or model property changes.

K003 stopped before proof because the scratch crate did not include supplied KMX_stubs.rs. The cfg(kani)-only include is now identical to the predecessor; exact KMX hashes are still checked.

K004 stopped before proof: supplied KMX functions require allocator_api. Added the same cfg_attr(kani, feature(allocator_api)) used by NJC_, with no non-kani change.

K016: one-window proof stopped on builtin memcmp unwinding at bound10 from whole-array assert_eq!, not a semantic counterexample or timeout. Replacement assertions check the same four u64 words individually, avoiding memcmp; bound10, timeout90 and memory caps unchanged, original pending_window name retained.

Audit input validation tightened before the first combined gate: fixture-mode receipts now pin NEP_Planted and NEP_Mutations themselves, instead of only the combined import. The walker, launcher and audit algorithm are unchanged. Expected same-binary fixture outputs are copied from the admitted NJC packet and compared exactly.
