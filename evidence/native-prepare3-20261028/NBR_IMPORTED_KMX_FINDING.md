# KMX copy mitigation finding

Frozen release revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Frozen lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Pinned cargo-kani 0.67.0 / CBMC 6.8.0. Scratch-only work; no release-source changes or toolchain adoption.


Summary: the one-u32 fixture exhibits a false-PASS on the pinned model. Six loop replacements have paired Kani controls, native differential checks and Lean value laws. Exposure replay outcomes: 18 PASS, 0 FAIL, 16 TIMEOUT, 0 NOT RUN, 24 EXCLUDED. TIMEOUT does not restore earlier proof credit.

## Configuration map

Each row has independent expected-value and wrong-zero controls. Native R002 checks all 49 original shapes and the loop replacements. R003 checks the three additional slice-parameter/literal shapes; R005 adds native value controls for 1, 255 and 256. These are concrete last-element observations, not a universal characterization of all inputs or compiler lowering. Source lengths are symbolic but constrained to the listed size, except slice_constant rows which use literal full-array copies; destinations start zeroed. A short copy uses a matching destination subslice of a larger backing allocation.

| ID | Type | Bytes | API / destination | Offset / extra | Expected / wrong | Interpretation |
|---|---|---:|---|---|---|---|
| c000 | `u8` | 1 | slice / array | 0 / 0 | PASS K009 / FAIL K009 | agrees on fixture |
| c001 | `u8` | 2 | slice / array | 0 / 0 | PASS K009 / FAIL K009 | agrees on fixture |
| c002 | `u8` | 3 | slice / array | 0 / 0 | PASS K009 / FAIL K009 | agrees on fixture |
| c003 | `u8` | 4 | slice / array | 0 / 0 | PASS K009 / FAIL K009 | agrees on fixture |
| c004 | `u8` | 8 | slice / array | 0 / 0 | PASS K009 / FAIL K009 | agrees on fixture |
| c005 | `u8` | 16 | slice / array | 0 / 0 | PASS K009 / FAIL K009 | agrees on fixture |
| c006 | `u32` | 4 | slice / array | 0 / 0 | FAIL K002 / PASS K002 | DISAGREES |
| c007 | `u32` | 8 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c008 | `u32` | 12 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c009 | `u32` | 16 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c010 | `u32` | 32 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c011 | `u32` | 64 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c012 | `u64` | 8 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c013 | `u64` | 16 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c014 | `u64` | 24 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c015 | `u64` | 32 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c016 | `u64` | 64 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c017 | `u64` | 128 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c018 | `[u8;32]` | 32 | slice / array | 0 / 0 | FAIL K030 / PASS K030 | DISAGREES |
| c019 | `[u8;32]` | 64 | slice / array | 0 / 0 | FAIL K031 / PASS K031 | DISAGREES |
| c020 | `[u8;32]` | 96 | slice / array | 0 / 0 | FAIL K032 / PASS K032 | DISAGREES |
| c021 | `[u8;32]` | 128 | slice / array | 0 / 0 | FAIL K033 / PASS K033 | DISAGREES |
| c022 | `[u8;32]` | 256 | slice / array | 0 / 0 | FAIL K034 / PASS K034 | DISAGREES |
| c023 | `[u8;32]` | 512 | slice / array | 0 / 0 | TIMEOUT K035 / TIMEOUT K035 | TIMEOUT |
| c024 | `KMX_Pair` | 8 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c025 | `KMX_Pair` | 16 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c026 | `KMX_Pair` | 24 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c027 | `KMX_Pair` | 32 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c028 | `KMX_Pair` | 64 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c029 | `KMX_Pair` | 128 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c030 | `u8` | 64 | slice / array | 0 / 0 | PASS K009 / FAIL K009 | agrees on fixture |
| c031 | `u32` | 64 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c032 | `u8` | 128 | slice / array | 0 / 0 | PASS K009 / FAIL K009 | agrees on fixture |
| c033 | `u32` | 128 | slice / array | 0 / 0 | FAIL K009 / PASS K009 | DISAGREES |
| c034 | `u8` | 1024 | slice / array | 0 / 0 | PASS K009 / FAIL K009 | agrees on fixture |
| c035 | `u32` | 1024 | slice / array | 0 / 0 | TIMEOUT K006 / TIMEOUT K006 | TIMEOUT |
| c036 | `u8` | 1736 | slice / array | 0 / 0 | PASS K006 / FAIL K006 | agrees on fixture |
| c037 | `u32` | 1736 | slice / array | 0 / 0 | TIMEOUT K006 / TIMEOUT K006 | TIMEOUT |
| c038 | `u8` | 1768 | slice / array | 0 / 0 | PASS K006 / FAIL K006 | agrees on fixture |
| c039 | `u32` | 1768 | slice / array | 0 / 0 | TIMEOUT K006 / TIMEOUT K006 | TIMEOUT |
| c040 | `u32` | 64 | ptr / array | 0 / 0 | FAIL K006 / PASS K006 | DISAGREES |
| c041 | `u32` | 64 | clone / array | 0 / 0 | FAIL K006 / PASS K006 | DISAGREES |
| c042 | `u32` | 64 | extend / vec | 0 / 0 | PASS K006 / FAIL K006 | agrees on fixture |
| c043 | `u32` | 64 | to_vec / vec | 0 / 0 | PASS K006 / FAIL K006 | agrees on fixture |
| c044 | `u32` | 64 | realloc / vec | 0 / 0 | PASS K006 / FAIL K006 | agrees on fixture |
| c045 | `u32` | 64 | slice / array | 0 / 1 | FAIL K006 / PASS K006 | DISAGREES |
| c046 | `u32` | 64 | slice / array | 1 / 1 | FAIL K006 / PASS K006 | DISAGREES |
| c047 | `u32` | 64 | slice / array | 3 / 5 | FAIL K006 / PASS K006 | DISAGREES |
| c048 | `u32` | 64 | slice / vec | 0 / 0 | PASS K006 / FAIL K006 | agrees on fixture |
| c049 | `u32` | 64 | slice_fn / slice | 0 / 0 | FAIL K036 / PASS K036 | DISAGREES |
| c050 | `u32` | 4 | slice_constant / array | 0 / 0 | PASS K037 / FAIL K037 | agrees on fixture |
| c051 | `u32` | 64 | slice_constant / array | 0 / 0 | PASS K038 / FAIL K038 | agrees on fixture |
| c052 | `u32` | 4 | slice_value_1 / array | 0 / 0 | FAIL K039 / PASS K039 | DISAGREES |
| c053 | `u32` | 4 | slice_value_255 / array | 0 / 0 | FAIL K039 / PASS K039 | DISAGREES |
| c054 | `u32` | 4 | slice_value_256 / array | 0 / 0 | FAIL K039 / PASS K039 | DISAGREES |

Across the 55 tested configurations: 34 DISAGREES, 17 agrees on fixture, 4 TIMEOUT, 0 NOT RUN. The symbolic-length array/slice u32 fixtures also disagree at values 1, 255 and 256 (R005 native controls), so this is not specific to 512. Direct full-array literal copies of one and sixteen u32 elements agree (K037/K038). The source/lowering distinction is observed, not an established internal cause.


The observed disagreement includes one u32 (4 bytes), so it is not restricted to the original 64-byte fixture. Flat byte copies and the tested Vec variants must not be generalized to untested shapes. For nested arrays, the original bounds counted outer elements and underbounded equality loops. K030–K035 change those source bounds to 35, covering the 32-byte equality loop, and retain the original failed drafts. Only completed adequately bounded pairs receive a classification. Larger typed-copy timeouts remain inconclusive. Internal model root cause remains open.

## Validated replacements

Six explicit element-loop replacements are packaged in [KMX_copy_stubs.patch](KMX_copy_stubs.patch); [KMX_STUB_USAGE.md](KMX_STUB_USAGE.md) gives attributes, preconditions and scope. K008: all six expected controls PASS; all six negative controls FAIL; no unwinding failure. R002: optimized native differential, 1,466,538 checks across exhaustive small inputs and seeded larger inputs, all five types and 49 matrix shapes. L003: `lean/KMX_CopyMeaning.lean` compiles; indexed copy, frame, append and retained-prefix laws have only accepted axioms. This is a value-level specification, not a proved Rust-to-Lean refinement.

## Exposure replay

Only rows with a reached copy require mitigation replay. Other audit rows are retained as EXCLUDED with their original reason. Passing rows confirm only the original selected property under its original auxiliary stubs and assumptions; they do not establish an entire release function or bridge.

| Original | Harness | Result / attempt |
|---|---|---|
| LPa_K004 | `compact::LPa_compact::LPa_expand_stage` | PASS KMX_K013  |
| LPa_K005 | `compact::LPa_compact::LPa_expand_alignment` | EXCLUDED  Alignment rejection precedes the copy. No exposure on admitted domain; K023 PASS. |
| LPa_K007 | `compact::LPa_compact::LPa_expand_length` | EXCLUDED  Length rejection precedes the copy. No copy exposure on admitted domain; K024 TIMEOUT, no new pass. |
| LPa_K015 | `verifier::candidate::LPa_candidate::LPa_view_inactive` | TIMEOUT KMX_K014  |
| LPl_K015 | `compact::LPl_expand::LPl_fixed_probe` | PASS KMX_K016  |
| LPm_K001 | `verifier::LPm_verifier::weights_iterator` | TIMEOUT KMX_K017  |
| LPm_K003 | `verifier::LPm_verifier::selected_reference_write` | TIMEOUT KMX_K018  |
| LPm_K004 | `verifier::LPm_verifier::append32` | TIMEOUT KMX_K019  |
| LPm_K005 | `verifier::LPm_verifier::query_word_append` | TIMEOUT KMX_K020  |
| LPn_K001 | `compact::LPn_expand::LPn_step_frame` | TIMEOUT KMX_K040  |
| LPn_K010 | `r1_wire::LPn_decode::LPn_nonvacuity` | PASS KMX_K015  |
| LPo_K002 | `verifier::candidate::LPo_candidate::LPo_read_round0` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPo_K003 | `verifier::candidate::LPo_candidate::LPo_read_root` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPo_K004 | `verifier::candidate::LPo_candidate::LPo_read_round1` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPo_K005 | `verifier::candidate::LPo_candidate::LPo_read_final` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPo_K006 | `verifier::candidate::LPo_candidate::LPo_read_passthrough` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPo_K007 | `verifier::candidate::LPo_candidate::LPo_read_header` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPo_K009 | `verifier::candidate::LPo_candidate::LPo_inactive_copy` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPp_K004 | `transcript::LPp_usize_capture::LPp_usize_capture` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPp_K007 | `transcript::LPp_usize_capture::LPp_usize_capture` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPb_K016 | `LPb_harnesses::LPb_wide_six` | TIMEOUT KMX_K021  |
| LPe_K005 | `LPe_replay::LPe_wide_six` | TIMEOUT KMX_K022  |
| LPe_K015 | `LPe_replay::LPe_header_cut` | PASS KMX_K023  |
| LPe_K016 | `verifier::LPe_verifier::LPe_digest_prefix_cut` | TIMEOUT KMX_K024  |
| LPe_K017 | `verifier::LPe_verifier::LPe_roots_queries_cut` | TIMEOUT KMX_K025  |
| LPe_K018 | `verifier::LPe_verifier::LPe_private_put_cut` | PASS KMX_K026  |
| LPe_K019 | `verifier::LPe_verifier::LPe_semantic_z_cut` | TIMEOUT KMX_K027  |
| LPf_K027 | `verifier::LPf_verifier::LPf_checksum_projection` | TIMEOUT KMX_K041  |
| LPg_K011 | `compact::LPg_compact::LPg_expand_low` | PASS KMX_K042  |
| LPg_K012 | `compact::LPg_compact::LPg_expand_high` | PASS KMX_K043  |
| LPh_K018 | `compact::LPh_compact::LPh_live_before` | PASS KMX_K044  |
| LPh_K019 | `compact::LPh_compact::LPh_live_low` | PASS KMX_K045  |
| LPh_K020 | `compact::LPh_compact::LPh_live_high` | PASS KMX_K046  |
| LPh_K021 | `compact::LPh_compact::LPh_live_after` | PASS KMX_K047  |
| LPh_K027 | `verifier::candidate::LPh_candidate::LPh_nonempty` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPh_K028 | `verifier::candidate::LPh_candidate::LPh_empty_backed` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| LPi_K005 | `LPi_contracts::q_owned16` | PASS KMX_K048  |
| LPi_K006 | `LPi_contracts::q_parent32_left` | PASS KMX_K049  |
| LPi_K007 | `LPi_contracts::q_parent32_right` | PASS KMX_K050  |
| LPi_K008 | `LPi_contracts::q_parent32_middle` | PASS KMX_K051  |
| LPi_K009 | `LPi_contracts::q_parent48_middle` | PASS KMX_K052  |
| LPi_K010 | `LPi_contracts::q_parent48_right` | PASS KMX_K053  |
| LPi_K012 | `verifier::LPi_verifier::put_k_arbitrary_prefix` | TIMEOUT KMX_K054  |
| LPi_K013 | `verifier::LPi_verifier::put_e_arbitrary_prefix` | TIMEOUT KMX_K055  |
| LPi_K017 | `verifier::LPi_verifier::joined_digest_cut_small` | TIMEOUT KMX_K056  |
| LPi_K018 | `verifier::LPi_verifier::joined_digest_cut_physical` | TIMEOUT KMX_K057  |
| NP6_K006 | `NP6_construction::NP6_construct_all_errors` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NP6_K025 | `NP6_ownership::NP6_owned_transfers_and_layout` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NP6_K026 | `NP6_alloc::NP6_uninit_allocation_outcomes` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NBE_K004 | `verifier::candidate::NBE_keys::NBE_sort` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NBE_K005 | `multiproof::NBE_multiproof::NBE_zero_reject` | EXCLUDED  n==0 or n>16 rejects before loops and copy; no exposure on admitted domain; no replay. |
| NBI_K013 | `verifier::candidate::NBI_keys::NBI_key_read` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NBI_K014 | `verifier::candidate::NBI_keys::NBI_index_equal` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NBI_K015 | `verifier::candidate::NBI_keys::NBI_leaf_equal` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NBI_K020 | `verifier::candidate::NBI_keys::NBI_duplicate_decision` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NBC_K001 | `verifier::NBC_runtime::NBC_mark_none` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NBC_K002 | `NBC_runtime::NBC_observer_none` | EXCLUDED  Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match. |
| NBH_K029 | `pool_v1::pair_forest_terminal::NBH_terminal::NBH_asf8_stores_gate` | PASS KMX_K058  |

## Newest release comparison

[Kani 0.68.0](https://github.com/model-checking/kani/releases/tag/kani-0.68.0), the latest published release at the lookup, was installed in a private scratch Rust toolchain (R004). CBMC is 6.11.0. The published Linux bundle SHA-256 is `32e2b484d73ede0bbf64a2cf0879c4259422497d8aec4ee67d448de9ae7843d3`; installer verification and version output are retained in `KMX_LATEST_INSTALL.json` and R004.

K029 runs the smallest one-u32 fixture without stubs: expected-512 **FAIL**, wrong-zero **PASS** (0/44 failing checks for the false assertion). The discrepancy therefore persists on this configuration in the newest release. K028 was an own-wrapper option error (omitted `-Z unstable-options`) before verification, corrected for K029. The dependency-free standalone source uses the private driver; the frozen scratch workspace graph is validated offline before invocation and its lock hash checked after. No release-function credit or toolchain upgrade is adopted.

K059 repeats the pair with explicit `RUSTFLAGS=-C opt-level=3` and verbose compiler evidence. The recorded `kani-compiler` command contains `-C opt-level=3`: expected-512 **FAIL**, wrong-zero **PASS** (0/39 failing checks for the false assertion). This optimized result is the final newest-release comparison.


## Execution and limitations

K004 was our omitted-input launcher error: `KMX_native.rs` was uploaded after admission KMX_UPLOAD4. K005 continued successfully; K004 remains a failed pre-Kani attempt, not a verification result. K001/K003/K007 were failed setup drafts. K010 failed on missing harness imports/helpers. K011 exposed additional unused historical contract attributes and incomplete auxiliary stub snapshots; scratch overlays were corrected without changing any selected property. L001/L002 were failed Lean drafts. Receipts, source snapshots, graph validation and exact commands are retained per attempt.

Conservative configured attempts: Kani 59/80; Lean 3/30; Rust 5/15. Each admitted build uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, one scope at a time. Cargo graph is validated against the copied frozen lock offline before each gate; before/after hashes are recorded. Optimized Rust profile. Persistent cache retained; no keys touched; no push.

**Confirmed earlier properties:** LPa_K004, LPl_K015, LPn_K010, LPe_K015, LPe_K018, LPg_K011, LPg_K012, LPh_K018, LPh_K019, LPh_K020, LPh_K021, LPi_K005, LPi_K006, LPi_K007, LPi_K008, LPi_K009, LPi_K010, NBH_K029. No complete release-function confirmation is claimed beyond the selected passing properties.

## Earlier results confirmed, by target

| Target | Confirmed earlier property IDs | Remaining selected properties |
|---|---|---|
| compact::expand_values | LPa_K004, LPl_K015, LPg_K011, LPg_K012, LPh_K018, LPh_K019, LPh_K020, LPh_K021 | LPn_K001 TIMEOUT |
| r1_wire::ValidatedRecord::decode_k | LPn_K010 | none |
| verifier::checkpoint / append stages | LPe_K015, LPe_K018 | LPm_K001 TIMEOUT, LPm_K003 TIMEOUT, LPm_K004 TIMEOUT, LPm_K005 TIMEOUT, LPe_K016 TIMEOUT, LPe_K017 TIMEOUT, LPe_K019 TIMEOUT, LPf_K027 TIMEOUT, LPi_K012 TIMEOUT, LPi_K013 TIMEOUT, LPi_K017 TIMEOUT, LPi_K018 TIMEOUT |
| QM31::write_le_bytes (existing CM31 byte stub retained) | LPi_K005, LPi_K006, LPi_K007, LPi_K008, LPi_K009, LPi_K010 | none |
| candidate::wide_view | none | LPa_K015 TIMEOUT |
| prepared_claim serializer stages | none | LPb_K016 TIMEOUT, LPe_K005 TIMEOUT |
| ASF8 stores helper (original local gate, not full release serializer) | NBH_K029 | none |

These confirmations restore only the named harness results under their retained assumptions. No complete P6 leaf, composed bridge or release-function theorem is promoted by this packet. No exposure replay has produced a concrete property counterexample if the FAIL count above is zero; TIMEOUT supplies no counterexample to replay natively. Native wrong-zero refutations for diagnostic fixtures are R002/R003/R005.


The K006 outer timeout ended before its in-process after-lock check; this missing contemporaneous check is retained as a limitation. Subsequent graph checks found the pinned lock unchanged. No unchanged timeout was resubmitted. The nested-array retry changes a demonstrably inadequate source bound; no memory cap or timeout was raised. Detailed target, exit status, wall time, peak RSS/cgroup memory, swap, source revision/hashes and axioms are in `KMX_LEDGER.json` and the individual receipts.

## Final audit

496 frozen scratch source files were checked. Only 7 intended scratch parent overlays differ; selected property bodies remain unchanged apart from namespace. No repository crates/programs were edited. All preexisting coherent/cache objects are unchanged. Own Cargo target, native binaries and solver scratch were removed; the persistent cache and installed scratch toolchain were retained. `KMX_CLEANUP.json` records exact hashes and removals. Final exposure table has no NOT RUN rows among the 34 reached-copy targets. No source counterexample was found; 16 TIMEOUT rows remain unconfirmed.
