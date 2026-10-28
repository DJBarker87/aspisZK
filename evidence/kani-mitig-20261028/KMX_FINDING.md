# KMX copy mitigation finding — interrupted, incomplete

Frozen release revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Frozen lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
Toolchain inherited from setup: cargo-kani 0.67.0 / CBMC 6.8.0.

## Result

The only completed configuration pair in this packet is K002: one `u32`
(4 bytes), array destination of equal length, offset zero, `copy_from_slice`.
The source value is 512. The expected-value assertion fails while the assertion
that the destination is zero **passes**. This disagrees with native Rust copy
semantics and confirms that the discrepancy is not restricted to 16 elements.
This resumed session has not executed a native replay. The prior diagnostic
packet supplies the native 16-element reproducer; do not generalize its native
receipt to all configurations below.

K001: compilation failure (no verification result). K003: compilation failure,
missing `-Z stubbing` (no stub validation). K004: launcher failure before Kani,
no terminal receipt; unresolved and never resubmitted.

## Mandatory stop

`S2W_run_host.py`, line 12, failed while snapshotting configured sources:

```
FileNotFoundError: [Errno 2] No such file or directory:
/home/dombarker/project-offloads/codex-cx-kani-mitig-20261028/KMX_src/crates/aspis-r1-cost-probe/src/KMX_native.rs
```

See `KMX_K004-launcher.log`, `KMX_K004_UNRESOLVED.json`, and
`KMX_TRANSPORT.jsonl`. The scope command exited 1. Admission had exit 0 and
`allowed:true`; the failure was not a refusal or transient transport exit 255.
The launcher produced no terminal receipt, wall/RSS/swap measurements, or Kani
result. Operating rule 5 requires stopping and reporting launcher/host failures
for the lead to fix; no infrastructure repair or further launch was attempted.
The next attempt must have a new identifier after the lead resolves the blocker.

## Configuration map

These are generated test shapes, not a completed characterization. Each has an
expected-value assertion and a separate wrong-value negative control. Larger
byte targets are represented by u8 and u32; this is not a full Cartesian sweep.

| ID | Type | Bytes | API | Destination | Offset | Extra elements | Result |
|---|---|---:|---|---|---:|---:|---|
| c000 | `u8` | 1 | slice | array | 0 | 0 | NOT RUN |
| c001 | `u8` | 2 | slice | array | 0 | 0 | NOT RUN |
| c002 | `u8` | 3 | slice | array | 0 | 0 | NOT RUN |
| c003 | `u8` | 4 | slice | array | 0 | 0 | NOT RUN |
| c004 | `u8` | 8 | slice | array | 0 | 0 | NOT RUN |
| c005 | `u8` | 16 | slice | array | 0 | 0 | NOT RUN |
| c006 | `u32` | 4 | slice | array | 0 | 0 | K002: expected FAIL / wrong PASS |
| c007 | `u32` | 8 | slice | array | 0 | 0 | NOT RUN |
| c008 | `u32` | 12 | slice | array | 0 | 0 | NOT RUN |
| c009 | `u32` | 16 | slice | array | 0 | 0 | NOT RUN |
| c010 | `u32` | 32 | slice | array | 0 | 0 | NOT RUN |
| c011 | `u32` | 64 | slice | array | 0 | 0 | NOT RUN |
| c012 | `u64` | 8 | slice | array | 0 | 0 | NOT RUN |
| c013 | `u64` | 16 | slice | array | 0 | 0 | NOT RUN |
| c014 | `u64` | 24 | slice | array | 0 | 0 | NOT RUN |
| c015 | `u64` | 32 | slice | array | 0 | 0 | NOT RUN |
| c016 | `u64` | 64 | slice | array | 0 | 0 | NOT RUN |
| c017 | `u64` | 128 | slice | array | 0 | 0 | NOT RUN |
| c018 | `[u8;32]` | 32 | slice | array | 0 | 0 | NOT RUN |
| c019 | `[u8;32]` | 64 | slice | array | 0 | 0 | NOT RUN |
| c020 | `[u8;32]` | 96 | slice | array | 0 | 0 | NOT RUN |
| c021 | `[u8;32]` | 128 | slice | array | 0 | 0 | NOT RUN |
| c022 | `[u8;32]` | 256 | slice | array | 0 | 0 | NOT RUN |
| c023 | `[u8;32]` | 512 | slice | array | 0 | 0 | NOT RUN |
| c024 | `KMX_Pair` | 8 | slice | array | 0 | 0 | NOT RUN |
| c025 | `KMX_Pair` | 16 | slice | array | 0 | 0 | NOT RUN |
| c026 | `KMX_Pair` | 24 | slice | array | 0 | 0 | NOT RUN |
| c027 | `KMX_Pair` | 32 | slice | array | 0 | 0 | NOT RUN |
| c028 | `KMX_Pair` | 64 | slice | array | 0 | 0 | NOT RUN |
| c029 | `KMX_Pair` | 128 | slice | array | 0 | 0 | NOT RUN |
| c030 | `u8` | 64 | slice | array | 0 | 0 | NOT RUN |
| c031 | `u32` | 64 | slice | array | 0 | 0 | NOT RUN |
| c032 | `u8` | 128 | slice | array | 0 | 0 | NOT RUN |
| c033 | `u32` | 128 | slice | array | 0 | 0 | NOT RUN |
| c034 | `u8` | 1024 | slice | array | 0 | 0 | NOT RUN |
| c035 | `u32` | 1024 | slice | array | 0 | 0 | NOT RUN |
| c036 | `u8` | 1736 | slice | array | 0 | 0 | NOT RUN |
| c037 | `u32` | 1736 | slice | array | 0 | 0 | NOT RUN |
| c038 | `u8` | 1768 | slice | array | 0 | 0 | NOT RUN |
| c039 | `u32` | 1768 | slice | array | 0 | 0 | NOT RUN |
| c040 | `u32` | 64 | ptr | array | 0 | 0 | NOT RUN |
| c041 | `u32` | 64 | clone | array | 0 | 0 | NOT RUN |
| c042 | `u32` | 64 | extend | vec | 0 | 0 | NOT RUN |
| c043 | `u32` | 64 | to_vec | vec | 0 | 0 | NOT RUN |
| c044 | `u32` | 64 | realloc | vec | 0 | 0 | NOT RUN |
| c045 | `u32` | 64 | slice | array | 0 | 1 | NOT RUN |
| c046 | `u32` | 64 | slice | array | 1 | 1 | NOT RUN |
| c047 | `u32` | 64 | slice | array | 3 | 5 | NOT RUN |
| c048 | `u32` | 64 | slice | vec | 0 | 0 | NOT RUN |

## Replacement status

`KMX_copy_stubs.patch` packages **unvalidated drafts** for slice copy, pointer
copy, Copy-only clone, vector extension and to_vec. `KMX_STUB_USAGE.md` records
usage and outstanding allocator/growth coverage. No stub is currently validated.
Native exhaustive-small and random-large checks are drafted, not run.
`lean/KMX_CopyMeaning.lean` is a draft meaning statement with four axioms-audit
commands; zero compiles and zero axioms results are available. No formal release
result is claimed.

## Exposure replay

Every row from `KDX_EXPOSURE.json` is retained below, including rows whose prior
audit excluded reached-copy exposure. NOT RUN is deliberately distinct from
PASS, FAIL and TIMEOUT: none of those outcomes can be assigned without a run.
The priority expand/checkpoint/wide_view/decode/prepared-claim work is pending.

| Original | Harness | New result |
|---|---|---|
| LPa_K004 | `compact::LPa_compact::LPa_expand_stage` | NOT RUN |
| LPa_K005 | `compact::LPa_compact::LPa_expand_alignment` | NOT RUN |
| LPa_K007 | `compact::LPa_compact::LPa_expand_length` | NOT RUN |
| LPa_K015 | `verifier::candidate::LPa_candidate::LPa_view_inactive` | NOT RUN |
| LPl_K015 | `compact::LPl_expand::LPl_fixed_probe` | NOT RUN |
| LPm_K001 | `verifier::LPm_verifier::weights_iterator` | NOT RUN |
| LPm_K003 | `verifier::LPm_verifier::selected_reference_write` | NOT RUN |
| LPm_K004 | `verifier::LPm_verifier::append32` | NOT RUN |
| LPm_K005 | `verifier::LPm_verifier::query_word_append` | NOT RUN |
| LPn_K001 | `compact::LPn_expand::LPn_step_frame` | NOT RUN |
| LPn_K010 | `r1_wire::LPn_decode::LPn_nonvacuity` | NOT RUN |
| LPo_K002 | `verifier::candidate::LPo_candidate::LPo_read_round0` | NOT RUN |
| LPo_K003 | `verifier::candidate::LPo_candidate::LPo_read_root` | NOT RUN |
| LPo_K004 | `verifier::candidate::LPo_candidate::LPo_read_round1` | NOT RUN |
| LPo_K005 | `verifier::candidate::LPo_candidate::LPo_read_final` | NOT RUN |
| LPo_K006 | `verifier::candidate::LPo_candidate::LPo_read_passthrough` | NOT RUN |
| LPo_K007 | `verifier::candidate::LPo_candidate::LPo_read_header` | NOT RUN |
| LPo_K009 | `verifier::candidate::LPo_candidate::LPo_inactive_copy` | NOT RUN |
| LPp_K004 | `transcript::LPp_usize_capture::LPp_usize_capture` | NOT RUN |
| LPp_K007 | `transcript::LPp_usize_capture::LPp_usize_capture` | NOT RUN |
| LPb_K016 | `LPb_harnesses::LPb_wide_six` | NOT RUN |
| LPe_K005 | `LPe_replay::LPe_wide_six` | NOT RUN |
| LPe_K015 | `LPe_replay::LPe_header_cut` | NOT RUN |
| LPe_K016 | `verifier::LPe_verifier::LPe_digest_prefix_cut` | NOT RUN |
| LPe_K017 | `verifier::LPe_verifier::LPe_roots_queries_cut` | NOT RUN |
| LPe_K018 | `verifier::LPe_verifier::LPe_private_put_cut` | NOT RUN |
| LPe_K019 | `verifier::LPe_verifier::LPe_semantic_z_cut` | NOT RUN |
| LPf_K027 | `verifier::LPf_verifier::LPf_checksum_projection` | NOT RUN |
| LPg_K011 | `compact::LPg_compact::LPg_expand_low` | NOT RUN |
| LPg_K012 | `compact::LPg_compact::LPg_expand_high` | NOT RUN |
| LPh_K018 | `compact::LPh_compact::LPh_live_before` | NOT RUN |
| LPh_K019 | `compact::LPh_compact::LPh_live_low` | NOT RUN |
| LPh_K020 | `compact::LPh_compact::LPh_live_high` | NOT RUN |
| LPh_K021 | `compact::LPh_compact::LPh_live_after` | NOT RUN |
| LPh_K027 | `verifier::candidate::LPh_candidate::LPh_nonempty` | NOT RUN |
| LPh_K028 | `verifier::candidate::LPh_candidate::LPh_empty_backed` | NOT RUN |
| LPi_K005 | `LPi_contracts::q_owned16` | NOT RUN |
| LPi_K006 | `LPi_contracts::q_parent32_left` | NOT RUN |
| LPi_K007 | `LPi_contracts::q_parent32_right` | NOT RUN |
| LPi_K008 | `LPi_contracts::q_parent32_middle` | NOT RUN |
| LPi_K009 | `LPi_contracts::q_parent48_middle` | NOT RUN |
| LPi_K010 | `LPi_contracts::q_parent48_right` | NOT RUN |
| LPi_K012 | `verifier::LPi_verifier::put_k_arbitrary_prefix` | NOT RUN |
| LPi_K013 | `verifier::LPi_verifier::put_e_arbitrary_prefix` | NOT RUN |
| LPi_K017 | `verifier::LPi_verifier::joined_digest_cut_small` | NOT RUN |
| LPi_K018 | `verifier::LPi_verifier::joined_digest_cut_physical` | NOT RUN |
| NP6_K006 | `NP6_construction::NP6_construct_all_errors` | NOT RUN |
| NP6_K025 | `NP6_ownership::NP6_owned_transfers_and_layout` | NOT RUN |
| NP6_K026 | `NP6_alloc::NP6_uninit_allocation_outcomes` | NOT RUN |
| NBE_K004 | `verifier::candidate::NBE_keys::NBE_sort` | NOT RUN |
| NBE_K005 | `multiproof::NBE_multiproof::NBE_zero_reject` | NOT RUN |
| NBI_K013 | `verifier::candidate::NBI_keys::NBI_key_read` | NOT RUN |
| NBI_K014 | `verifier::candidate::NBI_keys::NBI_index_equal` | NOT RUN |
| NBI_K015 | `verifier::candidate::NBI_keys::NBI_leaf_equal` | NOT RUN |
| NBI_K020 | `verifier::candidate::NBI_keys::NBI_duplicate_decision` | NOT RUN |
| NBC_K001 | `verifier::NBC_runtime::NBC_mark_none` | NOT RUN |
| NBC_K002 | `NBC_runtime::NBC_observer_none` | NOT RUN |
| NBH_K029 | `pool_v1::pair_forest_terminal::NBH_terminal::NBH_asf8_stores_gate` | NOT RUN |

## Confirmations and budget

**No earlier release-function result is confirmed by this mitigation packet.**
There are no new release-property counterexamples or native counterexample
replays. The false-PASS diagnostic remains active; earlier proof credit remains
suspended according to the background finding.

Newest-Kani installation and reproducer: NOT RUN. No version upgrade adopted.

Conservative configured-attempt count: 4/80 Kani (K001–K004), including two
compile failures and the pre-Kani launcher failure. Completed Kani verifications:
K002 only, two harnesses. Lean: 0/30. Rust native: 0/15. No budget exhaustion.
K001–K003 receipts record exact commands, exit status, time, RSS, swaps, source
revision/hashes and axioms N/A. K004 lacks a terminal receipt and is explicitly
unresolved. Existing cache is retained; no keys touched; no push. Repository
`crates/` and `programs/` were not edited. No cleanup command was run after the
launcher stop; own scratch target/temp status is therefore not claimed clean.
