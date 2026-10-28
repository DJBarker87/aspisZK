# Native/release compilation consistency

**Differences first: the native results are not, by themselves, proofs of the deployed SBF program.** Frozen source/lock identity does not imply identical feature selection, target lowering, or harness semantics. No source change or release-target weakening is proposed.

1. **Different evaluator bodies:** direct `cargo kani --manifest-path .../crates/aspis-r1-cost-probe/Cargo.toml --lib` runs (NBA/NBB/NBF/NBO/NBZ/NCG and NBY samples) select default `private-leaf-salts`, but do **not** select `optimized-terminal` or `program-build`. Both release verifier builds select all three. `optimized-terminal` expands into twelve statement features, selecting active-mask basis, packed digest/selector tensor, binary Copy weights, endpoint caching, semantic factorization, pattern windows, Copy tag/finish dots and packed ranges. Relevant reached bodies are enumerated below. A proof of an unaffected helper can transfer with its exact domain; an enclosing semantic/prepare result needs the selected-body association/equivalence, not merely a matching function name.
2. **Profile/overflow/assertions:** ordinary sampled Cargo Kani runs omit `--release`, set dev opt-level=3, usually dev debug=0, and often `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`. That last variable does **not** set the dev profile. Cargo dev normally keeps debug assertions and overflow checks; release SBF defaults omit both. The frozen workspace only explicitly enables release overflow checks for `aspis-r1-cert-check`/`aspis-r1-cert-build`, not these deployed crates. Actual retained release rustc commands have opt-level=3 and no override enabling overflow/debug checks. `debug=0` controls debug information, not assertions. Kani arithmetic/UB checks additionally impose proof obligations; they are not deployed instructions. Effective Kani rustc flags are not captured in every receipt: mark that as missing evidence rather than assuming profile identity. Transfer requires proving no checked overflow/debug-assert failure on the entire reached domain, or explicit wrapping/checked operations with the same behavior.
3. **Host versus SBF:** `cfg(kani)` instrumentation, host syscall implementations/stubs and host allocation differ from SBF. Pool also compiles a transaction-level invocation guard only for `target_os="solana"`; host execution omits that rejection. See [target inventory](NCR_TARGET_DEPENDENT.md). Setting host `target_os` by hand would not prove SBF semantics.
4. **Deployment constants:** default/devnet use identical Cargo features but different build-time Pool/registry IDs. Program Kani commands without those environment variables exercise defaults; generic authentication proofs must quantify over the concrete IDs or be instantiated separately. They do not thereby attest the devnet IDs.
5. **Verification replacements:** `cfg(kani)` modules, `kani::stub`/contracts, arbitrary digest replies, arithmetic replacements and KMX copying windows are proof abstractions with separate value/domain/caller obligations. Their implementations are not linked into the release ELF. Function-pointer-dependent PASS results remain quarantined under local rule14.
6. **Receipt-scope correction:** not every result in the named directories is a cargo-kani compilation of the entire frozen workspace. Later Kani reverify receipts, e.g. KNE_K001, invoke `kani-driver` on standalone `KNE_windows.rs`, checking the frozen Cargo graph separately. These are window lemmas with source-association obligations. Preserving a lock hash in their receipt does not make the standalone file a compiled release crate.

7. **Entrypoint suppressed in a native SDK lane:** `native-u04d-20261028/NCF_K063` selects `pool-adapter,private-leaf-salts,no-entrypoint`. The last feature cfg-excludes the `solana_program::entrypoint!` expansion (`programs/r1-cost-probe/src/lib.rs:20`); it is absent from both deployed verifier builds. This local SDK helper gate therefore does not cover the deployed entry ABI/panic expansion. Core adapter helper bodies may still agree. This additional variant is retained explicitly in the sample JSON.

## Exact release configuration

Source baseline `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; lock SHA256 `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. [Low2 build manifest](../lowering2-20261026/Low2_build_manifest.json) contains actual rustc arguments; [NCR_RELEASE_CFG.json](NCR_RELEASE_CFG.json) extracts their cfg/codegen/target switches. The sbf-identity recapture plan is **proposed**, so it is not treated as a successful build receipt; Low2 supplies the realized builds.

| Artifact | Cargo root / explicit features | Effective selected local features | Profile / target / flags |
|---|---|---|---|
| Default verifier | `programs/r1-cost-probe`; `pool-adapter,private-leaf-salts` | program: default/custom-heap, pool-adapter, private-leaf-salts; library: default, private-leaf-salts, optimized-terminal, program-build; core:r0; statement:r0,pool-v1-kernel plus twelve optimized features | release opt3; `sbpf-solana-solana`; platform-tools1.52 rustc1.89.0-dev/LLVM20.1.7; `RUSTFLAGS` unset, target flags `-C link-arg=--threads=4`; no test/kani/prover/profilers |
| Devnet verifier | Same | Same; `ASPIS_R1_POOL_PROGRAM_ID=BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs`, `ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q` | Same |
| Pool | `programs/aspis-pool`; `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit` | default, pair-forest-account-evidence, pair-forest-verifier-lane-invariant-audit plus explicit features; statement:pool-v1-kernel; core:no feature | Same release/target/codegen policy; no verifier optimized-terminal expansion |

Both verifier builds deliberately exclude the legacy `[1,k]`/`[2]` route. `pool-adapter` selects the actual dispatch. Private salts are already the library default; omission of an explicit `--features private-leaf-salts` in a direct library run is **not** a salt-format mismatch. `program-build` prohibits audit-eight-way and does not itself select a different successful arithmetic body.

## Function-family comparison

`K-lib` means direct frozen verifier-library default features; `K-program` means program root with `pool-adapter,private-leaf-salts`; `K-statement` means statement root with no feature flags, unless its retained scratch manifest supplies them; `K-window` is a standalone file. All are host x86_64 Linux / cfg(kani), not SBF. A manifest path or a frozen dependency graph does not prove the transitive *feature* graph: the latter must be checked separately.

| Verified family / representative receipt | Kani compilation | Deployed selection | Finding / transfer condition |
|---|---|---|---|
| Field arithmetic/reduction (LPf, LPg, LPh, LPi; NBS indices) | core defaults or K-lib; no r0-op-count/r0-r91-audit/r0-e4-reference | core:r0 in verifier, core default in Pool | Base field bodies have no active target branch; debug assertions and ordinary overflow differ; multiplication replacements need named value/domain laws |
| Compact scan, echeck, record decode/expand, private Dot (LPa/LPl/LPn, NCG, NBQ) | K-lib | same compact salt format; optimized dependencies enabled | Local selected helper bodies match apart from assertions/library lowering; no inference about full caller |
| Wide view, prepared claim, semantic boundary, circle sampler (LPo/LPp/LPt, NBA/NBR) | K-lib or later K-window | optimized terminal selected | Boundary/compact helper may be invariant; semantic finish/Claims producer must use release evaluator and exact saved values |
| Transcript/checkpoint/resume (LPm, NBB/NBF/NCG/NCI/NCD; KND/KNE windows) | K-lib or K-window; private salts default | private salts; prover/detail-phases absent | Domain tag matches; trace/mark no-op source matches with observer None, subject to pointer quarantine; window lemmas do not certify whole Vec writer |
| Query, geometry, residue/accumulate, binary multiproof/batch (NBB/NBF/NBO/NBZ/NCG; NBE/NBJ/NBV/NBY) | K-lib or K-window | same verifier algorithm/format and release optimized dependencies | `prover` branches absent in both; release arithmetic/allocator/caller association still owed |
| Semantic/Copy terminal, Poseidon/public validation | K-lib selects literal statement evaluator; direct statement builds often no optional features; explicit optimized helpers may require scratch feature additions | verifier selects all twelve optimized features; Pool does not | **Selected semantic bodies differ**; no universal native semantic-to-release transfer established by this audit |
| ASQ8/ASF8/ASR8, registry codecs/afterstate (NBH/NBK/NBN/NBU/NBX/NCC) | K-statement, sometimes scratch-exposed modules | verifier statement:r0,pool-v1-kernel + optimized features | Fixed codec body can agree; module availability differs. No-feature host module availability is not proof of SBF feature consistency |
| SDK runtime/error/observer/entry (NBC/NBG/NBP/NCK) | K-program, release feature expansion | same Cargo selection; default/devnet constants differ | Feature parity available here; syscall, allocator, ABI, debug/overflow and ID instantiation remain distinct |
| Kani diagnoses/mitigation/reverification | cargo Kani or standalone kani-driver; exact per-lane table below | no harness/stub module | Tool fidelity/regression/window evidence, not additional deployed function coverage |
| Pool settlement/CPI/entry | Not covered by verifier TX1/TX2 inventories or sampled library harnesses | separate pinned Pool ELF and feature set above | Do not count verifier proofs as Pool coverage; Solana-only entry guard and CPI/runtime remain explicit |

## Reached feature switches and assertions

The exact-body scan checks all345 TX1 and242 TX2 inventory spans against frozen SHA256 pins. [NCR_BODY_SCAN.json](NCR_BODY_SCAN.json) records only hits *inside* bodies (the initial broader [scan](NCR_REACHED_SCAN.json) also includes preceding attribute context). Static inventories are conservative, not compiler-certified dynamic reachability. This does not assert completeness for every SDK/std implementation or Pool lifecycle path.

<!-- GENERATED -->
| Reached body | Conditional/assertion lines |
|---|---|
| `crates/aspis-core/src/field.rs::add@62` | 63: #[cfg(feature = "r0-op-count")]<br>65: #[cfg(feature = "r0-r91-audit")]<br>67: #[cfg(all(feature = "r0-e4-reference", not(target_os = "solana")))]<br>83: #[cfg(not(feature = "r0-r91-audit"))] |
| `crates/aspis-core/src/field.rs::inv@213` | 214: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::mul@133` | 134: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::neg@122` | 123: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::reduce_u62@145` | 146: debug_assert!(value < (1u64 << 62)); |
| `crates/aspis-core/src/field.rs::sub@94` | 95: #[cfg(feature = "r0-op-count")]<br>97: #[cfg(feature = "r0-r91-audit")]<br>99: #[cfg(all(feature = "r0-e4-reference", not(target_os = "solana")))]<br>114: #[cfg(not(feature = "r0-r91-audit"))] |
| `crates/aspis-core/src/field.rs::add@896` | 897: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::mul@935` | 936: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::mul_m31@975` | 976: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::neg@916` | 917: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::square@951` | 952: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::sub@906` | 907: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::try_inv@1004` | 1005: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field.rs::qm31_sum_products_small@534` | 535: debug_assert!(N >= 2 && N <= 4); |
| `crates/aspis-core/src/field/wide_exact.rs::add@81` | 82: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field/wide_exact.rs::mul@112` | 113: #[cfg(feature = "r0-op-count")]<br>115: #[cfg(all(feature = "r0-e4-reference", not(target_os = "solana")))] |
| `crates/aspis-core/src/field/wide_exact.rs::mul_m31@190` | 191: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field/wide_exact.rs::mul_qm31@178` | 179: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field/wide_exact.rs::neg@101` | 102: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field/wide_exact.rs::square@139` | 140: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-core/src/field/wide_exact.rs::sub@91` | 92: #[cfg(feature = "r0-op-count")] |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark@75` | 76: #[cfg(feature="detail-phases")]<br>78: #[cfg(not(feature="detail-phases"))] |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_round@96` | 105: #[cfg(feature = "prover")] |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_rounds@133` | 136: #[cfg(feature = "prover")] |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_finish@232` | 233: #[cfg(not(feature = "prover"))]<br>235: #[cfg(feature = "prover")]<br>268: #[cfg(feature = "prover")]<br>301: #[cfg(feature = "prover")]<br>303: #[cfg(feature = "prover")]<br>305: #[cfg(feature = "prover")] |
| `crates/aspis-r1-cost-probe/src/sampler.rs::add_small_base_p@90` | 96: debug_assert!(addend <= 1); |
| `crates/aspis-r1-cost-probe/src/sampler.rs::gamma_sample@111` | 116: debug_assert!(!wrapped_again); |
| `crates/aspis-r1-cost-probe/src/sampler.rs::low_base_p_digits@56` | 70: debug_assert!(quotient[1..].iter().all(&#124;&limb&#124; limb == 0));<br>71: debug_assert!(quotient[0] <= 256); |
| `crates/aspis-r1-cost-probe/src/trace.rs::value@6` | 7: #[cfg(feature="prover")]<br>9: #[cfg(not(feature="prover"))] |
| `crates/aspis-r1-cost-probe/src/transcript.rs::new@7` | 8: #[cfg(not(feature = "private-leaf-salts"))]<br>10: #[cfg(feature = "private-leaf-salts")] |
| `crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node@277` | 283: #[cfg(feature="prover")] {a.weights[j]=weights.value(j);} |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::active@238` | 239: #[cfg(not(feature = "pool-v1-pair-forest-active-mask-basis-audit"))]<br>241: #[cfg(feature = "pool-v1-pair-forest-active-mask-basis-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::row@174` | 175: debug_assert!(row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1); |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::accumulate_endpoint_selector_tensor_basis@820` | 833: #[cfg(not(feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]<br>838: #[cfg(feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::evaluate_with_selectors@924` | 940: #[cfg(all(<br>945: #[cfg(all(<br>950: #[cfg(all(<br>955: #[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")]<br>961: #[cfg(all(<br>965: #[cfg(not(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit"))]<br>986: #[cfg(all(<br>990: #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]<br>1013: #[cfg(all(<br>1027: #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]<br>1039: #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]<br>1043: #[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")]<br>1064: #[cfg(all(<br>1073: #[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_selector_tensor_basis@850` | 857: #[cfg(not(feature = "pool-v1-pair-forest-copy-finish-dot-basis-audit"))]<br>870: #[cfg(feature = "pool-v1-pair-forest-copy-finish-dot-basis-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values@335` | 339: #[cfg(not(feature = "pool-v1-pair-forest-pattern-window-audit"))]<br>341: #[cfg(feature = "pool-v1-pair-forest-pattern-window-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_occupancy_lanes@544` | 553: #[cfg(not(feature = "pool-v1-pair-forest-semantic-factor-audit"))]<br>560: #[cfg(feature = "pool-v1-pair-forest-semantic-factor-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_path_lanes@408` | 419: #[cfg(not(feature = "pool-v1-pair-forest-semantic-factor-audit"))]<br>421: #[cfg(feature = "pool-v1-pair-forest-semantic-factor-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_value_lanes@480` | 517: #[cfg(not(feature = "pool-v1-pair-forest-packed-range-audit"))]<br>524: #[cfg(feature = "pool-v1-pair-forest-packed-range-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed@1124` | 1129: #[cfg(not(feature = "pool-v1-pair-forest-packed-digest-selector-tensor-audit"))]<br>1131: #[cfg(feature = "pool-v1-pair-forest-packed-digest-selector-tensor-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_initial_and_absorption@255` | 308: #[cfg(not(feature = "pool-v1-pair-forest-semantic-factor-audit"))]<br>317: #[cfg(feature = "pool-v1-pair-forest-semantic-factor-audit")] |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_packed@1157` | 1167: #[cfg(not(feature = "pool-v1-pair-forest-packed-digest-audit"))]<br>1173: #[cfg(feature = "pool-v1-pair-forest-packed-digest-audit")] |
| `crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1@278` | 290: debug_assert_eq!( |
| `crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace@362` | 409: debug_assert_eq!(round as usize, POSEIDON2_ROUNDS); |
| `crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw@217` | 244: debug_assert!(all_local_limbs_bounded);<br>257: debug_assert!(packed[0] < 8 * bound);<br>258: debug_assert!(packed[1] < 8 * bound);<br>259: debug_assert!(packed[2] < 4 * bound);<br>260: debug_assert!(packed[3] < 4 * bound); |
| `programs/r1-cost-probe/src/lib.rs::observer@36` | 37: #[cfg(feature="cu-profiling")] {Some(mark)}<br>38: #[cfg(not(feature="cu-profiling"))] {None} |
| `programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction@56` | 57: #[cfg(feature="pool-adapter")]<br>67: #[cfg(not(feature="pool-adapter"))]<br>83: #[cfg(target_os="solana")] |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1@447` | 458: #[cfg(feature="cu-profiling")] |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::pair@268` | 319: #[cfg(feature="prover")] |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2@463` | 468: #[cfg(feature="cu-profiling")] |

## Representative receipt lanes

120 sampled receipts across 61 lanes. These include failures/negative controls; sampling is configuration evidence, not proof credit. Full commands/environments/source pins/statuses are retained in [NCR_RECEIPT_SAMPLE.json](NCR_RECEIPT_SAMPLE.json); wrapper source in [NCR_WRAPPERS.json](NCR_WRAPPERS.json).

| Lane / first sampled receipt | Effective command class / features | Profile/flags |
|---|---|---|
| `kani-diag-20261027` / `KDX_K001` | `/home/dombarker/project-offloads/codex-cx-kani-diag-20261027/KDX_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `kani-diag2-20261028` / `KNB_K001` | `/home/dombarker/project-offloads/codex-cx-kani-diag2-20261028/KNB_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `kani-diag3-20261028` / `KNC_K001` | `/home/dombarker/project-offloads/codex-cx-kani-diag3-20261028/KNC_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `kani-mitig-20261028` / `KMX_K001` | `/home/dombarker/project-offloads/codex-cx-kani-mitig-20261028/KMX_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `kani-reverify1-20261028` / `KMY_K001` | `standalone /home/dombarker/project-offloads/codex-cx-kani-reverify1-20261028/KMY_windows.rs`; no explicit features | standalone profile unspecified; `-C opt-level=3` |
| `kani-reverify2-20261028` / `KMZ_K001` | `standalone /home/dombarker/project-offloads/codex-cx-kani-reverify1-20261028/KMZ_windows.rs`; no explicit features | standalone profile unspecified; `-C opt-level=3` |
| `kani-reverify3-20261028` / `KNA_K001` | `standalone /home/dombarker/project-offloads/codex-cx-kani-reverify1-20261028/KNA_windows.rs`; no explicit features | standalone profile unspecified; `-C opt-level=3 --edition=2021` |
| `kani-reverify4-20261028` / `KND_K001` | `standalone /home/dombarker/project-offloads/codex-cx-kani-reverify1-20261028/KND_windows.rs`; no explicit features | standalone profile unspecified; `-C opt-level=3 --edition=2021` |
| `kani-reverify5-20261028` / `KNE_K001` | `standalone /home/dombarker/project-offloads/codex-cx-kani-reverify1-20261028/KNE_windows.rs`; no explicit features | standalone profile unspecified; `-C opt-level=3 --edition=2021` |
| `leaf-p6-1-20261027` / `LPa_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-1-20261027/LPa_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-10-20261027` / `LPl_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-10-20261027/LPl_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-11-20261027` / `LPm_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-11-20261027/LPm_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-12-20261027` / `LPn_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-12-20261027/LPn_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-13-20261027` / `LPo_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-13-20261027/LPo_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-14-20261027` / `LPp_K002` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-14-20261027/LPp_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-15-20261027` / `LPq_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-15-20261027/LPq_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-2-20261027` / `LPb_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-2-20261027/LPb_crate/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-3-20261027` / `LPc_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-3-20261027/LPc_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-4-20261027` / `LPd_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-4-20261027/LPd_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-5-20261027` / `LPe_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-5-20261027/LPe_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-6-20261027` / `LPf_K004` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-6-20261027/LPf_src/crates/aspis-core/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-7-20261027` / `LPg_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-7-20261027/LPg_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-8-20261027` / `LPh_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-8-20261027/LPh_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `leaf-p6-9-20261027` / `LPi_K001` | `/home/dombarker/project-offloads/codex-cx-leaf-p6-9-20261027/LPi_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-p6-20261026` / `NP6_K001` | `NP6_claims/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=4` |
| `native-prepare1-20261027` / `NBA_K002` | `/home/dombarker/project-offloads/codex-cx-native-prepare1-20261027/NBA_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-prepare2-20261027` / `NBL_K002` | `/home/dombarker/project-offloads/codex-cx-native-prepare2-20261027/NBL_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-prepare3-20261028` / `NBR_K001` | `/home/dombarker/project-offloads/codex-cx-native-prepare3-20261028/NBR_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-prepare4-20261028` / `NCA_K002` | `/home/dombarker/project-offloads/codex-cx-native-prepare4-20261028/NCA_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-prepare5-20261028` / `NCH_K001` | `/home/dombarker/project-offloads/codex-cx-native-prepare5-20261028/NCH_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-query1-20261027` / `NBB_K001` | `/home/dombarker/project-offloads/codex-cx-native-query1-20261027/NBB_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-query2-20261027` / `NBF_K001` | `/home/dombarker/project-offloads/codex-cx-native-query2-20261027/NBF_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-query3-20261028` / `NBO_K001` | `/home/dombarker/project-offloads/codex-cx-native-query3-20261028/NBO_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-query4-20261028` / `NBW_K001` | `/home/dombarker/project-offloads/codex-cx-native-query4-20261028/NBW_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-query5-20261028` / `NBZ_K001` | `/home/dombarker/project-offloads/codex-cx-native-query5-20261028/NBZ_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-query6-20261028` / `NCG_K001` | `/home/dombarker/project-offloads/codex-cx-native-query6-20261028/NCG_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx1a-20261027` / `NBE_K001` | `wrapper; see snapshot`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx1b-20261027` / `NBI_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx1b-20261027/NBI_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx1c-20261027` / `NBJ_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx1c-20261027/NBJ_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx1d-20261027` / `NBM_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx1d-20261027/NBM_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx1e-20261028` / `NBV_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx1e-20261028/NBV_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx1f-20261028` / `NBY_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx1f-20261028/NBY_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx1top-20261028` / `NCL_K001` | `programs/r1-cost-probe (NCL_gate.py)`; pool-adapter,private-leaf-salts | dev; opt=3; `unrecorded` |
| `native-tx2a-20261027` / `NBC_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2a-20261027/NBC_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx2b-20261027` / `NBD_K003` | `/home/dombarker/project-offloads/codex-cx-native-tx2b-20261027/NBD_src/crates/aspis-statement/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx2c-20261027` / `NBG_K003` | `/home/dombarker/project-offloads/codex-cx-native-tx2c-20261027/NBG_src/programs/r1-cost-probe/Cargo.toml`; pool-adapter,private-leaf-salts | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx2d-20261027` / `NBH_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2d-20261027/NBH_src/crates/aspis-statement/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx2e-20261027` / `NBK_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2e-20261027/NBK_src/crates/aspis-statement/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx2f-20261027` / `NBN_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2f-20261027/NBN_src/crates/aspis-statement/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx2g-20261028` / `NBP_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2g-20261028/NBP_src/programs/r1-cost-probe/Cargo.toml`; pool-adapter,private-leaf-salts | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx2h-20261028` / `NBQ_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2h-20261028/NBQ_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx2i-20261028` / `NBS_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2i-20261028/NBS_src/crates/aspis-core/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx2j-20261028` / `NBU_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2j-20261028/NBU_src/crates/aspis-statement/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx2k-20261028` / `NBX_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2j-20261028/NBU_src/crates/aspis-statement/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-tx2l-20261028` / `NCB_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2l-20261028/NCB_src/crates/aspis-core/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx2m-20261028` / `NCD_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2m-20261028/NCD_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx2r-20261028` / `NCI_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2r-20261028/NCI_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx2top-20261028` / `NCK_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2top-20261028/NCK_src/programs/r1-cost-probe/Cargo.toml`; pool-adapter,private-leaf-salts | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-tx2w-20261028` / `NCJ_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2w-20261028/NCJ_src/crates/aspis-r1-cost-probe/Cargo.toml`; no explicit features | dev; opt=3; `-C link-arg=-Wl,--threads=1` |
| `native-u04c-20261028` / `NCC_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2j-20261028/NBU_src/crates/aspis-statement/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |
| `native-u04d-20261028` / `NCF_K001` | `/home/dombarker/project-offloads/codex-cx-native-tx2j-20261028/NBU_src/crates/aspis-statement/Cargo.toml`; no explicit features | dev; opt=3; `unrecorded` |

Additional feature variant: `native-u04d-20261028/NCF_K063` uses program features `pool-adapter,private-leaf-salts,no-entrypoint`; entrypoint expansion is excluded. Full receipt is included in the sample JSON.
