# R569 target-only masked-claim LLBC inspection

Capture only; no Aeneas translation, Lean compilation, runtime test, or verifier source edit. This report records the raw LLBC boundary for lead inspection.

## Capture receipt and pins

* Frozen source root: `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`; campaign source revision `4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35`, source freeze revision `6677d5f1310ff7373301fbd79f186278f772e68a`.
* Target: `aspis_core::state_only_hiding::begin_state_only_masked_sumcheck`, source `crates/aspis-core/src/state_only_hiding.rs`, SHA-256 `18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f`.
* Copied `crates/aspis-core/src`: 47 files; the staging runner compared every source/destination file hash before adding the probe. Full hash map is in `R569-prelaunch.json`. `build.rs` SHA `7905b8c2a92c72a79a8a6c785a91ce162fb338569a02867f671d1910e21b6e0d`; core `Cargo.toml` SHA `55c89bbbaf826ab428589ff81f8b422749a95ca96c0253bacb2a20dbba1e349c`; root `Cargo.lock` SHA `a1d2fc87435e98734f74a0fb1f070f1eaa5e5fe19266967092a7ea7849f8a91d`.
* Host `performance-host/Cargo.toml` SHA `62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c`; its lock SHA `a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814`. The only staged source edit was appending `claim_probe` to the copied host root `relation_callback.rs`; original SHA `4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`, staged root SHA `84fb98e93d368a7588c4dbd956e53731c4c1c1cac05fac5387cc1444ab267357`.
* Feature arguments: host features exactly `insecure-spend-fixture,selected-v7-kernels`, copied host feature declarations unchanged. Resolved active core feature is `v7-gamma-four-slot-block-audit`; the host feature also activates statement features `pool-v1-pair-forest-packed-digest-selector-tensor-audit`, `pool-v1-pair-forest-binary-copy-weights-audit`, `pool-v1-pair-forest-endpoint-selector-cache-audit`, `pool-v1-pair-forest-semantic-factor-audit`, `pool-v1-pair-forest-pattern-window-audit`, `pool-v1-pair-forest-copy-tag-dot-basis-audit`, `pool-v1-pair-forest-copy-finish-dot-basis-audit`, `pool-v1-pair-forest-packed-range-audit`, and `pool-v1-pair-forest-active-mask-basis-audit`. Core's original feature declarations were retained byte-for-byte. Rust flags are the exact selected file `evidence/r555-zero-output-rejoin/selected-rustflags.txt`, file SHA `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8`, normalized argv SHA `f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613`. Release overflow checks were explicitly set true; nightly `2026-06-01`; cargo jobs one, offline and locked.
* Charon path `/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon`, SHA `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`. Command and include list are fully recorded in `R569-prelaunch.json` and `launch.json`; it starts at `crate::claim_probe` and includes `core::option`, `core::result::_::map_err`, exact target function, `aspis_core::transcript`, and `aspis_core::field`. No broad `core::slice` include was used.
* Dedicated unit `aspis-r569-masked-claim-20261004.service`; cap MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128; aggregate campaign reservation preflight ≤40 GiB. Attempt B result: Charon exit 0, 41.15 s elapsed, GNU maximum RSS 637,544 KiB, swaps 0; cgroup unit runtime 41.616 s, memory peak 597.4 MiB, swap peak 0. Raw LLBC is `R569MaskedClaim.llbc`, SHA-256 `f359adc969db6fee290f0dab7d7c5cd7834918934ecf56b54d223b70f4022962`, 625,299 bytes, `has_errors=false`. `formal_axioms` is N/A for LLBC capture.
* Attempt A failed in a pre-capture manifest assertion because of a relative-key spelling mismatch. Its receipt and complete launcher inputs are preserved in `failed-attempt-a/`; it invoked no Charon and produced no LLBC. Attempt B changed that assertion and used a fresh remote destination.

## Captured target and call boundary

The LLBC target is `fun_decls[1]`, source file id 6 (`state_only_hiding.rs`), lines 377–389, `Structured`. Probe root is `fun_decls[0]` and makes only the call to target id 1. Target input signature is the concrete mutable `Transcript` reference plus `QM31`; return is `Result<QM31, StateOnlyHidingScheduleError>`.

The target's direct calls from its structured body are:

| LLBC declaration | Operation | Body classification |
| --- | --- | --- |
| 2 | core array `index_mut` | opaque trait implementation |
| 3 | selected QM31 `write_le_bytes` | structured source body |
| 4 | selected `Transcript::absorb` | structured source body |
| 5 | selected `challenge_nonzero_qm31` | structured source body |
| 6 | `Result::map_err` | structured core body |

The record initialization and two fixed array writes appear as LLBC builtins (`ArrayRepeat` and `Index` operations); the conversion in `map_err(StateOnlyHidingScheduleError::from)` is declaration 7 and has an opaque trait-implementation body in this extraction. Targeted transitive structured bodies include M31 `write_le_bytes` (9), `challenge_qm31` (17), QM31 `to_le_bytes` (21), and `squeeze_block` (22).

The LLBC contains opaque core operations in the dependency graph: array/slice `index_mut` (2, 8, 11, 13), slice `len` (10), `copy_from_slice` (12), array `index` (14, 26), iterator `into_iter` (15, 24), range/iterator `next` (16, 25), Result branch/`from_residual`/`unwrap` (18, 20, 28), `PartialEq::ne` (19), slice `iter_mut` (23), `try_into` (27), and `U32::from_le_bytes` (29). Declaration names, source kinds, body classification, and all discovered call edges are machine-readable in `llbc-inventory.json`.

The captured function source shows the write to `record[2..]`, absorb with the fixed claim label, then nonzero sampling and `map_err`. This report does not assign semantics to opaque declarations or assert that a translation can prove them. In particular, no `From` semantics were substituted for opaque declaration 7. Root should inspect the raw LLBC/dependency closure before any translation decision.
