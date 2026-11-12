# Aspis Pool program: first release-style translator emission (task X2, stage 1)

Status: a tool record. It says which functions of the frozen Pool program, and of the Aspis library code it links,
the Charon and Aeneas tools translate, and whether the emitted Lean elaborates against the R1 (L187) library.
Nothing here is a proof. A translated, elaborated function is not a verified function.

Source: frozen commit 3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de, host tree `W/src-frz-a` (read only; nothing under
`crates/` or `programs/` was changed or copied for the emission). `W` = `~/project-offloads/future-version-20261111`
on the build host. Everything below ran in `fv_slot.sh` scopes (MemoryHigh 6G, MemoryMax 8G, no swap), one at a time.

## Files

| File | Content |
|---|---|
| `rows.tsv` | one row per Aspis function or constant in scope, for each overflow setting (column `overflow_checks`; `off` is the deployed setting) |
| `externals.tsv` | every bodiless declaration of the final (overflow-off) package, classed |
| `shims.tsv` | every shim definition in the package and the Rust item it models |
| `not-emitted.tsv` | per crate, every function with a body in the LLBC that has no emitted definition, with the reason |
| `named-gaps.json` | every item made opaque by name, with the exact Aeneas (or Charon) message and the triggering construct |
| `compare-frza.tsv` | statement and core functions emitted both here and in the freeze emission (`W/frz-emit/frza`, scopes s, d, c), compared at overflow checks on |
| `overflow-off-vs-on.tsv` | every emitted function: emitted text with overflow checks off against on |
| `../host/fv_x2_*` | the scripts and configs |

## What was run

Tools, checked by hash at the start of every run (the hashes of the freeze emission README):
Charon 454586e9 `charon` 57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851, `charon-driver`
6a6552bce70d59e041fb96a67c08294377ef16d3f77a7876fea7f1250ee37845; Aeneas 0d21a9ec
230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91. Lean 4.32.0 against the L187 objects by reference
(`codex-cx-replay-l187-20261109/objs` and `base_ref`; nothing written there).

Charon (`fv_x2_run.py`, the command line and environment of `fv_frz_emit_run.py`):
`charon cargo --preset aeneas --mir built --sysroot default --include core::option::Option --include core::result::Result
--include core::option::_::ok_or --start-from <roots> --opaque <opaque items> --include aspis_statement --include aspis_core
--dest-file out.llbc -- --manifest-path programs/aspis-pool/Cargo.toml --locked --offline --release --lib --jobs 4
--features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`, with
`RUSTUP_TOOLCHAIN=nightly-2026-09-17`, `CARGO_PROFILE_RELEASE_CODEGEN_UNITS=2`, `RAYON_NUM_THREADS=1`, cargo target
directories `W/x2/target/off` and `W/x2/target/on`. `Cargo.lock` was unchanged in every run.
Overflow off (deployed): `RUSTFLAGS=-Zthreads=1 -C link-arg=-Wl,--threads=1`, no `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS`.
Overflow on: `RUSTFLAGS=... -C overflow-checks=yes` and `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`.

Aeneas: `aeneas -diagnose-translation -sequential -no-progress-bar -abort-on-error -backend lean -namespace AspisX2
-dest raw -subdir AspisX2 -split-files out.llbc` (exploratory runs without `-abort-on-error`).

Lean: the four modules adapted by the freeze emission's `TP_adapt.py` with `fv_x2_rules.json` (the rules of
`TP_rules_release.json` minus the two verifier-only `compact.`/`weights.` module-qualification rules; rules applied to
`Funs`: 0 linter option, 1 shim import, 2 to 6 the five shim names, 11 joining broken applications), compiled one at
a time by `fv_x2_lean_one.sh` (`lean -j1 -M7000 -DElab.async=false`, timeout 1200 s), shim `AspisTPNewLib` first.
No new shim was written. The raw (unadapted) Aeneas output of every run is kept on the host beside the adapted copy.

### Deployed build settings

The deployed ELF (`W/out/PL-frz-a/cmd.txt`) is `cargo-build-sbf` 3.1.13 `--manifest-path programs/aspis-pool/Cargo.toml
--features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit
--skip-tools-install --offline -j 4 -- --locked` (release profile; `env_exact.txt` sets no overflow variable).

Resolved features (`cargo tree -e normal -f '{p}|{f}'`, `fv_x2_tree.sh`, run `X2-tree`, exit 0), identical for the host
target and for `sbpf-solana-solana` with the platform tools' cargo (v1.54):
- `aspis-pool`: default, pair-forest-account-evidence, pair-forest-source-invariant-audit,
  pair-forest-source-result-invariant-audit, pair-forest-verifier-lane-invariant-audit, r1-split-checkpoint
- `aspis-statement`: pool-v1-kernel
- `aspis-core`: none

Overflow checks: the workspace `Cargo.toml` has no `[profile.release]` table; its only profile overrides set
`overflow-checks = true` for `aspis-r1-cert-check` and `aspis-r1-cert-build`, which are not in this build. The program
manifest has no profile. So the deployed setting for `aspis-pool`, `aspis-statement` and `aspis-core` is the release
default: overflow checks off (and debug assertions off). This is read from the manifests and the recorded build
environment; the ELF itself was not inspected for it.

Target: Charon compiles for the host target (x86_64). Within the emitted functions the only `cfg(target_os)`
difference is `processor.rs:502`: the call `require_transaction_level_invocation_v1(get_stack_height())?` exists only
for `target_os = "solana"`, so the emitted `process_instruction` does not contain the transaction-level CPI check that
the deployed program runs first. (`field.rs:67` is also gated, but by a feature that is off on both targets.)
`debug_assert!` sites in emitted functions are compiled out in both the deployed build and the emission.

### Runs

| Run (attempt) | What | Exit | Wall (scope) | Peak RSS | Scope memory peak | Memory events |
|---|---|---|---|---|---|---|
| `X2-r1-off` | entry root, everything transparent, Aeneas without abort | Aeneas stopped by me (143) | Charon 59 s; Aeneas 14 min | Aeneas 6.4 GB | at MemoryHigh, 81 % stall | high 447,468 |
| `X2-offA-1` | deposit handler opaque, its callees as roots; Aeneas without abort (the rejection list) | Aeneas 1 | 77.5 s Aeneas | 3,596,964 kB | | |
| `X2-offA-rec` | the same LLBC, Aeneas `-loops-to-rec` | 1 | 92 s | | | |
| `X2-dep-ncd-1` | deposit handler alone, Charon `--no-code-duplication` | Aeneas 2 | 8.5 s | 278,060 kB | | |
| `X2-offR*` | iterations of the opaque list and roots | | | | | |
| `X2-final-off` | final, overflow off (deployed) | 0 | 2:29.57 | 2,993,812 kB | 2,964,877,312 B | none (oom 0) |
| `X2-final-on` | final, overflow on (comparison) | 0 | 5:06.25 | 3,409,024 kB | 3,793,592,320 B | none (oom 0) |

Per step, final runs (exit, wall, peak RSS kB):

| Step | off | on |
|---|---|---|
| Charon | 0, 3.2 s (cached deps), 331,820 | 0, 123.1 s (cold), 726,268 |
| Aeneas `-abort-on-error` | 0, 89.0 s, 2,863,868 | 0, 115.1 s, 3,409,024 |
| Lean shim `AspisTPNewLib` | 0, 3.2 s | 0, 3.0 s |
| Lean `TypesExternal` | 0, 2.1 s, 0 errors | 0, 2.9 s, 0 errors |
| Lean `Types` | 0, 7.5 s, 0 errors | 0, 11.5 s, 0 errors |
| Lean `FunsExternal` | 0, 2.7 s, 0 errors | 0, 2.6 s, 0 errors |
| Lean `Funs` | 1, 24.8 s, 56 errors, 2,993,812 | 1, 32.7 s, 49 errors, 2,980,224 |

### Hashes (sha256, copied from the run results)

LLBC: off e9c0edeb91869f89b7453f455f75dcddf9e1ad8ada1eda039ed8c3c2cd64e5f0 (876 function declarations);
on fff3b7ceef711b162497ffdb821899c90f87ad43af014fcbb01d531d446b1ac1 (877). The first full-entry LLBC (run r1-off,
410 MB) d2330669eadff53f3d2a6133b128a9e4dfce28985b4a2308be8bdc848226f602.

Raw Aeneas output (`W/x2/final-*/runs/A-release/raw/AspisX2/`):

| File | off | on |
|---|---|---|
| `Funs.lean` | 725effc1958fbbfbbf012e210fa2e95d36595e27587f31f13e21e16f191fa5cd | 72a864b4ed9a404af84eb40a298440f282c650a464199915b990935d223023c8 |
| `FunsExternal_Template.lean` | 6c8e3effdf59a01864de926b1eebd9fc1cfcf7dc7823799ce9b00ac4a63ec8fd | 6c8e3effdf59a01864de926b1eebd9fc1cfcf7dc7823799ce9b00ac4a63ec8fd |
| `Types.lean` | e254ff4a9b1446aee920bcafb454b98a5d48f59dfce80a36704be5805a5e2134 | e254ff4a9b1446aee920bcafb454b98a5d48f59dfce80a36704be5805a5e2134 |
| `TypesExternal_Template.lean` | 060f66dce033ed574f489fc09e348b7f18089881d87aa9df80eab438c923b373 | 060f66dce033ed574f489fc09e348b7f18089881d87aa9df80eab438c923b373 |

Adapted Lean (`W/x2/final-*/lean-src/`):

| Module | off (`AspisX2off*`) | on (`AspisX2on*`) |
|---|---|---|
| `Funs` | 6b97d96085c581e1e7f43f82e531afe2760fa082e0d37c1d620f2c4f3888d8c7 | 4bd4553504d8b2632cdf379427c1b493c4052ee4742841b7d241e62417b8f8e6 |
| `FunsExternal` | 2565c821d9f3dfe0cd252d98f88024aa39ea7d6c746979778b0991e362561c8d | abdbd69dbba6c57d7765d2b3013b75f3b874cad513ad5a3082ee02ee5ca5664b |
| `Types` | 361421717afafcd6fbf2a583fcbc89f86b08907eb8a7fe18f543190c9b26f597 | a33dd0add92c305cede5fd96a9e6eec6065ffcd659663ec484812051a815e963 |
| `TypesExternal` | 2424a6f0aa9415aa492dae3493582e65a0f7095fc6acaac6f60c81e43aac26ac | 2424a6f0aa9415aa492dae3493582e65a0f7095fc6acaac6f60c81e43aac26ac |

Shim `AspisTPNewLib` 13f0700ef54893b0fcef4741dc76ac212b66d7efdf1f11bf8af5215873a8f81a (unchanged). Configs:
`fv_x2_cfg_final_off.json` and `fv_x2_cfg_final_on.json` (in `../host/`; their hashes are in each run's `result.json`).

## Roots

The single root `crate::processor::process_instruction` (the function `entrypoint!` calls) was accepted by Charon;
everything in the Pool crate, `aspis_statement` and `aspis_core` transparent. That LLBC was 410 MB, 370 MB of it one
body (below), and Aeneas could not finish on it inside the cap. The final runs therefore make every rejected function
opaque by name and add, as extra roots, every Aspis function called directly by an opaque function (108 roots in
all, listed in the config), so that nothing reachable from the entry leaves the emission because an opaque function
hides it. The dispatch module and the three spend-path entries are covered through these roots; see "Handlers".

## Totals (overflow off, the deployed setting)

Rows: one per function or constant with a doc block in `Funs` or `FunsExternal` (the freeze emission's row rule;
closures and loop bodies count for their function), plus one row per in-scope function with no doc block.

| Crate | In scope | Translate and elaborate | Translate only | Named gap (opaque) | Not translated (dropped by the tool) |
|---|---|---|---|---|---|
| aspis_pool | 186 | 137 | 13 | 36 | 0 |
| aspis_statement | 244 | 209 | 7 | 7 | 21 |
| aspis_core | 8 | 8 | 0 | 0 | 0 |
| all | 438 | 354 | 20 | 43 | 21 |

Overflow on: 359 / 15 / 43 / 21 (the wrapping-shift signature errors below do not arise there).

Body hashes: the Pool ledger's convention (`NIK_census.py` on branch `research`, `evidence/pool-borrow-20261107/`,
line 58): tree-sitter 0.25.2 with tree-sitter-rust 0.24.2; for each `function_item` with a body, key =
`<path>::<enclosing mod and fn names and impl type texts, outermost first>::<name>`, `body_sha256` = sha256 of the
body block's bytes from `{` to `}`. The same convention is used for the library crates (`fv_x2_bodyhash.py`).
Constants have no body hash; four function rows were not matched to a parsed function and have none either (the
`PoolCpiRuntimeV1` impl row of `SolanaPoolCpiRuntimeV1`, `ValidatedIncrementalMerkleTreeV1::from_parts` and
`::into_inner`, and the constructor function `PoolV1PairForestTerminalFormatErrorV1::Payment`). Against the pin
c7593d23fdc56fcee9a9df1628d5f63b52ac7a95 by the same convention, the overflow-off rows with a hash are 221 unchanged,
7 changed and 5 new (column `changed_vs_pin_c7593d23fdc`). In the Pool crate these are the page-check change only:
`page_bytes_are_zero` new; `validate_root_page_bytes`, `require_program_owned_zeroed`,
`account_is_zeroed_program_page` changed (`validate_new_page_account` is not reached from the entry). In
`aspis_statement` they are the decoder rewrites the freeze README lists as reshaped in the pass
(`validate_master`, `decode_pool_v1_pair_forest_master_v1`, `decode_pool_v1_pair_forest_checkpoint_v1`,
`decode_pool_v1_pair_verified_afterstate_v1`, `decode_afterstate_frontier_v1`) and the new helpers
`any_lane_sequence_above_capacity`, `lane_sequences_at`, `any_nonzero_byte`.

## What is not translated, and why

Named gaps (43, `named-gaps.json`, each with the exact message of the exploratory non-aborting run):
- Loops: return inside nested loops (`require_unique_accounts`, `exact_five_accounts`, `exact_five_withdrawal_accounts`,
  `plan_pool_v1_pair_forest_checkpoint_v1`); early return inside a loop (`validate_root_page_bytes`,
  `decode_lane_account_from_program_invariant_v1`, `plan_pair_forest_terminal_dispatch_with_bytes_v1`); break to an
  outer loop (`process_pair_forest_initialize_with_runtime_v1`); `Unexpected return` (`validate_with_empty_roots`).
- AccountInfo data access: `Unreachable` (Aeneas `Interp.ml` line 686) at the call of the SDK method `try_borrow_data`
  (`plan_fresh_program_pda`, `validate_exact_deposit_delta_v1`, `validate_exact_withdrawal_delta_v1`,
  `decode_lane_account`, `require_initialized_empty_vault`, `classify_nullifier_marker_account_v1`), `data_is_empty`
  (`create_or_allocate_pda_with_rent`, `create_or_allocate_with_seed_with_rent`, `plan_vault_initialization`),
  `data_len` (`require_forest_mint_account`); also `Unreachable` in `plan_legacy_deposit/withdrawal_transfer_from_identity_v1`
  and `plan_pair_forest_nullifier_marker_consumption_v1`.
- `Unimplemented` in `translate_end_abs_identity` with no attribution line: `exact_transfer_account_infos_v1`,
  `exact_withdrawal_transfer_account_infos_v1` (slice pattern over accounts, clones into an array),
  `dispatch_pair_forest_terminal_readonly_v1`, `proof_transport_verifier`, `plan_pair_forest_terminal_dispatch_v1`.
- Function items passed as closures (their FnOnce/FnMut shims rejected): `process_pair_forest_terminal_v1`,
  `note_commitment`, `decode_with_empty_roots`.
- Higher-ranked lifetime constraint: `process_pair_forest_terminal_with_verifier_v1`; its signature cannot be
  translated, so it has no declaration at all.
- `Inconsistent projection: PtrMetadata`: `invoke_pair_forest_terminal_with_runtime_v1`,
  `authenticate_verifier_selection_v1`, `_v2`. `Could not match the contexts`: `encode_lane_from_authenticated_result_v1`,
  `encode_pool_v1_pair_forest_checkpoint_v1`. Nested borrows: `decode_checkpoint_lanes_box_v1`. Region-abstraction
  join: `ValidatedIncrementalMerkleTreeV1::append_one`. Internal errors in closures: `require_alias_free`,
  `require_checkpoint_distinct`, `stored_lane_bump`, `PoolV1PairLeafWitnessV1::validate`.
- `process_pair_forest_deposit_with_runtime_v1` (the deposit handler): no message. Charon reconstructs a
  369,603,777-byte body (code after each of the three page-mode branches and each `?` exit is duplicated); Aeneas
  reached the 6 GiB MemoryHigh and stalled (run r1-off, stopped). With Charon `--no-code-duplication` the body is 10 MB
  but Aeneas rejects it and 54 other functions with `Breaks to outer loops are not supported yet` (run dep-ncd). No
  flag resolved it.

Tool flags tried: Aeneas `-loops-to-rec` (no change: the same 45 rejections), Charon `--no-code-duplication` (worse).
No other Aeneas or Charon option addresses these messages. A std shim cannot resolve any of them: none is a missing
library item. Every one needs a source change (stage 2, not done here).

Not translated (21, `not-emitted.tsv`, reason "dropped by the tool"): `aspis_statement` functions reachable from the
entry only through named gaps (for example `pool_v1_note_commitment`, `decode_verifier_registry_v1/v2`,
`decode_verifier_registry_entry_v1/v2`, `decode_pool_v1_nullifier_marker`, `hash_fields`, `note_commitment_with`).
They are in the LLBC with a body, but Aeneas emits a non-local function only when an emitted definition uses it, and
none does. Their own closures are emitted without them. Some of them are emitted and elaborate in the freeze
emission's decoder scope (`aspis_statement` local there).

Translate only (20, overflow off): the `Funs` errors, classed in `rows.tsv` column `lean_error_class`:
- library item missing from the old library: `Iterator::map/any/all/sum` fields, `IterMut` iterator instance,
  `Option::map`, `Result::map` (`matches_verifier_owner`, `external_linear_lazy`, `decode_tree_image_unvalidated`,
  one `IncrementalMerkleTreeV1` method);
- library signature differs: `wrapping_shl`/`wrapping_shr` with a non-`u32` shift amount (overflow off only:
  `pack_pool_v1_pair_forest_marker_seed_v1`, `validate_pair_forest_request_accounts_v1`, `next_pair_forest_lane_v1`,
  `internal_linear_lazy`, one `IncrementalMerkleTreeV1` method);
- library encoding differs: `?` on a value that holds a mutable borrow (`try_borrow_data`'s `Ref<&mut [u8]>`); the
  emitted code expects `branch` to return a backward function, the old shim does not (`require_program_owned_zeroed`,
  `decode_master_account`, `account_is_zeroed_program_page`, `validate_lane_current_page`,
  `decode_retained_pair_forest_checkpoint_account_v1`, `process_pair_forest_checkpoint_with_runtime_v1`);
- other: `process_instruction` (implicit type argument of `Result::is_err` not inferred), `initialize_vault_account`
  (a local named `vault` shadows the module `vault`), `plan_pair_forest_spend_layout_v1` (expected a product type,
  got `Option AccountInfo`), `merkle_node_compress_v3` and `hash_fields_with_trace` (closure instance type mismatch).
These are recorded, not modelled. Whether they elaborate against the pinned Aeneas commit's own library is unchecked.

## Handlers

`process_instruction` dispatches on the magic: `AS8I` initialize, `AS8C` checkpoint, `AS8D` deposit, `ASQ8` terminal
(the `ASF8` and pair-afterstate branches are disabled by the deployed features). Status, overflow off:
- `AS8I` `process_pair_forest_initialize_with_runtime_v1`: named gap (break to an outer loop).
- `AS8C` `process_pair_forest_checkpoint_with_runtime_v1`: translates; does not elaborate (library encoding of `?`).
- `AS8D` `process_pair_forest_deposit_with_runtime_v1`: named gap (size); its callees are roots.
- `ASQ8` `process_pair_forest_terminal_v1`: named gap (fn items as closures); it calls
  `process_pair_forest_terminal_with_verifier_v1`, whose signature does not translate; the dispatch
  `dispatch_pair_forest_terminal_readonly_v1` and its callees in `pair_forest_dispatch.rs` are named gaps except
  `require_verifier_program`, `supported_loader` and the result accessors, which translate and elaborate.
- `process_instruction` itself translates and does not elaborate (above), and lacks the SBF-only CPI check.

## Externals (`externals.tsv`, final overflow-off package: 111 bodiless declarations)

42 named gaps (the 43rd, `process_pair_forest_terminal_with_verifier_v1`, has no declaration), 38 std, 23 SDK, 8 Solana
runtime (`program::invoke`, `program::invoke_signed`, `set_return_data`, `Clock::get`, `Rent::get`,
`find_program_address`, `create_program_address`, `hashv`), no derived impl, no other. The SDK type `solana_rent::Rent` is opaque by a Charon flag
(its `f64` field has no Lean model in the old library; the Pool only passes it to SDK calls).

## Defect checks (final runs, both settings)

- Completeness per crate (`TP_llbc_scan.py`, one run per crate; `not-emitted.tsv`): `aspis_pool` 198 functions with a
  body, 7 not emitted, all derived `Clone`; `aspis_statement` 414, 130 not emitted: 36 derived impls, 73
  compiler-generated `{Builtin}` items, 21 dropped by the tool (above); `aspis_core` 10, 0 not emitted. No function is
  called by an emitted definition and lacks both a definition and an external declaration: Lean reports no unknown
  Aspis name, and the four textual references found are each function's own emitted closure.
- Mutable-borrow type arguments under an erased region: 0 for each crate with both `TP_llbc_scan.py` and
  `tp3_erased_scan.py` (as in the freeze README, this pair's Charon never writes an erased region there).
- Reversed mutable iterator: the source search over the three crates finds `crates/aspis-core/src/r0_transcript.rs:129`
  only (`base_p_digits`); it is not in the emission.
- No `sorry` in the final `Funs` (Aeneas ran with `-abort-on-error`; every rejected function is opaque).

## Overflow comparison (`overflow-off-vs-on.tsv`)

Of 400 emitted functions, 362 are identical and 38 differ (Pool 10, statement 25, core 3). Every difference is in
integer arithmetic: with overflow checks off (deployed) the emission uses the library's `wrapping_add/sub/mul/shl/shr`,
with checks on it uses the failing `+ - * <<< >>>` (for example `M31::add`, `M31::mul`, `reduce_u64`,
`append_roots_unchecked`, `plan_pair_forest_spend_layout_v1`).

## Comparison with the freeze emission (`compare-frza.tsv`, overflow on)

153 `aspis_statement`/`aspis_core` functions are emitted in both. After normalising namespaces, crate prefixes, shim
module names and the `rust_fun`/`rust_const` attributes, 146 are identical and 7 differ: a non-local constant written
inline here and bound with `←` there (`decode_pool_identity_v1`, both `digest_is_canonical`,
`decode_afterstate_frontier_v1`), `POOL_V1_PAIR_TREE_DEPTH` folded to `20` here and a reference to `POOL_V1_TREE_DEPTH`
there, and two owners under which the freeze emission groups additional closure instances. 89 are emitted only here.

## Rerun

1. Copy `../host/fv_x2_*.{sh,py,json}` to `W/x2/bin` (configs to `W/x2/config`); copy `W/frz-emit/bin/fv_frz_emit_run.py`
   to `W/x2/bin/frz/` and `W/frz-emit/bin/worker/*` to `W/x2/bin/worker/`.
2. `bash W/x2/bin/fv_x2.sh <name> 3600 W/x2/config/fv_x2_cfg_final_off.json W/x2/<out> charon,aeneas,scan,lean`
   (and the same with `fv_x2_cfg_final_on.json`); `fv_x2_cmd.sh tree 1800 W/x2/tree bash W/x2/bin/fv_x2_tree.sh`.
3. Locally: `fv_x2_bodyhash.py` at both revisions, then `fv_x2_rows.py`, `fv_x2_externals.py`, `fv_x2_notemitted.py`,
   `fv_x2_compare.py`, `fv_x2_overflow.py`, `fv_x2_assemble.py` on the fetched run directories.

## Not done, and unchecked

- Stage 2 (rewrites) is not done.
- Nothing was compiled against the pinned Aeneas commit's own Lean library (task X3); the 20 translate-only rows may
  change there.
- The deployed overflow setting is read from the manifests and the build environment, not from the ELF.
- The emission is of the host-target compilation; apart from the `cfg(target_os)` audit above, equivalence with the
  SBF compilation is not checked.
- `IncrementalMerkleTreeV1::append_one` matches the pattern `_::append_one` used for the Validated method (Charon does
  not parse an impl pattern with a lifetime argument); it is not reached in the final emission, so this has no effect
  on the rows.

# Stage 2 (in progress): rewrites on a scratch tree, by rejection class

Nothing below is applied to the repository or to the frozen tree. The scratch tree is `W/x2/rw-tree` (a copy of
`src-frz-a`); every rewrite is a `diff -u` patch against the frozen file in `rewrites/` (one per function; the
stack-height change is `process_instruction_stack_height_check.patch`), summarised in `rewrites.tsv`. Done: classes a
and b, and the target_os audit. Not done: classes c to g, the shadowing and inference rows, the native-library items
below, the deposit split.

## Reproducers (probe crate `W/x2/probe/a`; source `rewrites/probe-lib.rs`, manifest `rewrites/probe-Cargo.toml`)

Compiled with the same Charon/Aeneas flags as the Pool emission (config `fv_x2_cfg_probe_a.json`; the probe's lock was
derived offline from the frozen `Cargo.lock` with `cargo metadata --offline`). Runs `X2-probe-a1` to `X2-probe-a6`.

Class a, "Unreachable" at an AccountInfo SDK call. The SDK methods are already external (axioms in `FunsExternal`):
their bodies are not pulled in, so an opaque/exclude flag cannot change anything. The error comes from Aeneas
`interp/InterpProjectors.ml` line 84 (`VLoan _ -> Unreachable` in `apply_proj_borrows_on_shared_borrow`, found with
`-print-error-emitters`, run `X2-offA-emit`): when the SDK call's `&AccountInfo` argument is projected, the
AccountInfo value still holds a shared loan. Every borrow shape alone translates (probes a1-a9: guard held, temporary,
block-scoped, dropped, chained calls). The trigger (probes b7, b9, c2) is a comparison of an AccountInfo reference
field with a reference, `acc.key != e` or `acc.owner == p` with `e, p: &Pubkey`, earlier in the function than an SDK
call on the same account. Accepted shape (c1, c3): compare values, `*acc.key != *e`, `*acc.owner == x`.

Class b, loops. `?` or `return` inside nested loops is rejected (d0). Any loop in a function that holds an AccountInfo
value or reference is rejected with "Found a case of unsupported nested borrows" or "Could not match the contexts",
whatever the loop shape: `while` with a flag (d1), helper with the inner loop (d2), `for` with `break` (d3), helper
for the comparison (f1, f3), and even a loop over an array of copied `&Pubkey` in such a function (f2). Accepted
shapes: no loop at all (f4, ten comparisons written out); recursion over the slice (g1); keys copied out and the loop
in a helper that sees only `[Pubkey]` (g2). For loops over plain data (no AccountInfo in the function), a `while`
loop with an `ok` flag in its condition and the error returned after the loop translates (e1).

Class g (seen in passing): a slice pattern `let [a, b] = accounts else {..}` over `&[AccountInfo]` gives
"Inconsistent projection: PtrMetadata" (b8, c4, c5); a length check and indexing translates (c6).

## Result after classes a and b (run `X2-rw-ab`, deployed setting, LLBC aea72fd66db2236e1cf5c8c760df0734a471a4550ba103f796ab0e520f7a2d5e)

All 17 rewritten functions, the two new helpers and the stack-height wrapper's caller translate: Aeneas
`-abort-on-error` exits 0 with them no longer opaque (26 named gaps remain opaque, plus the deposit handler and the
runtime wrapper `runtime_stack_height_v1`). `cargo test --release` of the Pool crate with the deployed features: 78
passed, 0 failed on the frozen tree (`X2-test-frz`) and on the rewrite tree before and after the stack-height change
(`X2-test-rw1`, `X2-test-rw2`).

Native library (raw Aeneas output, zero edits, X3's Lean 4.36.0-rc2 library by reference, `fv_x2_native.sh`):
`TypesExternal`, `Types`, `FunsExternal` compile in both; `Funs` errors: frozen emission 55 (`X2-native-frz`), after
classes a and b 68 (`X2-native-rwab`). The count rises because 17 more functions reach `Funs`. Of the rewritten
functions, 9 elaborate natively (`create_or_allocate_pda_with_rent`, `create_or_allocate_with_seed_with_rent`,
`require_token_owned_account`, `plan_pair_forest_nullifier_marker_consumption_v1`, both `exact_five_*`,
`require_unique_accounts` and helpers, `require_transaction_level_invocation_v1`); the others fail on:
- `?` on `try_borrow_data` (a value holding a mutable borrow): "expected a product type", also with the native
  library (7 functions; also the probe's a3-a8). This needs its own reproducer and shape (next step: an explicit
  `match` on the borrow result).
- a local named `vault` shadowing the module `vault` (`require_initialized_empty_vault`, `plan_vault_initialization`,
  and `initialize_vault_account`): rename the binder (next step).
- an emitter line break (`plan_legacy_withdrawal_transfer_from_identity_v1`), and an application type mismatch in
  `validate_root_page_bytes` and `process_instruction` (not yet diagnosed).

## target_os sites in the Pool reachable from the entry

`processor.rs`: line 9 `use alloc::format` (solana only; unused on the path), line 13 `use get_stack_height`
(solana only), line 15 `use TRANSACTION_LEVEL_STACK_HEIGHT` (solana or test), lines 502-503 the call
`require_transaction_level_invocation_v1(get_stack_height())?` (solana only), lines 628-635 the predicate itself
(solana or test): `stack_height != TRANSACTION_LEVEL_STACK_HEIGHT` gives `CpiInvocationForbidden`. This is
validation logic present only in the SBF build. `pair_forest.rs:161` (`not(target_os = "solana")`) is the client-side
helper `pool_v1_pair_forest_terminal_bump_hints_v1`, not reachable from the entry; `lib.rs:84` re-exports it. The
rewrite (`process_instruction_stack_height_check.patch`) makes the predicate and its call ordinary code on every
target and leaves only the runtime boundary behind the cfg: `runtime_stack_height_v1()` is `get_stack_height()` on
SBF and the constant `TRANSACTION_LEVEL_STACK_HEIGHT` off chain (what the host build already did, so host tests are
unchanged). In the emission the wrapper is opaque by name as a runtime boundary.

## Silent-fault checks

Fault 1, writes through a reversed mutable iterator: the source search over the three crates finds only
`aspis-core/src/r0_transcript.rs:129`, not in any emission (frozen or rewrite tree). The class a and b rewrites add
no `rev()`.

Fault 2, writes through a copied `Box` in optimized MIR: (a) 15 emitted functions involve a `Box`, all in the Pool
crate (local, built MIR, not the optimized MIR of a dependency): `decode_checkpoint_master_box_v1`,
`prepare_deposit_append_v1`, `decode_deposit_lane_box_v1`, `decode_terminal_request_box_v1`,
`decode_terminal_master_box_v1`, `decode_terminal_checkpoint_box_v1`, `decode_terminal_lane_box_v1`,
`terminal_common_box_v1`, `transfer_terminal_statement_box_v1`, `withdrawal_terminal_statement_box_v1`,
`next_lane_image_box_v1`, `terminal_result_bytes_box_v1`, `decode_forest_initialization_box_v1`,
`forest_master_image_box_v1`, `genesis_lane_image_box_v1` (`pair_forest.rs` lines 704 to 1977). Each builds a `Box`
from a value with `Box::new` and reads or returns it; none writes through a `Box` or takes `&mut Box`. No
`aspis_statement` or `aspis_core` function in the emission involves a `Box`. The SDK's account data reaches Aspis
code only through `Rc<RefCell<&mut [u8]>>` borrows (`try_borrow_data` / `try_borrow_mut_data` giving `Ref` /
`RefMut`), never as a `Box`. (b) so there is no write through a `Box` to compare; this was established by reading
the Rust source of the 15 functions, not by reading their emitted Lean. (c) `compare-frza.tsv`: 7 of 153 shared
functions differ beyond renaming; all 7 are representational (a non-local constant inline here and bound with `←`
there in `decode_pool_identity_v1`, both `digest_is_canonical`, `decode_afterstate_frontier_v1`;
`POOL_V1_PAIR_TREE_DEPTH` folded to `20`; two owners where the freeze emission groups extra closure instances). The
lines are in the `note` column of `compare-frza.tsv`.
