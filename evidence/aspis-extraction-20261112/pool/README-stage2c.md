# Aspis Pool program: stage 2 rewrites, write boundary (task X2c)

Status: a tool record. It says which rewrites of the frozen Pool program, and of the two library crates it links,
make the Charon and Aeneas tools translate it from its single entry point, and whether the raw Aeneas output compiles
against the native Aeneas Lean library. Nothing here is a proof. A translated, elaborated function is not a verified
function, and nothing below is described as proved or established.

Source: frozen commit 3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de. Work tree `W/x2c/rw-tree` (a copy of X2b's
`W/x2b/rw-tree`); `W` = `~/project-offloads/future-version-20261111` on the build host. Nothing was applied to the
repository worktree, `W/src-frz-a`, `W/x2`, `W/x2b`, `W/x1*` or `W/x3`. Every heavy command ran in one `fv_slot.sh`
scope at a time (MemoryHigh 6G, MemoryMax 8G, no swap), attempt names `X2c-*`.

Tools: X2's runner `fv_x2_run.py` unchanged (Charon 454586e9, Aeneas 0d21a9ec, hashes checked at every run), deployed
feature list, overflow checks off; native compile `fv_x2b_native.sh` (raw `Types`, `Funs` and the two generated
templates, zero edits, Lean 4.36.0-rc2 against X3's native library under `W/x3`, read only).

## Files

| File | Content |
|---|---|
| `rewrites3/*.patch` | one cumulative `diff -u` per changed source file, against the FROZEN file (new files against /dev/null). They supersede X2's `rewrites/*.patch` and X2b's `rewrites2/*.patch` for the same files; applied to the frozen files they reproduce `W/x2c/rw-tree` exactly (checked: patch, then `diff -r`) |
| `rewrites3/frozen-test-tree__pool__pair_forest.patch` | the test-only recorder added to a copy of the FROZEN `pair_forest.rs` (tree `W/x2c/frz-test-tree`) for the state comparison |
| `rewrites3/checker-negatives/` | the write-boundary grammar checker's planted cases and its output |
| `rewrites3.tsv` | one row per rewritten function |
| `write-boundary.md` | the boundary function, its contract, its callers, each handler's writes in frozen order |
| `../host/fv_x2c_*` | scripts and configs of this task |

## Step 1: X2b's unread runs

- `X2b-pool-r5` (emission, Aeneas without abort): exit 124 (timeout 3000 s). Scope memory peak 6,723,620,864 B with
  813,990 MemoryHigh events: Aeneas stalled at the cap. Charon exit 0 (LLBC
  d7e97e0d7afa679f80585ca8aa0f133215b3f78250569f880b2426e833af5fa2, 966 functions). The only rejection logged before
  the stall: `invoke_pair_forest_terminal_with_runtime_v1`, "Nested borrows are not supported yet" at
  `pair_forest_dispatch.rs` 353-355 (the conditional push). Size census of that LLBC (`X2c-r5-sizes`): the settlement
  handler `process_pair_forest_terminal_with_host_v1` body was 8,759,732 bytes, the deposit handler 1,513,038, the
  next largest 1.16 MB. The settlement body is the stall.
- `X2b-test-r5` (tests): exit 0; Pool 82 passed, 0 failed; statement `x2b_` 2 passed.

## Step 2: the write boundary and the four handlers

See `write-boundary.md`. One boundary function (`account_write::write_account_data_v1`, 9 lines), opaque by name in
every emission. The Pool has no direct lamports write, so there is no lamports boundary. Handlers:

- Checkpoint: the two writes go through the boundary (checkpoint image, then master image).
- Settlement: split into four stages in the frozen order (`load_terminal_inputs_v1`, `prepare_terminal_marker_v1`,
  `verify_terminal_v1`, then the withdrawal settlement and `write_terminal_accounts_v1` / `write_terminal_page_v1`).
  The handler body is now a chain of stage calls; the 8.76 MB body is gone (Aeneas run c4: no MemoryHigh events).
- Deposit: stages `load_deposit_inputs_v1`, `select_deposit_page_mode_v1` (X2b), `plan_deposit_transfer_v1`,
  `prepare_deposit_writable_page_v1` (X2b), `settle_deposit_transfer_v1`, `write_deposit_accounts_v1`.
- Initialize: every loop over the eight lanes written out (planning, images, creation CPIs, zeroed checks, writes),
  in stage helpers `plan_initialize_accounts_v1`, `genesis_lane_images_v1`, `create_initialize_accounts_v1`,
  `require_initialize_accounts_zeroed_v1`, `write_initialize_accounts_v1`; this removes X2's named gap (break to an
  outer loop) and the `Vec` of `RefMut` guards.

Fresh root pages are written as their header-and-roots prefix (96 or 128 bytes) instead of zero-fill plus writes;
the pure helpers `root_page_header_bytes_v1`, `new_root_page_prefix_one_v1`, `new_root_page_prefix_two_v1`,
`root_page_append_one_v1` (`history.rs`) return the bytes. Why the account states are the same is argued in
`write-boundary.md` and checked by the state comparison below.

### State comparison, frozen against rewrite (coordinator item 4)

Method (`fv_x2c_test.sh`, `fv_x2c_compare_dumps.py`): in both a copy of the frozen tree and the rewrite tree, the
four handler names are shadowed inside the existing `pair_forest::tests` module by recording wrappers (identical
text in both trees; local items take precedence over the module's glob import). Each wrapper records, for every
account passed in, its key, owner, lamports and complete data before and after the call, and the result. Each test
of `pair_forest::tests` runs in its own process (so `Pubkey::new_unique` starts from the same counter in both
trees). This covers every fixture of the existing Pool tests, including all their rejecting inputs.

Run `X2c-test-frz1` (frozen tree) against `X2c-test-3` (rewrite tree after step 2): 12 tests call a handler; 1,083
handler calls in all, 22 accepted and 1,061 rejected; every record byte-identical; exit codes identical. One rejected
call leaves an account changed, identically in both trees: in
`terminal_marker_creation_fails_closed_rolls_back_and_rejects_replay` the nullifier marker is created by a System CPI
(test mock) before the verifier rejects. No frozen handler writes Pool account data before a later check: in all
four frozen handlers the data writes are the last account operations (frozen `pair_forest.rs` 1173-1188, 1796-1818,
2119-2122, 2185-2186), so a rejection by the frozen handler leaves only CPI effects, and the rewrite keeps that.

Final tree (run `X2c-test-c9` against `X2c-test-frz-c5`): the same 1,083 calls, byte-identical (`rewrites3/runs/compare-c9.txt`).

## Step 3: named gaps

- `invoke_pair_forest_terminal_with_runtime_v1` (conditional push into the CPI vectors): with `r1-split-checkpoint`
  the earlier `proof_transport_verifier` call has already rejected an empty `verifier_checkpoint`, so the frozen push
  and insert always ran; the account metas are built with the checkpoint in place (seven elements, no growth), and
  the account infos as a fixed array of eight (the CPI takes a slice). The `vec!` of AccountInfo values crashed Aeneas
  with an internal exception ("ty_regions shouldn't be called on erased or body regions"; located with `-log
  Translate,InterpStatements`, runs `X2c-c2-log`, `X2c-c3-log`, `X2c-c3-log2`: at the box of the eight-element
  AccountInfo array that `vec!` builds). Other feature combinations keep the frozen code.
- `plan_pair_forest_terminal_dispatch_with_bytes_v1` (early return inside a loop, `any` closure): the six pairwise
  key comparisons written out as value comparisons.
- `decode_lane_account_from_program_invariant_v1` (frontier loop with `?` and early return): the byte part moved to
  `decode_lane_bytes_from_program_invariant_v1` over `&[u8]`, a `while` with a failure code; differential test.
- `process_pair_forest_initialize_with_runtime_v1`: see step 2.
- `lane_keys_alias` (X2b's three-state loop; Aeneas "could not compute a loop fixed point", run `X2c-pool-c1`):
  the list [master, checkpoint, lanes] goes to `keys_repeat` (all pairs; 45 comparisons at eight lanes, as before).

## Step 4: the split handlers through the tools

| Attempt | Tree state | Charon | Aeneas | Native `Funs` |
|---|---|---|---|---|
| `X2c-pool-c1` | steps 2-3, single root, no abort | 0, 131.2 s, LLBC 07a263b4... (985 functions) | exit 2, 217 s: one rejection, `lane_keys_alias` (loop fixed point); no output written | not compiled |
| `X2c-pool-c2` | + `lane_keys_alias` via `keys_repeat`, abort | 0 | exit 2, 224 s: internal exception in `invoke_pair_forest_terminal_with_runtime_v1` (`vec!` of AccountInfo) | not compiled |
| `X2c-pool-c3` | + checkpoint account bound to a local | 0 | exit 2: same exception | not compiled |
| `X2c-pool-c4` | + infos as a fixed array | 0, LLBC 4e266247a7433753512d070b36f7e7e18ea075ddbc37e0d23fa817abd6dfb3af (985) | exit 0, 321.7 s, no MemoryHigh events | 45 errors in 18 declarations |

c4's 45 native errors: 5 in the Pool crate (a helper returning `[AccountInfo; 5]`, two binders named like modules,
the emitter line break in `plan_legacy_withdrawal_transfer_from_identity_v1`, the `is_err` inference row), the rest
in `aspis_statement` (`ok_or`, a `u8` shift amount, `iter_mut().enumerate()` loops, Poseidon2 trace callbacks) and
the std iterator instances that list `map`/`all`/`any`/`sum` because reached code uses them.

| Attempt | Tree state | Charon | Aeneas | Native `Funs` |
|---|---|---|---|---|
| `X2c-pool-c5` | + native-library fixes (Pool and statement), the five statement named gaps rewritten; only the boundary, `Rent` and `runtime_stack_height_v1` opaque | 0, LLBC 2530ba52435e419f08a7f486904d4ed171d543c3f87435aefeffa8144efe0cb5 (966) | exit 2, 36 s: "could not match the contexts" in the checkpoint planner's flag loop over the borrowed lanes | not compiled |
| `X2c-pool-c6` | + planner: per-lane helper written out, progress helper | 0, LLBC 448078b5af08ca8e43c1703079ff58f2591a28b9179258891492eda41456801d (968) | exit 2, 92 s: "nested borrows" in `plan_legacy_withdrawal_transfer_from_identity_v1` (the new authority helper took an account reference) | not compiled |
| `X2c-pool-c7` | + withdrawal helpers over values | 0, LLBC 4e70716be1504c20da2acc12ad6010799fd7ecdece38caca2364d8fb9926d725 (969) | exit 2, 115 s: "Unimplemented" at the `while` writing through the state in `external_linear_lazy` | not compiled |
| `X2c-pool-c8` | + loop-free Poseidon2 lazy linear layers | 0, LLBC 16637ad927b0321d69563673463c7ddd6308afd9fecfc3b5124195e4418d31c3 (967) | exit 0, 154 s | 67 errors in 3 declarations: a comparison stored in loop state (Prop for Bool), `read_discriminant` resolved inside the `From` impl's namespace, and one deep-nesting line break in `authenticate_verifier_selection_v2` (64 errors) |
| `X2c-pool-c9` | + error-code free function, v2 selection tail helper, progress scan with branches (FINAL tree) | 0, 34.9 s, LLBC dea71bd70afa620188a04fd544b5cf68aa900b105b72863f3a6200148c93b68a (969) | **exit 0**, 248.9 s; scope wall 5:50.53, peak RSS 2,397,120 kB, cgroup peak 2,526,650,368 B, 0 MemoryHigh events | **0 errors**: `TypesExternal` 0, `Types` 0, `FunsExternal` 0, `Funs` 0 |


## Step 5: the two library crates

Before patching, `../onchain/rewrites/` was searched for existing patches of the same functions (X1b's verifier-side
set): it patches `aspis-core/src/field.rs`, `aspis-statement/src/state_only_poseidon.rs` and the two
`pair_forest_*_terminal.rs` files, none of which this task touches; `../onchain/rewrites2/` did not exist. No
`aspis_core` function needed a change. Functions patched in `aspis_statement` (for the lead's merge with X1b's set):

| File | Functions |
|---|---|
| `poseidon2.rs` | `external_linear_lazy`, `internal_linear_lazy`, `permute_optimized`, `merkle_node_compress_v3`, `hash_fields`; new `permute_optimized_untraced` |
| `atomic_statement.rs` | `decode_digest_canonical` |
| `pool_v1/nullifier_marker.rs` | `digest_is_canonical` (private) |
| `pool_v1/pair_forest_accounts.rs` | `decode_pool_v1_pair_forest_lane_state_v1`, `encode_pool_v1_pair_forest_checkpoint_v1`, `plan_pool_v1_pair_forest_checkpoint_v1` |
| `pool_v1/incremental_merkle.rs` | `decode_tree_image_unvalidated`, `IncrementalMerkleTreeV1::validate_with_empty_roots`, `::reconstruct_nonfull_root_from_level`, `ValidatedIncrementalMerkleTreeV1::append_one`; new `append_one_core_v1`; X2b's `decode_with_empty_roots` change kept |
| `pool_v1/pair_tree_profile.rs` | `PoolV1PairLeafWitnessV1::validate` |
| `spend.rs` | X2b's `note_commitment` change only |

The traced Poseidon2 entry points (`permute_optimized_with_trace`, `hash_fields_with_trace`) are unchanged; they are
no longer reached from the Pool. Differential tests (frozen bodies kept under `#[cfg(test)]`): `x2c_linear_layers_
match_frozen`, `x2c_untraced_permutation_and_hashes_match_traced`, `x2c_same_result_as_frozen_body` (digest decoder,
tree image), `x2c_same_result_as_iter_all`, `x2c_append_and_validate_match_frozen`. The checkpoint planner and
encoder and the leaf-witness check are covered by the crate's existing tests and by the Pool state comparison
(checkpoint and deposit handlers).


## Step 6: the single-root run (`X2c-pool-c9`, final tree)

Config `../host/fv_x2c_cfg_c9.json`: root `crate::processor::process_instruction` only (X2's 108 extra roots dropped),
deployed feature list, overflow checks off. Opaque by name: `crate::account_write::write_account_data_v1` (the write
boundary), `crate::processor::runtime_stack_height_v1` (X2's one-line runtime wrapper of the stack-height syscall:
`get_stack_height()` on SBF, the transaction-level constant off chain; kept from X2, a runtime boundary, not a write),
and the SDK type `solana_rent::Rent` (Charon flag, as in X2). No other Aspis function is opaque; X2b's five
`aspis_statement` named gaps are rewritten and translated.

Aeneas `-abort-on-error` exits 0. The raw output compiles against the native library with zero edits and zero errors
(no regex adaptation, no shim, the generated templates as they are; `rewrites3/runs/native-errors-c9.txt`, inputs
`rewrites3/runs/native-inputs-c9.sha256`). No `sorry` in `Funs.lean`. Raw output sha256: `Funs.lean`
b8de70fae7269b41cc4ab808cdecfc4ecb4aa1c375d39d4081aa8ce5b460e713, `FunsExternal_Template.lean`
bd5f7c40ee27b0c3a391972e530cf47de1b1f4bd771c96066a9e31d035666edb, `Types.lean`
17e8080f027948a5453d30749a64a1c632c2670c94700bef402e0d67a85871fe, `TypesExternal_Template.lean`
cc468c968a4196ad6cb03695ca11e41ef5bdef38d3229bf83263ad2badba4e8c.

Bodiless declarations (the two external templates): std (`core`, `alloc`, slice and box instances), Solana SDK and
runtime items (`solana_pubkey`, `solana_system_interface`, `solana_sdk_ids`, `solana_account_info`, `solana_rent`,
`solana_program`, `solana_instruction`, `solana_hash`, `solana_sha256_hasher`, `solana_clock`), and exactly two Aspis
items: `account_write.write_account_data_v1` and `processor.runtime_stack_height_v1`. Named gaps left: none.

The four handlers, from the single root: `AS8I` `process_pair_forest_initialize_with_runtime_v1`, `AS8C`
`process_pair_forest_checkpoint_with_runtime_v1`, `AS8D` `process_pair_forest_deposit_with_runtime_v1`, `ASQ8`
`process_pair_forest_terminal_v1` / `process_pair_forest_terminal_with_host_v1`: each translates and elaborates, and each
writes account data only through calls of the bodiless boundary. Totals over the steps: named gaps 10 opaque items
(X2b r5 config) to 0 beyond the boundary and the runtime wrapper; native `Funs` errors 53 (X2b c12) to 45 (c4) to 67
(c8, more code reaching `Funs`) to 0 (c9); tests 82/82 (X2b r5) to 85/85 Pool and 273/273 statement.

## Step 7: checks

(a), (b), (c) of the emission: see `write-boundary.md`, section "Emission checks" (route check passes; two textual
read-before-write flags, both examined: exclusive dispatch branches, and an argument of the same call; the write order
matches the frozen order in all four handlers).

Silent-fault checks on c9: reversed mutable iterator sites in the three crates: `aspis-core/src/r0_transcript.rs:129`
only, not emitted (as in X2 and X2b); the rewrites add no `rev()`. Written-through `Box`: the new code holds `Box`
values only as struct fields that are moved and read (`TerminalInputsV1`, `TerminalVerifiedV1`, `DepositInputsV1`,
the initialize `Vec<Box<[u8; 768]>>`); nothing writes through a `Box`; the added `iter_mut` uses are all in test-only
code (frozen copies and test helpers). Erased-region scan: exit 0 for all three crates.

Tests (`cargo test --release`, deployed feature list, offline, locked; `fv_x2c_test.sh`):

| Run | Tree | Pool crate | Statement crate (all lib tests, feature pool-v1-kernel) |
|---|---|---|---|
| `X2c-test-frz-c5` | frozen copy (plus the test-only recorder) | 78 passed, 0 failed | 264 passed, 0 failed |
| `X2c-test-c9` | final rewrite tree | 85 passed, 0 failed | 273 passed, 0 failed |

The added Pool tests are X2b's and this task's differential tests and the updated lane-persistence surface test
(it counted the frozen write lines; it now counts the boundary calls and requires that no non-test code of
`pair_forest.rs` takes a mutable borrow and that `account_write.rs` holds exactly one). Handler state comparison
frozen against final: identical on 1,083 calls (above).

Compute (`fv_x2c_compute.sh`, run `X2c-compute-c9b`: the Pool ELF built from the final tree with the lead's
`fv_pool_build.sh` (tree `W/src-x2c-1`, ELF sha256 90ceb6ea67590a50f7f18901905f3b38871a10a4dbd93067c31030af373aeced),
replayed with the frozen verifier ELF and `PIN2_TRANSACTIONS.json` beside the frozen Pool in the same run; the tool exits
non-zero for both Pools because its two-transaction control differs from the recorded one, and the figures are read
from its output files, `rewrites3/runs/compute-c9/`):

| Payment (one transaction) | Frozen Pool | X2c Pool | Delta |
|---|---|---|---|
| Transfer, transaction CU | 1,232,920 | 1,231,515 | -1,405 |
| Withdrawal, transaction CU | 1,239,440 | 1,239,577 | +137 |

Verifier CU unchanged (1,184,299 and 1,181,418). In all four replays the one-transaction final state equals the
control's and rejected runs leave state unchanged except the payer fee. Neither delta exceeds 2,000 CU. The earlier
tree state c5 measured -1,397 and +84 (run `X2c-compute-c5`); the +53 between c5 and c9 on the withdrawal comes from the
withdrawal-path helpers added after c5 (`withdrawal_vault_authority_v1` over values with the eager `data_is_empty`
read, `withdrawal_vault_address_ok_v1`, `verifier_selection_from_entry_v2`). The transfer saving is consistent with
dropping the 8,256-byte zero fill of fresh pages, the `Vec` growth in the verifier CPI and the no-op Poseidon2 trace
copies, but no per-function attribution was measured. Deposit, checkpoint and initialize compute was not measured.

SBF build messages: 28 "Stack offset ... exceeded" messages, none in an `aspis_pool` function (all in `aspis_core::r0`
and two generic std instances; list in `rewrites3/runs/receipts-and-stack.txt`). The frozen build's log was not
kept, so the same list was not compared against a frozen build (a frozen-copy build was prepared and not run: the
host disk stood at 40 GiB free). Unchecked.

## Not done, and unchecked

- The comparison of the SBF stack-offset messages with a frozen build (above).
- Deposit, checkpoint and initialize compute.
- The handler state comparison covers the existing Pool tests' fixtures (22 accepted and 1,061 rejected calls); it is
  not an exhaustive input search. The settlement page modes are covered as far as those fixtures reach them.
- The read-before-write check is textual and conservative; its two flags were examined by reading, not by a tool.
- The argument that moving each mutable borrow from before the CPI to its write changes no outcome rests on the
  accounts being distinct (checked by `require_unique_accounts`) and on no CPI receiving these accounts; it is stated
  in `write-boundary.md`, not checked by a tool.
- Elaboration is against X3's native library build (Lean 4.36.0-rc2); nothing is proved about any emitted function.

## Rerun

1. Build the tree: copy `W/src-frz-a` and apply `rewrites3/*.patch` (each against the frozen file, `patch -p1`; not the
   `frozen-test-tree__` patch, which builds the frozen test copy instead). Copy `../host/fv_x2c_*` to `W/x2c/bin` and
   the configs to `W/x2c/config`, with X2's `fv_x2_run.py` and helpers as in X2b's README.
2. Emission and native compile: `bash W/x2c/bin/fv_x2c_job.sh <name> 3000 W/x2c/<out> bash W/x2c/bin/fv_x2c_emit.sh
   W/x2c/config/fv_x2c_cfg_c9.json W/x2c/<out> charon,aeneas,scan native`.
3. Emission checks: `fv_x2c_emission_checks.py <out>/runs/A-release/raw/AspisX2 account_write.write_account_data_v1
   solana_account_info.AccountInfo.try_borrow_data <pool src>,<statement src>,<core src> <pool src>/account_write.rs`.
4. Grammar check: `fv_x2c_write_boundary_check.py <pool src>/account_write.rs` (and `--only name,...` for a larger file).
5. Tests and state comparison: `fv_x2c_test.sh <tree> <target> <dump dir> ""` on both trees, then
   `fv_x2c_compare_dumps.py <frozen dump> <rewrite dump>`.
6. Compute: `fv_slot.sh <attempt> 3000 bash fv_x2c_compute.sh <build attempt> src-x2c-<n> <out>`.
