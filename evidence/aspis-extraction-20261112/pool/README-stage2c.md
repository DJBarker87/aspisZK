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

STEP2_RESULTS

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
the std iterator instances that list `map`/`all`/`any`/`sum` because reached code uses them. All are addressed in
the tree state of run c5 (below).

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

STEP5_RESULTS

STEP6_ONWARD
