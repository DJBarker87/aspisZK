# Aspis Pool program: account write boundary (task X2c)

Status: a tool record. Nothing here is proved. It lists the one function through which every account-data write of
the four deployed Pool handlers now passes, its exact text, its callers, and for each handler the writes in the
frozen order beside the boundary calls that now perform them.

Source: frozen commit 3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de; rewrite tree `W/x2c/rw-tree` (patches in
`rewrites3/`). Line numbers "rewrite" are those of the patched files (`rewrites3/pool__*.patch` applied to the frozen
files).

## Why a boundary

Charon and Aeneas cannot express a write through the SDK's `RefMut<&mut [u8]>` (X2b, 17 shapes): either the native
library rejects the emitted code, or the emitted Lean silently drops the write (the backward functions of the borrow
are discarded). The writes are therefore isolated in one function that is made opaque by name in the emission
(`--opaque crate::account_write::write_account_data_v1`). Everything that decides what is written (the account, the
range, the bytes) is translated code over plain values.

## The boundary function (one function, 9 lines; `programs/aspis-pool/src/account_write.rs`)

```rust
#[inline(always)]
pub(crate) fn write_account_data_v1(account: &AccountInfo<'_>, start: usize, end: usize, bytes: &[u8]) -> ProgramResult {
    let mut data = match account.try_borrow_mut_data() {
        Ok(data) => data,
        Err(err) => return Err(err),
    };
    data[start..end].copy_from_slice(bytes);
    Ok(())
}
```

Classification: an SDK/std operation (`AccountInfo::try_borrow_mut_data`, `<[u8]>::copy_from_slice`) at the call
sites listed below.

Contract on bytes: after `write_account_data_v1(account, start, end, bytes)` returns `Ok(())`, the account's data
equals its old data with `bytes` at `start..end`; every other field of the account and every other account are
unchanged. If the borrow fails, the borrow error is returned unchanged and nothing is changed. The caller guarantees
`start <= end`, `end - start == bytes.len()` and `end <= account.data_len()`; otherwise the index or the copy panics,
as the frozen write at the same place would have (each call site below states where the frozen code checked the
length).

There is no lamports boundary: the Pool never writes lamports directly. Every lamport movement of the four handlers
is a System or Token program invocation (`create_or_allocate_*`, `initialize_vault_account`, the token transfer
CPIs). The only `try_borrow_mut_lamports` sites in the crate are in test mocks (`pair_forest.rs` test module).

Grammar check: `../host/fv_x2c_write_boundary_check.py` (Python; a strict token matcher, no third-party parser,
program-independent). After one SDK borrow of one account's mutable handle, spelled `match ... { Ok(x) => x,
Err(err) => return Err(err) }`, it accepts exactly three forms of the single operation: L, `**G = AMOUNT;` (lamports,
parameter value); D, `G[START..END].copy_from_slice(SRC);` (data, all three operands parameters); Z, `G.fill(LITERAL);`
(the whole data, an integer literal); then `Ok(())`. Nothing else: no arithmetic, branch, loop, other call, read of
the contents, second account, string literal. `--only name,...` checks named functions inside a larger file (each
function's own text is cut out and checked; nothing else in the file is examined). Output
(`rewrites3/checker-negatives/output.txt`):

| File | Verdict |
|---|---|
| `positive-account_write.rs` (the module above) | pass, `write_account_data_v1` lines 18-26 (9 lines), form D |
| `positive-lamports.rs` (a lamports form, not used by the Pool) | pass, form L |
| `neg-branch.rs` (`if start > 0 { .. }` around the copy) | FAIL: expected a name, found `if` |
| `neg-arith.rs` (`data[start..start + bytes.len()]`) | FAIL: expected `]`, found `+` |
| `neg-read.rs` (`let first = data[0];` before the copy) | FAIL: expected a name, found `let` |
| `neg-second-account.rs` (a second `&AccountInfo` parameter) | FAIL: parameter list outside the grammar |
| `positive-zero.rs` (the verifier's `write_zero_data` text) | pass, form Z |
| `neg-fill-partial.rs` (`data[..8].fill(0)`) | FAIL: expected `.`, found `[` |
| `neg-fill-param.rs` (`data.fill(value)` with a parameter) | FAIL (parameter list read as the lamports form; the data borrow does not match it) |
| verifier program `programs/r1-cost-probe/src/r1_pool_adapter.rs` (worktree `aspis-next`, read only, sha256 7877ed3269556ce444da48109042af3b8afe0348574053593d9b82e8f87b6e0b), `--only write_zero_data,write_lamports` | pass: `write_zero_data` lines 1092-1097 (6 lines) form Z; `write_lamports` lines 1101-1106 (6 lines) form L |

Shared vocabulary with the verifier program: the Pool needs neither a whole-data zero fill nor a lamports write (no
direct lamports write; a fresh page receives only its header-and-roots prefix because it is checked entirely zero
first), so it has no `write_zero_data` or `write_lamports`; it needs only form D, `write_account_data_v1`. If a later
change needs either operation, the verifier's names and texts are to be used.

## Callers (all in `programs/aspis-pool/src/pair_forest.rs`, rewrite tree)

| Caller | Lines of the calls | Writes |
|---|---|---|
| `write_deposit_accounts_v1` (deposit stage 6) | 1288, 1307, 1316, 1325, 1339 | lane image; page (one of three modes) |
| `write_terminal_accounts_v1` (settlement) | 2363, 2377 | lane image; nullifier marker |
| `write_terminal_page_v1` (settlement page) | 2406, 2415, 2424, 2438 | page (one of three modes) |
| `write_initialize_accounts_v1` (initialize stage 6) | 3030, 3039, 3048, 3057, 3066, 3075, 3084, 3093, 3102 | master image; lanes 0 to 7 |
| `process_pair_forest_checkpoint_with_runtime_v1` | 3194, 3203 | checkpoint image; master image |

## Writes per handler: frozen order and boundary calls

Frozen lines are in the frozen `programs/aspis-pool/src/pair_forest.rs` and `history.rs`.

### Checkpoint (`AS8C`)

| # | Frozen (pair_forest.rs) | Boundary call (rewrite) | Account | Range | Bytes |
|---|---|---|---|---|---|
| - | 2183-2184 acquire master, then checkpoint borrows | (none; each borrow is taken at its write) | | | |
| 1 | 2185 `checkpoint_data.copy_from_slice(&planned.checkpoint_image)` | 3194 | accounts[9] checkpoint | 0..192 | planned checkpoint image |
| 2 | 2186 `master_data.copy_from_slice(&planned.next_master_image)` | 3203 | accounts[0] master | 0..384 | planned master image |

Lengths: checkpoint by `require_program_owned_zeroed` (exact 192), master by `decode_pool_v1_pair_forest_master_v1`
(exact 384) in the planner.

### Deposit (`AS8D`)

| # | Frozen | Boundary call (rewrite) | Account | Range | Bytes |
|---|---|---|---|---|---|
| - | 1168-1169 acquire lane, then page borrows (before the token CPI at 1170) | (none) | | | |
| 1 | 1173 `lane_data.copy_from_slice(next_lane_image)` | 1288 | accounts[1] lane | 0..768 | new lane image |
| 2a | 1175 genesis: `write_new_page_unchecked(page, lane, 0, 0, [old root, new root])` (history.rs 259-283: `fill(0)`, header, two roots) | 1307 | accounts[2] page | 0..128 | header (filled 2) and the two roots |
| 2b | 1183 same page: `append_roots_unchecked(page, header, [new root])` (history.rs 285-294: root, then filled) | 1316, then 1325 | accounts[2] page | 64+32·filled..+32, then 56..58 | root; filled+1 |
| 2c | 1187 rollover: `write_new_page_unchecked(page, lane, n, seq, [new root])` | 1339 | accounts[3] next page | 0..96 | header (filled 1) and the root |

### Settlement (`ASQ8`)

| # | Frozen | Boundary call (rewrite) | Account | Range | Bytes |
|---|---|---|---|---|---|
| - | 1780-1782 acquire lane, page, marker borrows (before the withdrawal CPI at 1792) | (none) | | | |
| 1 | 1796 `lane_data.copy_from_slice(next_lane_image)` | 2363 | accounts[2] lane | 0..768 | new lane image |
| 2a | 1798 genesis page | 2406 | accounts[3] | 0..128 | header (filled 2), old root, verified next root |
| 2b | 1805 same page append | 2415, then 2424 | accounts[3] | root slot, then 56..58 | verified next root; filled+1 |
| 2c | 1810 rollover | 2438 | accounts[next_index] (4) | 0..96 | header (filled 1), verified next root |
| 3 | 1818 `marker_data.copy_from_slice(&ready_marker.encoded_marker())` | 2377 | accounts[marker_index] | 0..208 | marker image |
| - | 1819 `set_return_data(result bytes)` | host `set_return_data` (not an account write) | | | |

### Initialize (`AS8I`)

| # | Frozen | Boundary call (rewrite) | Account | Range | Bytes |
|---|---|---|---|---|---|
| - | 2114-2118 acquire master, then lanes 0 to 7 (guards pushed into a `Vec`) | (none) | | | |
| 1 | 2119 `master_data.copy_from_slice(master_image)` | 3030 | accounts[0] | 0..384 | master image |
| 2-9 | 2120-2122 loop: `lane_data[lane].copy_from_slice(lane_images[lane])`, lanes 0 to 7 | 3039, 3048, 3057, 3066, 3075, 3084, 3093, 3102 | accounts[1..9] | 0..768 each | genesis lane images |

## What differs from the frozen code, and why the account states are the same

1. Borrow acquisition point. The frozen handlers took every mutable borrow before the first write (deposit and
   settlement: before the token CPI). Each boundary call now takes its own borrow at its write. A borrow fails only if
   another borrow of the same account's data is live. In all four handlers the written accounts are pairwise distinct
   (`require_unique_accounts` runs earlier in each), none is passed to the CPIs between the frozen acquisition and the
   write, and no other borrow is live at either point (every read borrow is scoped to its decoder). So no borrow can
   fail at either point, and the moved acquisition changes no outcome. The guards are no longer held across the CPI;
   the frozen guards could only have made that CPI fail if one of these accounts had been passed to it, which none is.
2. Fresh pages. The frozen `write_new_page_unchecked` zeroed the whole page, then wrote the header and roots. The
   boundary writes only the prefix (header and roots, 96 or 128 bytes). Every fresh page is checked entirely zero
   before (deposit: `require_program_owned_zeroed`; settlement: `account_is_zeroed_program_page` in the layout) and
   nothing writes it in between (CPIs cannot write Pool-owned data), so the page after the write is the same. This
   removes an 8,256-byte `fill(0)` per fresh page.
3. Two calls for a same-page append (root, then counter) instead of one function writing both: the same two byte
   ranges in the same order.
4. No translated code reads an account's data after writing it: the writes are the last account operations of each
   handler (settlement: followed only by `set_return_data`).

Rejection paths: the frozen handlers write account data only after their last check, so a frozen handler that
rejects has written no Pool account data itself. Accounts can still differ after a rejection when a CPI ran before
the rejecting check (in the settlement handler, the nullifier marker is created by a System CPI before the verifier
call; a later rejection leaves that creation in the instruction's view, and the runtime rolls the failed instruction
back). This is the same in both trees; see the state comparison in `README-stage2c.md` (test
`terminal_marker_creation_fails_closed_rolls_back_and_rejects_replay`, the one rejected call with changed accounts).

## Emission checks (run `X2c-pool-c9`, the final tree; `../host/fv_x2c_emission_checks.py`, output `rewrites3/emission-checks-c9.txt`)

(a) Single route. Source search over the Pool, `aspis_statement` and `aspis_core` (`try_borrow_mut_data`,
`try_borrow_mut_lamports`, `.data.borrow_mut()`, `.lamports.borrow_mut()`): outside `#[cfg(test)]` items, one site in
the boundary (`account_write.rs` line 20) and eight in the legacy `pair_processor.rs` (lines 383, 391, 399, 403, 543,
545, 547, 548, functions `process_pair_private_transfer_with_verifier_v1` and `process_pair_withdrawal_with_verifier_v1`,
reached only under the feature `pair-afterstate-evidence`, off in the deployed build); neither function has an emitted
definition. Emission: no name containing `borrow_mut` or `lamports_mut` in `Funs.lean` or in the external template;
the boundary is a bodiless `axiom account_write.write_account_data_v1` in the external template and has no definition
in `Funs.lean`. The two agree: no translated body reaches a mutable handle. Pass.

(b) Read before write (conservative, textual). Eleven emitted definitions write (directly or through calls). Two are
flagged, both examined:
- `processor.dispatch_pool_instruction_v1`: the four handler calls sit on mutually exclusive branches of the magic
  dispatch (`AS8I`, `AS8C`, `AS8D`, `ASQ8`); a later branch's handler textually follows an earlier branch's. No path
  runs two handlers.
- `pair_forest.process_pair_forest_terminal_v1`: the flagged "reading" name is the production host instance
  (`SolanaPairForestTerminalHostV1`) passed as an argument of the same handler call; there is no later call.
No handler definition reads account data after its first boundary call. (The checkpoint handler was flagged in
run c4 because Charon duplicated its tail after the creation branch; the creation branch is now a stage helper.)

(c) Write order in the emission (Funs.lean of c9) beside the frozen order:

| Handler | Emitted boundary calls, in text order (account; start; end) | Frozen writes |
|---|---|---|
| Checkpoint (`process_pair_forest_checkpoint_with_runtime_v1`) | line 28435: checkpoint; 0; CHECKPOINT_ACCOUNT_BYTES. line 28442: master; 0; MASTER_ACCOUNT_BYTES | 2185 checkpoint, 2186 master |
| Deposit (`write_deposit_accounts_v1`) | 18490: lane; 0; lane bytes. Then one branch: 18501 genesis page; 0; 128. Same page: 18506 page; root_start; root_end, then 18511 page; filled_start; filled_end. 18521 rollover page; 0; 96 | 1173 lane, then 1175 / 1183 / 1187 page |
| Settlement (`write_terminal_accounts_v1`, `write_terminal_page_v1`) | 25559: lane; 0; lane bytes. Then the page call (25521 genesis 0..128; 25527 then 25532 same page; 25542 rollover 0..96). 25572: marker; 0; MARKER_ACCOUNT_BYTES | 1796 lane, 1798 / 1805 / 1810 page, 1818 marker |
| Initialize (`write_initialize_accounts_v1`) | 27130: master; 0; MASTER_ACCOUNT_BYTES. 27143, 27152, 27161, 27170, 27179, 27188, 27198, 27208: lanes 0 to 7; 0; lane bytes | 2119 master, 2120-2122 lanes 0 to 7 |

