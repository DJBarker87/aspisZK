# Aspis Pool program: four follow-ups to X2c (task X2d)

Status: a tool record. Nothing here is a proof. A translated, elaborated function is not a verified function, a
passing check is not a proof of the property it checks, and nothing below is described as proved or established.

Base: candidate commit d78cbfaa4037634d91013f884ac89d2e6a718d4a (branch `aspis-next`, read only). Host tree
`W/src-x2d-1` made from it with the lead's `fv_frz_tree.sh` (archive sha256
478770ba3f3400cd58fdb48a12adacf539c2c96775c395d7bf5b0fde3ad894d7, files sha256
d51cbdbc78fe4929bce8fd65a8280f6d460743ce01dc8c8ff9c5dd48b31fbbb1, 1,874 files); work tree `W/x2d/rw-tree` (a copy,
edited); build tree for the item 1 Pool `W/src-x2d-2` (a copy of the edited work tree). `W` =
`~/project-offloads/future-version-20261111` on the build host. Nothing was applied to a repository worktree. Every
heavy command ran in one `fv_slot.sh` scope at a time (MemoryHigh 6G, MemoryMax 8G, no swap), attempt names `X2d-*`.

## Files

| File | Content |
|---|---|
| `patches/pool__pair_forest.patch` | item 1: the only changed source file, `diff -u` against the file at d78cbfaa403 |
| `read-after-write/` | item 2: the planted cases (`planted/positive`, `planted/negative`) and the outputs of the new check on them, on X2c's c9 emission, on planted reads in copies of that emission, on the verifier's `close_checkpoint` (X1b run G), and on this task's emission |
| `runs/` | item 1 and 4 run records: test log excerpt, state comparison, emission steps and native compile, X2c's emission checks, grammar checker, compute summaries and the replay tool's JSON files |
| `../../host/fv_emit_read_after_write.py` | item 2: the check |
| `../../host/fv_x2d_*` | this task's scripts, the emission config, the raw-emission mutation script and the replay tool's source `fv_x2d_pool_replay.rs` (item 4) |
## Item 1: the boundary's range precondition as a check in the caller

The boundary `account_write::write_account_data_v1` is unchanged (text and line count; the grammar checker's verdict
is below). Its precondition (`start <= end`, `end - start == bytes.len()`, `end <= data_len`) is now checked in the
pure callers, for every write of a handler, before that handler's first write, on data lengths read before that
write (`AccountInfo::data_len`, after the handler's last CPI and before its first boundary call). One plain-value
function states it:

```rust
#[inline(always)]
fn write_range_fits_v1(data_len: usize, start: usize, end: usize, bytes_len: usize) -> bool {
    start <= end && end - start == bytes_len && end <= data_len
}
```

(the subtraction runs only when `start <= end`). `bytes_len` is the `.len()` of the very array that is passed to
the boundary. For the root-history page of the deposit and the settlement, the bytes are now decided before the
handler's first write, in a value `RootPageWriteV1` (two-root prefix, one-root prefix, or same-page append), checked
by `root_page_write_fits_v1` and written by `write_root_page_v1`, which makes the same boundary calls with the same
arguments in the same order as the former page branches. Moving these pure computations before the lane write is
not observable: they read no account and write nothing. Only `programs/aspis-pool/src/pair_forest.rs` changes (295
lines added, 77 removed, all in the Pool crate; the statement and core crates are untouched).

The error at each site is the one the frozen handler returns for a malformed (wrong-length) account of the same
role, where the frozen code checks that length; `ProgramError::AccountDataTooSmall` was not needed at any site.

| Handler, write (frozen order) | Account | Range checked | Error if it does not fit | Why no input the frozen program accepts reaches it |
|---|---|---|---|---|
| Initialize, master | `accounts[0]` | `0..384`, 384 bytes | `InvalidFreshAccount` (0x41532035) | `require_initialize_accounts_zeroed_v1` has just required data length exactly 384 (`require_program_owned_zeroed`, same error); no CPI follows |
| Initialize, lanes 0 to 7 | `accounts[1..9]` | `0..768`, 768 bytes each | `InvalidFreshAccount` | the same function has required exactly 768 for each lane |
| Checkpoint, checkpoint image | `accounts[9]` | `0..192`, 192 bytes | `InvalidFreshAccount` | `require_program_owned_zeroed(checkpoint, .., 192, ..)` just before (after the creation CPI) |
| Checkpoint, master image | `accounts[0]` | `0..384`, 384 bytes | `InvalidAccountType` (0x41532001) | `decode_master_account` in the planner required exactly 384 (decoder `WrongLength` mapped to `InvalidAccountType`); the master is not passed to the creation CPI, which cannot resize a Pool-owned account anyway |
| Deposit, lane image | `accounts[1]` | `0..768`, 768 bytes | `InvalidAccountType` | the lane decoder (`decode_lane_account`, decoder `WrongLength` to `InvalidAccountType`) required exactly 768; the page creation and token CPIs do not receive the lane |
| Deposit, fresh page (genesis, rollover) | `accounts[2]` or `accounts[3]` | `0..128` (two roots) or `0..96` (one root) | `InvalidFreshAccount` | `require_program_owned_zeroed(page, .., 8256, ..)` after the creation CPI required exactly 8,256 |
| Deposit, same page (root, then counter) | `accounts[2]` | `64+32·filled .. +32`, then `56..58` | `InvalidAccountType` | `validate_root_page_bytes` required exactly 8,256 (`InvalidAccountType` otherwise) and `filled == slot + 1` with the next root on the same page, so `filled <= 255` and the root ends at most at 64 + 32·256 = 8,256 |
| Settlement, lane image | `accounts[2]` | `0..768` | `InvalidAccountType` | `decode_lane_bytes_from_program_invariant_v1` (deployed feature `pair-forest-source-invariant-audit`) required exactly 768 |
| Settlement, genesis page | `accounts[3]` | `0..128` | `InvalidAccountType` | the genesis mode is chosen only if `account_is_zeroed_program_page` holds, which requires exactly 8,256; a page of another length goes to `validate_lane_current_page`, whose error for it is `InvalidAccountType` |
| Settlement, same page | `accounts[3]` | as for the deposit | `InvalidAccountType` | as for the deposit (`validate_lane_current_page`) |
| Settlement, rollover page | `accounts[4]` | `0..96` | `InvalidFreshAccount` | `plan_pair_forest_spend_layout_v1` requires `account_is_zeroed_program_page(next)` (exactly 8,256), `InvalidFreshAccount` otherwise |
| Settlement, nullifier marker | `accounts[marker_index]` | `0..208` | `InvalidNullifierMarkerAccount` (0x41532025) | `create_pair_forest_nullifier_marker_if_needed_v1` re-classifies the marker after its creation and requires exactly 208 (`classify_nullifier_marker_account_v1`) |

In every row the length the check reads is the length the frozen code required, and every account in the table is
owned by the Pool when its length is checked. Between that check and the new one the handler only makes CPIs (System
creation of other accounts, the token transfers, and in the settlement the read-only verifier call, which receives
the master, checkpoint and lane accounts). A CPI callee cannot change the data length of an account it does not own,
the System program resizes only system-owned accounts, and the Pool itself performs no realloc. So on every input the
frozen program accepts, every check passes, the same writes follow, and the outcome is unchanged.

For the record: the class that changes is the inputs on which the frozen code panicked inside a write (a range
outside the data, or of the wrong length). There the outcome changes from an abort (the instruction fails with a
panic, nothing persists) to an error return with the named error before any write (the instruction also fails,
nothing persists). The table above argues that no such input reaches a write in the frozen handlers; the change
concerns the code's form (the check is now a translated comparison instead of a precondition carried by the trust
row), not any recorded outcome. The boundary's contract no longer needs the caller's range obligation as an
assumption at these call sites; the contract text in `account_write.rs` (a doc comment) is unchanged.

Added work: at most one `data_len()` per written account and three comparisons and one subtraction per boundary call,
done once per handler (initialize: nine lengths, 27 comparisons; checkpoint: two; deposit: two; settlement: three),
plus building the page bytes into one value before the first write instead of after it. Measured in item 4.

### Item 1: checks run on the item 1 tree

- Pool tests (`../../host/fv_x2d_test.sh`: `cargo test --release --offline --locked`, deployed feature list
  `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`, toolchain
  nightly-2026-09-17 as X2c): run `X2d-test-2`, 88 passed, 0 failed (X2c's 85 and three new tests in
  `pair_forest::x2d_write_range`: the range check equals the condition under which `data[start..end]
  .copy_from_slice(bytes)` does not panic, over all 10,000 combinations of four values below 10 and two extremes;
  the page writes fit exactly up to the last slot and not beyond; the initialize stage writes all nine accounts when
  their lengths are exact and, with any one account one byte short, returns `InvalidFreshAccount` with every account
  unchanged, where the code without the check would have written the accounts before it and then panicked). The
  first run, `X2d-test-1`, failed to compile (`vec!` is not in scope in this `no_std` crate's test module); the tests
  were changed to `alloc::vec!` and rerun. The statement and core crates are unchanged and were not rerun. Excerpt
  and run receipts: `runs/test-and-receipts.txt`.
- Handler state comparison (X2c's recorder and `fv_x2c_compare_dumps.py`, unchanged): the dumps of the item 1 tree
  (`X2d-test-2`) against X2c's dumps of the frozen tree (`W/x2c/dump-frz-c5`, read only; the frozen tree and its
  recorder are unchanged since that run): 12 tests, 1,083 handler calls (22 accepted, 1,061 rejected), every record
  byte-identical (result, and each account's key, owner, lamports and complete data before and after), exit codes
  identical (`runs/compare-2.txt`). No recorded call takes a new error: every rejected call has the same error value
  as in the frozen tree. The new tests are outside `pair_forest::tests`, so the recorded test list is X2c's.
- Emission (`../../host/fv_x2d_emit.sh` with X2c's runner and native compile copied unchanged to `W/x2d/emitbin`;
  config `../../host/fv_x2d_cfg_1.json`, X2c's c9 configuration with only the source and target paths changed: single
  root `crate::processor::process_instruction`, deployed features, overflow checks off, opaque only the boundary,
  `solana_rent::Rent` and `runtime_stack_height_v1`): run `X2d-pool-2`. Charon exit 0 (99.1 s, LLBC sha256
  2238688b5dc0669bed76081cac65335eceb4c8b060dddc2fd7930c48790f6078, 975 function declarations, no errors); Aeneas
  `-abort-on-error` exit 0 (272.7 s, 0 functions with errors); scans and erased-region scans exit 0; reversed mutable
  iterator sites `crates/aspis-core/src/r0_transcript.rs:129` only (not emitted, as in X2c). Scope: wall 7:37.33,
  peak RSS 2,151,052 kB, cgroup peak 2,474,823,680 B, no MemoryHigh events. Raw output sha256: `Funs.lean`
  6504610852b86a06f549ac542fd65b438109a1a65294f1220d6faef14e332bd7, `Types.lean`
  e6acdb393f1da8540629560a15507944f06340417167a146369347fc5a59eca5, `FunsExternal_Template.lean`
  bd5f7c40ee27b0c3a391972e530cf47de1b1f4bd771c96066a9e31d035666edb and `TypesExternal_Template.lean`
  cc468c968a4196ad6cb03695ca11e41ef5bdef38d3229bf83263ad2badba4e8c (both templates byte-identical to X2c's c9).
- Native compile of the raw output with zero edits against X3's Lean 4.36.0-rc2 library: `TypesExternal` 0, `Types`
  0, `FunsExternal` 0, `Funs` 0 errors (`runs/pool-2/native/`). No `sorry` in `Funs.lean`. Bodiless Aspis
  declarations: `account_write.write_account_data_v1` and `processor.runtime_stack_height_v1` only, as in X2c.
- X2c's emission checks (`runs/emission-checks-2.txt`): (a) single route passes (the boundary is the only non-test
  source site that borrows mutably apart from the unreached legacy `pair_processor.rs` functions; no mutable-handle
  name in the emission); (c) the boundary calls in emission order: initialize master then lanes 0 to 7; checkpoint
  image then master; deposit lane then the page (Aeneas emitted the deposit write stage's tail once per page mode,
  because the page bytes are now bound by a three-way match: each of the three paths makes the lane write and then
  calls `write_root_page_v1`); settlement lane, then `write_root_page_v1`, then the marker; `write_root_page_v1`
  holds the four page calls of the former branches. This is the frozen order of every handler. (b) raises X2c's two
  textual flags again (see item 2).
- Read-after-write (item 2's check on this emission): pass for the four handlers and the entry.
- Grammar checker (`fv_x2c_write_boundary_check.py`, unchanged) on `account_write.rs` of the item 1 tree: pass,
  `write_account_data_v1` lines 18-26 (9 lines), form D (`runs/grammar-2.txt`); the file is byte-identical to the one
  at d78cbfaa403.

## Item 2: read-after-write as a mechanical check

`../../host/fv_emit_read_after_write.py` replaces the reading of X2c's two textual flags. It works on the emitted
Lean and names nothing of the Pool: the write boundaries, the read externals and the roots are arguments.

Method (full text in the script's header). Every `def` of the emission is parsed into statements by indentation: a
`match ... with` with its `|` arms, an `if` whose `then` and `else` begin lines, or an atomic statement. A walk of each
body carries the set of possible states {nothing written, written}: through sequencing; into every arm of a match
and both branches of an if from the state before it, joining the arms' end states; and through calls, by a summary
of each definition (may read, may write, may read after a write) computed to a fixed point over all definitions,
recursion included. A call of D in a possibly written state is a read after write if D may read; a statement that
contains the `loop` combinator is applied twice (a later iteration may read what an earlier one wrote). A call
through a trait parameter (`p.m` with `(p : T ...)` in the header) resolves to the method `m` of every emitted
instance of `T` (definitions named `<type>.Insts.<...>` whose body is a record). An instance named as an argument of
an emitted definition is covered by that definition's own summary; named in a statement with no emitted call, it
counts as a possible call of all its methods. Inside one atomic statement events are taken in text order unless the
statement contains a nested action `(← ...)`; then a statement where one event may write and another may read
counts as a read after write. Read externals given for the Pool: `AccountInfo.try_borrow_data`, `data_len`,
`data_is_empty`, `impl.lamports` (every read of an account's data or lamports in the emission's external template);
write boundary: `account_write.write_account_data_v1`.

Planted cases (`read-after-write/planted/`, emitted-style Lean, not compiled; output `planted-output.txt`):

| Case | Shape | New check | X2c's textual check |
|---|---|---|---|
| P1 | write, read in the `Ok` arm | read after write reported | flagged |
| P2 | write, then a call of a reading definition | reported | flagged |
| P3 | write on one `if` branch, read after the join | reported | flagged |
| P4 | loop body reads then writes, run by `loop` | reported | not flagged (missed) |
| P5 | write, then a trait method whose only instance reads | reported | not flagged (missed) |
| P6 | write in one match arm, read after the match | reported | flagged |
| N1 | dispatch: a writing handler on one branch, a handler that reads then writes on a later exclusive branch (the shape of `processor.dispatch_pool_instruction_v1`) | pass | flagged (wrongly) |
| N2 | an instance whose method reads, passed to a generic handler that calls it and then writes (the shape of `pair_forest.process_pair_forest_terminal_v1`) | pass | flagged (wrongly) |
| N3 | two match arms, each reading before its own write | pass | flagged (wrongly) |

Real emissions (all files under `read-after-write/`):

- X2c's c9 emission (`c9-output.txt`): the four handlers and `processor.process_instruction` pass. Reached
  definitions: initialize 302, checkpoint 291, deposit 362, settlement 524, entry 670; definitions that may write:
  2, 1, 2, 4, 11; that may read after a write: 0 everywhere.
- Planted reads in copies of that emission (`mutants-c9.txt`, `../../host/fv_x2d_raw_mutants.py`): a read after the
  settlement page write, after the initialize handler call inside its dispatch branch, after the checkpoint image
  write, after the deposit lane write. Each is reported, at the root whose path contains it and at the entry; the
  roots whose paths do not contain it still pass.
- This task's emission (run `X2d-pool-2`, item 1 applied; `x2d-emission-output.txt`): the four handlers and the
  entry pass. The added `data_len` reads appear as reads before any write. Planted reads in copies of it
  (`mutants-x2d-emission.txt`, after the settlement lane write, inside `write_root_page_v1` between its two append
  writes, after the checkpoint write, after the initialize master write) are each reported.
- The verifier program, `r1_pool_adapter.close_checkpoint` in X1b's run G emission (`W/x1b/probe/G`, read only;
  boundaries `write_zero_data`, `write_lamports`; reads `try_borrow_data`, `try_lamports`; output
  `verifier-close-checkpoint-x1bG.txt`): pass, reads before any write only.

X2c's textual check, rerun on this task's emission (`runs/emission-checks-2.txt`), still raises its two flags on
`processor.dispatch_pool_instruction_v1` and `pair_forest.process_pair_forest_terminal_v1`; they are the shapes of
N1 and N2, and the new check passes both definitions. Its sections (a) and (c) pass and are reported under item 1.

Limits of the check. It reads text, not the elaborated terms: a construct the parser does not recognise is treated
as an atomic statement (conservative only when the nested-action rule applies). Calls through function values other
than trait instances (closures passed to library functions) count at the place where they are written. Library
functions without an emitted body are taken to have no account effect; only the given read externals and write
boundaries do. It checks reads after writes, not the order or ranges of writes (X2c's check (c) and item 1).

## Item 3: two items for the trust list

Line numbers are those of commit d78cbfaa403. Item 1 changes only `pair_forest.rs`; `processor.rs` is unchanged, and
the `pair_forest.rs` lines named below that lie after the first item 1 edit (line 1281) move down in the item 1 tree.

### (a) `processor::runtime_stack_height_v1`

Exact text (`programs/aspis-pool/src/processor.rs` lines 785 to 795):

```rust
#[inline(always)]
fn runtime_stack_height_v1() -> usize {
    #[cfg(target_os = "solana")]
    {
        get_stack_height()
    }
    #[cfg(not(target_os = "solana"))]
    {
        TRANSACTION_LEVEL_STACK_HEIGHT
    }
}
```

`get_stack_height` is `solana_program::instruction::get_stack_height` (import at line 14) and
`TRANSACTION_LEVEL_STACK_HEIGHT` is `solana_program::instruction::TRANSACTION_LEVEL_STACK_HEIGHT` (line 15), defined
in `solana-instruction` 2.3.3 `src/lib.rs` line 290 as `pub const TRANSACTION_LEVEL_STACK_HEIGHT: usize = 1;`.

- Solana build: `solana_program::instruction::get_stack_height()` (`solana-program` 2.3.0 `src/instruction.rs` 36-46)
  calls `solana_instruction::syscalls::get_stack_height()` (`solana-instruction` 2.3.3 `src/syscalls.rs` 76-80),
  which is the syscall `sol_get_stack_height()` (declared in `solana-define-syscall` `definitions.rs`, `fn
  sol_get_stack_height() -> u64`), cast to `usize`. The runtime returns the invocation depth of the running
  instruction: 1 for an instruction of the transaction, 2 for an instruction invoked by it, and so on.
- Host build (the build the translator reads): the constant `TRANSACTION_LEVEL_STACK_HEIGHT`, which is 1. The
  function is opaque by name in the emission (`axiom processor.runtime_stack_height_v1 : Result Std.Usize`), so the
  emitted Lean has neither value: the axiom stands for the call.
- The check it feeds: `processor.rs` line 636, the first check of `process_instruction` after `set_return_data(&[])`:
  `require_transaction_level_invocation_v1(runtime_stack_height_v1())?;`. That function (lines 797 to 803) compares
  `stack_height != TRANSACTION_LEVEL_STACK_HEIGHT` and returns
  `Err(PoolV1ProgramError::CpiInvocationForbidden.into())`, that is `ProgramError::Custom(0x4153_2036)`; otherwise
  `Ok(())`. In the emission the comparison is translated code (`processor.require_transaction_level_invocation_v1`),
  and the constant is the bodiless `solana_instruction.TRANSACTION_LEVEL_STACK_HEIGHT : Result Std.Usize`.
- What makes the host value stand for the deployed one: the Pool instruction runs at transaction level, i.e. it is
  an instruction of the transaction itself and not invoked through a cross-program invocation. Under that
  assumption the syscall returns 1, which is the host value, and the check passes in both builds. Without it (stack
  height 2 or more) the deployed program returns `CpiInvocationForbidden` before any other check while a model that
  takes the host value would go on: the host value enlarges the set of accepted inputs, so a statement of the form
  "accepted implies P" proved with the host value carries over to the deployed program, and a statement that the
  program rejects some input does not. The trust row has to state the syscall's contract (it returns the
  invocation depth; 1 at transaction level) and the value of `TRANSACTION_LEVEL_STACK_HEIGHT` (1).

### (b) `solana_rent::Rent`, opaque by the Charon flag

In the emission `Rent` is a bodiless type (`axiom solana_rent.Rent : Type`) with three bodiless functions:
`solana_rent.Rent.Insts.Solana_sysvarSysvar.get : Result (core.result.Result solana_rent.Rent ProgramError)`,
`solana_rent.Rent.minimum_balance : solana_rent.Rent → Std.Usize → Result Std.U64` and
`solana_rent.Rent.is_exempt : solana_rent.Rent → Std.U64 → Std.Usize → Result Bool`. Every use reachable from
`process_instruction` (the reachability is that of `fv_emit_read_after_write.py`'s call graph over the c9 emission,
the same functions in d78cbfaa403):

| # | Site (d78cbfaa403) | Method | Handlers whose path reaches it | On an accepting path |
|---|---|---|---|---|
| 1 | `processor.rs` 668, 682, 696, 711 (`dispatch_pool_instruction_v1`) | `Rent::get()` (sysvar), passed to the handler as `rent` | initialize (668), checkpoint (682), deposit (696), settlement (711, after `Clock::get`) | yes, every call of these handlers |
| 2 | `processor.rs` 319 (`create_or_allocate_pda`) | `Rent::get()` again, passed on as `rent` | initialize (master `pair_forest.rs` 2875, lanes 2947, vault `processor.rs` 547), checkpoint (`pair_forest.rs` 3135), deposit (genesis 1443, rollover 1481) | yes, whenever that account is created (system-owned and empty); the recorded initialize, both recorded deposits and the recorded checkpoint take it |
| 3 | `processor.rs` 346 (`create_or_allocate_pda_with_rent`) | `minimum_balance(exact_bytes)`, then `.max(1)` | as row 2 | as row 2 |
| 4 | `processor.rs` 412 (`create_or_allocate_with_seed_with_rent`) | `minimum_balance(208)`, then `.max(1)` | settlement (nullifier marker, from `processor.rs` 596, `create_pair_forest_nullifier_marker_if_needed_v1`, called at `pair_forest.rs` 2271) | yes, whenever the marker is system-owned and empty (both recorded payments) |
| 5 | `pair_forest.rs` 421 (`require_program_owned_zeroed`) | `is_exempt(account.lamports(), exact_bytes)` | initialize (master and the eight lanes, 2966-3014), checkpoint (3182), deposit (fresh page: 1453 genesis, 1491 rollover) | yes, on every accepting initialize and checkpoint and on every accepting deposit that writes a fresh page |
| 6 | `processor.rs` 611 (`create_pair_forest_nullifier_marker_if_needed_v1`) | `is_exempt(marker.lamports(), 208)` | settlement | yes, on every accepting settlement |

`Rent::get()` at `processor.rs` 727 (route `ASF8`) is compiled out at the deployed features. The test-only uses
(`Rent::default()` in the test modules, `nullifier.rs` 600 in a test) are not reached.

Lengths. `minimum_balance` is called with exactly these lengths: 384 (master), 768 (lane), 165 (vault token
account), 192 (checkpoint), 8,256 (root-history page), 208 (nullifier marker). `is_exempt` is called with 384, 768,
192, 8,256 and 208. So the only reachable uses are not `minimum_balance` alone: `Rent::get` and `is_exempt` are
reached too.

The value the deployed runtime supplies: `Rent::get()` on Solana is the syscall `sol_get_rent_sysvar`
(`solana-sysvar` 2.3.0 `src/lib.rs` 195-213, `impl Sysvar for Rent` at `src/rent.rs` 133-135), which copies the
cluster's Rent sysvar (`lamports_per_byte_year`, `exemption_threshold`, `burn_percent`); off chain the stub returns
`UNSUPPORTED_SYSVAR` (an error). `minimum_balance(n)` is `(((128 + n) * lamports_per_byte_year) as f64 *
exemption_threshold) as u64` and `is_exempt(b, n)` is `b >= minimum_balance(n)` (`solana-rent` 2.2.1 `src/lib.rs`
93-102). On devnet at the PIN2 run, every account the recorded transactions created holds (128 + n) × 5,080
lamports, the amount the Pool passed to `create_account` (`minimum_balance(n).max(1)`): 384 → 2,600,960; 768 →
4,551,680; 165 → 1,488,440; 8,256 → 42,590,720; 192 → 1,625,600; 208 → 1,706,880 (recorded post-states of
`pool-initialize`, `deposit-0`, `forest-checkpoint`, `transfer-stage2` in `PIN2_TRANSACTIONS.json`). The replays
use `lamports_per_byte_year` 2,540 and `exemption_threshold` 2.0, which give the same figures.

What the emission needs to know about the results: that `Rent.Insts.Solana_sysvarSysvar.get` either returns
`Ok r` for the cluster's sysvar value `r` or an error that the dispatch returns unchanged (its `?`); that, for that
`r` and for each of the six lengths above, `minimum_balance r n` returns `ok m(n)` (it does not fail) where `m(n)` is
the cluster's figure; and that `is_exempt r b n` returns `ok (b >= m(n))` for the five lengths it is called with. The
two `Rent::get` calls of one instruction (rows 1 and 2) read the same sysvar and give the same value. The exact
numbers matter for state only through the lamports given to created accounts (rows 3 and 4) and through the rent
checks (rows 5 and 6), which a precreated account with fewer lamports fails with `InvalidFreshAccount` or
`InvalidNullifierMarkerAccount`.

## Item 4: compute of the four handlers

Tools. The lead's replay tools do not cover initialize, deposit or checkpoint: `one_tx_replay` replays only the two
recorded settlements (stage 2 of each payment). This task adds one binary, `x2d_pool_replay`
(`../../host/fv_x2d_pool_replay.rs`, sha256 7633894c7507ab0fda1273171186556d6d2a6bde2fd368536facc517bb3d160a),
placed in a copy of the d78cbfaa403 tree (`W/x2d/tool-tree`, `tools/r1-cost-probe/src/bin/`, a new file; no existing
tool source changed) and built with the tool recipe of the lead's scripts (`cargo +1.94.1 build --release --offline
--locked`, attempt `X2d-tool-1`, binary sha256 2965cf79d1c4e1a92bccaca22d803a89aa889b8094810e25f663b4a71a7519e6). It
follows `one_tx_replay`: LiteSVM 0.16.0, signature verification off, the recorded Clock slot, devnet's rent (2,540
lamports per byte-year, threshold 2.0), the recorded pre-state, the recorded instruction after a
compute-unit-limit instruction of 1,400,000. For each recorded transaction it runs a control (the deployed devnet
Pool, `W/devnet/pool.so`) and then each Pool ELF; it compares the control's final state with the recorded
post-state (payer lamports excepted) and every other ELF's final state with the control's (every account).
Settlements: the lead's `one_tx_replay`, unchanged, as in X2c's `fv_x2c_compute.sh` (frozen one-transaction verifier
`W/out/frz-a-meas`, deployed verifier for its two-transaction control). Script `../../host/fv_x2d_compute.sh`; runs
`X2d-compute-1` (frozen and d78cbfaa403 Pools) and `X2d-compute-x2d-2` (item 1 Pool); records in `runs/compute-1/`
and `runs/compute-x2d-2/`.

Pool ELFs: frozen `W/out/PL-frz-a/artifacts/aspis_pool.so` (commit 3d700effcabe, sha256
0553a8bd5ef5c5ff93023b1923f96f9651a23f5aa4e50855baebe29109799cec); d78cbfaa403 built here with the lead's
`fv_pool_build.sh` recipe (`../../host/fv_x2d_pool_build.sh`, attempt `X2d-build-d78`, tree `W/src-x2d-1`, sha256
009bffb5d317765067c58cce55293b1401e8017b29a6d6fc75f766397a4747d1, 318,848 bytes); item 1 (attempt `X2d-build-x2d-2`,
tree `W/src-x2d-2`, sha256 6302e3550929733736a07d035084438eb5dbf3397d856bb3a20613a938f7a83a, 321,240 bytes). The
two builds share one target directory, so the second recompiled the Pool crate only. Both builds print the same 28
SBF stack-offset messages (identical lists, none in an `aspis_pool` function; `runs/test-and-receipts.txt`).

Pool compute units (the Pool program's "consumed" figure, which includes its CPIs; settlement rows: the
one-transaction run's transaction compute, the figure X2c reported, and in brackets the Pool's own figure in that
run, which includes the verifier CPI):

| Handler (recorded transaction) | Frozen Pool | d78cbfaa403 | After item 1 | Item 1 delta |
|---|---|---|---|---|
| Initialize (`pool-initialize`: creates master, eight lanes, vault) | 103,898 | 104,865 | 104,946 | +81 |
| Deposit (`deposit-0`: genesis page created) | 1,070,123 | 933,197 | 933,284 | +87 |
| Deposit (`deposit-1`: genesis page created, other lane) | 1,067,118 | 930,192 | 930,279 | +87 |
| Checkpoint (`forest-checkpoint`: checkpoint created) | 1,152,932 | 1,003,043 | 1,003,063 | +20 |
| Settlement, transfer (one transaction) | 1,232,920 (1,232,564) | 1,231,515 (1,231,159) | 1,231,676 (1,231,320) | +161 |
| Settlement, withdrawal (one transaction) | 1,239,440 (1,239,084) | 1,239,577 (1,239,221) | 1,239,730 (1,239,374) | +153 |

Checks in the same runs: every ELF completes every transaction; for every ELF and transaction the final state of
every account equals the control's (initialize, deposits, checkpoint), and for the settlements `one_tx_replay`
reports the one-transaction final state equal to its control's, the rejected runs (changed certificate, pinned-format
buffer) leaving state unchanged except the payer fee, and both prefunded-marker variants ending in the control's
state. The verifier compute is unchanged (1,184,299 transfer, 1,181,418 withdrawal). The d78cbfaa403 settlement
figures equal X2c's (1,231,515 and 1,239,577). The heaviest measured case after item 1 is the withdrawal at 1,239,730,
below the freeze's 1,262,410; item 1 adds at most 161 units (0.013 percent of a settlement), under the round limits
of ASPIS-PIN-RULES section 4.

Replay calibration. The control reproduces the recorded Pool compute exactly for the checkpoint (1,153,871); for
initialize and the deposits the
control is 50 and 56 units below the recorded figure (136,268 against 136,318; 1,111,359 against 1,111,415;
1,108,354 against 1,108,410), with final states equal to the recorded ones. The three transactions that differ are
the three with an SPL Token CPI; in the initialize the Token program itself consumed 239 in LiteSVM against 233 on
devnet, so LiteSVM's bundled Token program is not byte-identical to devnet's and its CPI path costs slightly
differently. The cause of the remaining units was not isolated. All four Pools run against the same LiteSVM programs,
so the columns compare with each other; the absolute deposit and initialize figures are LiteSVM's, not devnet's.
The `x2d_pool_replay` invocations therefore exit non-zero (its control check is strict). `one_tx_replay` exits
non-zero for every Pool other than the deployed one, because its two-transaction control then differs from the
recorded compute (as in X2c); its final-state checks pass. The figures are read from the JSON files.

Not covered by the recorded set: a deposit to an existing page (same page) and a deposit or settlement that rolls
over to a new page; a precreated (program-owned, zeroed) master, lane, page or checkpoint. Their compute was not
measured. The d78cbfaa403 savings on deposit (about 137,000) and checkpoint (about 150,000) against the frozen Pool
come from the rounds merged before d78cbfaa403 (X2c's untraced Poseidon2 paths and the other rewrites); no
per-function attribution was measured.

## Not done, and unchecked

- The item 1 argument that no accepted input reaches the new errors rests on the per-site reasons in the table
  (the length checks the frozen code makes before each write, and that no CPI between that check and the write can
  change a Pool-owned account's length); it is not checked by a tool. The state comparison covers the existing
  tests' 1,083 handler calls, not an input search.
- Compute was measured for the six recorded Pool transactions only; same-page and rollover deposits, rollover
  settlements and precreated accounts were not replayed (item 4). The LiteSVM replays of initialize and the deposits
  differ from devnet by 50 to 56 units in the control, cause not isolated.
- The read-after-write check reads the emitted text; its limits are listed under item 2. It was not run on an
  emission of the verifier program from d78cbfaa403 (only on X1b's run G).
- The statement and core crates' tests were not rerun (unchanged). The verifier program and the prover were not
  built or tested.
- Nothing about any emitted function is proved; elaboration against the native library is not verification.

## Rerun

1. Trees: `git archive d78cbfaa403 crates programs tools Cargo.toml Cargo.lock | ssh host bash W/fv_frz_tree.sh
   src-x2d-1 d78cbfaa403`; copy it to `W/x2d/rw-tree` and apply `patches/pool__pair_forest.patch` (`patch -p1`; checked:
   the result equals the work tree file, sha256 5194da7dfc9f3206c7c11b93a420cc5023d717b676296f03756febae7efb5813).
   Copy `../../host/fv_x2d_*`, `fv_emit_read_after_write.py` and X2c's `fv_x2c_compare_dumps.py`,
   `fv_x2c_emission_checks.py`, `fv_x2c_write_boundary_check.py` to `W/x2d/bin`; copy `W/x2c/bin` to `W/x2d/emitbin`.
2. `fv_x2d_chain1.sh` (d78cbfaa403 build; replay tool build, with `fv_x2d_pool_replay.rs` placed as
   `W/x2d/tool-tree/tools/r1-cost-probe/src/bin/x2d_pool_replay.rs` in a copy of `src-x2d-1`), then
   `fv_slot.sh X2d-compute-<n> 900 bash fv_x2d_compute.sh <out> frozen=<frozen pool>,d78=<d78 pool>`.
3. `fv_x2d_chain2.sh <suffix>`: tests and dumps, comparison, emission and native compile, the checks, the item 1
   build, its compute.
