# Aspis Pool program: stage 2 rewrites continued (task X2b)

Status: a tool record. It says which rewrites of the frozen Pool program make the Charon and Aeneas tools translate
more of it, and whether the raw Aeneas output then compiles against the native Aeneas Lean library. Nothing here is a
proof. A translated, elaborated function is not a verified function, and nothing below is described as proved or
established.

Source: frozen commit 3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de. Work tree: `W/x2b/rw-tree`, a copy of X2's scratch tree
`W/x2/rw-tree` (frozen tree plus X2's classes a and b); `W` = `~/project-offloads/future-version-20261111` on the build
host. Nothing was applied to the repository worktree, to `W/src-frz-a` or to `W/x2`. Every heavy command ran in one
`fv_slot.sh` scope at a time (MemoryHigh 6G, MemoryMax 8G, no swap), attempt names `X2b-*`.

Tools: X2's runner `fv_x2_run.py` unchanged (Charon 454586e9, Aeneas 0d21a9ec, hashes checked at every run; the
command line and environment in X2's README, deployed feature list, overflow checks off). Native compile:
`fv_x2b_native.sh` (a copy of `fv_x2_native.sh` writing under `W/x2b`): the raw `Types`, `Funs` and the two generated
templates renamed to the module names they are imported under, zero edits, compiled with Lean 4.36.0-rc2 against X3's
native library build under `W/x3` by reference (read only).

## Files

| File | Content |
|---|---|
| `rewrites2/*.patch` | one cumulative `diff -u` per changed source file, against the frozen file (X2's changes to that file included) |
| `rewrites2.tsv` | one row per rewritten function |
| `rewrites2/probes/` | the reproducer crates' sources (`probe-b-lib.rs` to `probe-g-lib.rs`) and their manifest |
| `../host/fv_x2b_*` | the scripts and configs of this task |

The patches supersede X2's per-function patches `rewrites/*.patch` for the same files (`history.rs`, `nullifier.rs`,
`pair_forest.rs`, `processor.rs`, `vault.rs`): each of mine contains X2's hunks for that file. X2's patches stay as they
are. X2's `require_unique_accounts` recursion (`rewrites/require_unique_accounts.patch`) is replaced (class 8).

## Reproducers and accepted shapes

The probe crates (`W/x2b/probe/{b..g}`, lock derived from X2's probe lock by renaming the package) are compiled with the
Pool emission's Charon and Aeneas flags (Aeneas without abort, so that every rejection is listed) and then natively.
"Translates" means no Aeneas error for the function; "elaborates" means no native Lean error in its declaration or in
an instance it needs.

### Class 1: `?` on account-data borrows (probes b, c, d, e)

Cause, read side: `?` on `Result<Ref<&mut [u8]>, ProgramError>` makes Aeneas give `Result::branch` a backward function
(the value holds a borrow), so the emitted code destructures `(cf, _)`; the native `branch` returns only the
`ControlFlow` ("expected a product type, got ControlFlow ..."). The same holds for `?` on any `Result` whose `Ok` value
holds references: `[&AccountInfo; 5]` from `exact_five_accounts`, `[AccountInfo; 5]` from the transfer-account
builders, `Option<&AccountInfo>` from `get`.

Accepted shape, read side (probe b, q1 to q5 and q10, all translate and elaborate): an explicit match with an early
return, `let data = match account.try_borrow_data() { Ok(data) => data, Err(err) => return Err(err) };`, the guard
kept to the end of the same scope as before (a block where the frozen code used a temporary guard). This is what `?`
does here (`From<ProgramError> for ProgramError` is the identity). Zero added work. The frozen `?` form (q0) fails.

Write side: no accepted shape. Every write through `RefMut<&mut [u8]>` (the type `AccountInfo::try_borrow_mut_data`
returns; the SDK's `AccountInfo::data` is `Rc<RefCell<&'a mut [u8]>>`) fails natively, in 17 shapes:
- direct writes through the guard, `match` acquisition (probe b q6 to q9, c w-series): the concrete call of
  `RefMut::deref_mut` destructures four components `(s, _, _, _)`, the generated template declares three
  (`T × (T → RefMut T) × (RefMut T → RefMut T)`): "expected a product type, got RefMut (Slice U8) → RefMut (Slice U8)";
- generic writers over `&mut RefMut<T>` or `D: DerefMut<Target = &mut [u8]>` (c w1, w2, w3, w5, w8): rejected by
  Aeneas (`Unreachable`, `Could not find var for symbolic value`);
- `RefMut::map` (c w4): closure instance type mismatch;
- the guard moved by value into a generic writer (d d1 to d4): the writers translate and elaborate, but they need a
  trait instance for `&'a mut [u8]`, and every method taking `&mut self` there has one more backward function than
  the trait declaration (`Slice U8 → Slice U8 → Result (Slice U8 × (Slice U8 → Slice U8))` against
  `... → Result (Slice U8)`); std's `AsMut`/`DerefMut` instances for `&mut T` fail the same way (c);
- moving the slice out with `mem::take` and back (e e1, e3, e4): the `Default` instance for `&mut [T]` and the by-value
  trait methods mismatch the same way.
The common cause is a mutable borrow nested in a mutable borrow (`&mut &'a mut [u8]`): Aeneas gives it one more
backward function at a concrete site than the generic templates and the native trait structures carry. No Rust shape
of the Pool can avoid that type, because the SDK fixes it. Writes are kept as in the frozen code, with the guard
acquired by the explicit match (same order, held across the CPI as before). Each account-data write site is one native
error; they are listed under "Named gaps".

### Class 2: binders named like a module

A parameter or local named like an emitted module (`vault`) makes Lean read `vault.pool_v1_vault_...` as a field
projection of the local ("Invalid field ... The environment does not contain AccountInfo.pool_v1_vault_tag"). Probe b:
n0 fails, n1 (renamed) elaborates. Applied: `vault` renamed to `vault_account` (parameters, three functions in
`processor.rs`) and to `vault_state` (locals holding the parsed token account, four functions in `vault.rs`). The match
binder of class 1 is `err`, not `error`, because `error` is also a module. Zero compute change.

### Class c: `Unimplemented` in `translate_end_abs_identity` (probe f)

Two causes:
- the array pattern over the returned `[&AccountInfo; 5]` and clones out of it (c0), and also indexing that array
  (c1). Accepted (c2): run the same check (`exact_five_accounts`), ignore its value, clone from the slice by index in
  the same output order (the check returns references to `accounts[0..5]` in order). Same clones; five slice bounds
  checks that the compiler can remove after the length check.
- any function with an `Option<&AccountInfo>` parameter is rejected (probe g h1 to h5, whatever the body; probe f c4 to
  c6). An `Option<&AccountInfo>` value from `get` or `first` fails natively (f e1, e2, c7). Accepted: no
  `Option<&AccountInfo>` anywhere. Account lookups become a length check and an index with the same error at the same
  point; the optional verifier checkpoint becomes a slice of zero or one accounts (`&accounts[i..i + 1]` or
  `&accounts[..0]`), unwrapped by `is_empty` and `[0]`. A slice plus `Option<usize>` (h6) also elaborates.

### Class d: function items passed as closure values (probe f)

`with_h(a, &mut hash2)` (d0) is rejected (the `FnMut` shim of a function item has a higher-ranked signature). Accepted:
a direct call (d1) or an explicit match (d3). Applied to `note_commitment` (body of `note_commitment_with` with
`hash_fields` called directly; `note_commitment_with` stays for its traced caller) and
`IncrementalMerkleTreeV1::decode_with_empty_roots` (explicit match instead of `.map(Validated..::into_inner)`).

### Class e: settlement entry generic over two callables (probe f)

`process_pair_forest_terminal_with_verifier_v1` is generic over `V: FnOnce(&Pubkey, &AccountInfo<'info>, ...)` and
`S: FnOnce(&[u8])`; the elided lifetimes make a higher-ranked constraint, and Aeneas rejects the signature
("found an occurrence of a lifetime constraint relating a higher-ranked lifetime to a free lifetime", e0). Accepted
(e1, e2): a local trait for the two host calls, generic over the trait. Applied: trait `PairForestTerminalHostV1<'info>`
(`verify`, `set_return_data`), production impl `SolanaPairForestTerminalHostV1` calling
`dispatch_pair_forest_terminal_readonly_v1` and the `set_return_data` syscall, handler
`process_pair_forest_terminal_with_host_v1`. The former function with the closure signature stays, compiled only for
tests and the audit-only ASF8 route (feature off in the deployed build), as an adapter over the trait; the 18 test
call sites are unchanged. Zero added work on the deployed path (static dispatch, the same two calls).

### Class f: one exploding body (deposit handler; also the settlement handler)

Charon reconstructs the code after each branch that contains `?` exits once per branch. The deposit handler's two
three-way page-mode branches gave a 370 MB body (X2). With class e the settlement handler gets a declaration for the
first time and showed the same effect: in run `X2b-pool-r3` Aeneas sat at MemoryHigh (131,636 high events, log not
growing) and was stopped after 7 minutes. Accepted shape: each branchy stage becomes a named helper that returns a
plain value, so the caller has no branch with a long tail:
- deposit: `select_deposit_page_mode_v1` (returns mode, token start, account count) and
  `prepare_deposit_writable_page_v1` (payer checks, PDA creation CPI, zeroed check; returns the index of the writable
  page);
- settlement: `plan_terminal_withdrawal_v1`, `terminal_writable_page_index_v1`, `settle_terminal_withdrawal_v1`,
  `write_terminal_page_v1`.
Same checks, CPIs, errors and writes in the same order. Added work: one call per helper unless inlined, one indexed
lookup of the writable page (bounds already checked by the exact account count).

### Class g (probe g)

- Loop or `any` closure in a function that holds `AccountInfo` values (`require_alias_free` g1, `require_checkpoint_distinct`
  g7): rejected. Accepted: keys copied to a plain array and compared in a helper over plain keys (g2 with the scan
  flattened), or the comparisons written out (g8).
- A conditional write into a local key array (`if count > i { keys[i] = *accounts[i].key }`) in such a function:
  "Nested borrows are not supported yet" at the join (g2 line 61; seen again in the Pool). Accepted: an unconditional
  array literal of `account_key_or_zero(accounts, i)` (a helper whose branches return a plain key).
- Nested `while` loops over a borrowed plain array: "Nested borrows" at the inner loop join (Pool run r2). Accepted:
  one loop over (left, right) pairs with the same visiting order.
- Early return inside a loop over plain data (`encode_lane_from_authenticated_result_v1`, g3; "could not match the
  contexts"): accepted shape a `while` with a flag in its condition and the error after the loop (g4).
- Loop with `?` pushing into a `Vec` in a function holding accounts (`decode_checkpoint_lanes_box_v1`, g5: "unsupported
  nested borrows"). Accepted (g6): the eight decodes written out with explicit matches, still into the heap `Vec`
  (an `[_; 8]` of lane states on the stack would exceed the SBF frame).
- Slice pattern `let [a, b] = accounts else {..}` (PtrMetadata, X2's b8/c4/c5): length check and indexing (X2's c6),
  applied in `invoke_pair_forest_terminal_with_runtime_v1` and both `authenticate_verifier_selection_*`.

### Class 8: `require_unique_accounts`

X2's recursion costs one call per visited pair and per left index (about n(n+1)/2 + n calls) and a depth up to 2n + 1
frames. Replacement: the keys copied, written out without a loop, into `[Pubkey; 18]` by `account_key_or_zero`, and
the pairwise scan in `keys_repeat`, a helper over plain keys: one `while` over (left, right) pairs, left ascending then
right ascending, stopping at the first repeat, the same result and error as the frozen nested loop. Largest n: 18 (the
settlement layout: at most 5 + 7 + 5 + 1 accounts; initialize 14, checkpoint 12, deposit at most 11). A longer list is
rejected with the duplicate error; no caller can pass one, because each first requires an exact count of at most 18.
This is a narrowing of the function on inputs no caller produces, stated here. Cost against the frozen code: the same
n(n-1)/2 key comparisons in the same order, plus 18 key copies (576 bytes) and 18 index checks, one call, no
recursion, call depth one frame. Differential test `x2b_unique_accounts_differential` (frozen body kept under
`#[cfg(test)]`; every count 0 to 18, every single duplicated pair, 200 random lists per count from a small and a large
alphabet).

### Class 9: library-driven items

- `Option::ok_or(e)?` and `ok_or(e)` returned directly: the emitter treats `ok_or` as pure (`lift`), the native
  library returns `Result`: "Application type mismatch ... CoreOpsTry.branch" (probe b o0, o8). This is the cause of
  the two "application type mismatch" rows X2 left undiagnosed (`validate_root_page_bytes`, `process_instruction`).
  Accepted: explicit match with the same error value, converted as `?` converts it (`return Err(e.into())`).
  `ok_or_else`, `Option::map`, `Result::map_err`, `Option::and_then`, `Result::map` and `?` on a plain `Result`
  elaborate natively (o2 to o7); only `ok_or` has the problem. Applied to every single-line `let x = .. .ok_or(e)?;`
  of the reachable Pool code, and by hand where the call spans lines.
- Shift amounts: with overflow checks off `x >> n` and `x << n` become `wrapping_shr/shl`, whose native signature takes
  `u32`; a `usize`, `u8` or untyped literal amount fails ("argument level has type Usize but is expected to have type
  U32"). Accepted: the amount as `u32` (`level as u32`, `u32::from(lane)`, `8u32`); the value is the same.
- `Iterator::map/any/all/sum/fold/zip/rev`: an emitted std iterator instance lists every method the crate uses, and the
  native `Iterator` structure has no such fields, so one use anywhere gives errors in the std instance declarations.
  Accepted (probe c l1 to l8, all elaborate): `while` with an index and a flag, `for` over a range (with or without
  `break`), `for` over `slice.iter()`. In the Pool: `data.iter().any(|b| *b != 0)` and `.all(|b| *b == 0)` replaced
  by the existing `page_bytes_are_zero` (a slice comparison, fewer instructions than the byte loop), same result for
  every input (all-zero test). The `aspis_statement` and `aspis_core` uses are not rewritten (see "Not done").

## Results

Runs (deployed setting: overflow checks off, deployed feature list; X2's 108 extra roots kept):

| Attempt | Tree state | Charon | Aeneas | Native `Funs` errors | Tests (Pool; statement `x2b_`) |
|---|---|---|---|---|---|
| X2's `X2-rw-ab` / `X2-native-rwab` | classes a, b | 0 | abort, 0 | 68 | 78/78 |
| `X2b-pool-c12` | + class 1 read side, class 2 | 0, LLBC ec74fe6efb0effa63c93fc39deeb812379a2434325f2c98ffb27764356c36eec (909 functions) | abort, exit 0, 184.0 s; scope wall 4:07, peak RSS 4,008,440 kB | 53 in 28 declarations | not run |
| `X2b-pool-r2` | + `?` on reference-holding results, class c builders, class d, class 8 (nested loop) | 0, 49.1 s, LLBC a883fd... (908) | abort, exit 2: "Nested borrows are not supported yet" in `keys_repeat` (fixed: one loop) | not compiled | `X2b-test-r2`: 79 passed, 0 failed; 2 passed |
| `X2b-pool-r3` | + class e, optional accounts as slices, class g items, `ok_or` sweep | 0, LLBC b92ab0bcc2c008c2bce618015d141b96abdc6ddcbb8e1764c62f186b415a4a8c (945) | no abort; stalled at MemoryHigh (settlement handler body), stopped after 427 s; rejections before the stall: `require_unique_accounts` (conditional key writes), `authenticate_verifier_selection_v1` (Unreachable), `invoke_pair_forest_terminal_with_runtime_v1` (conditional push) | not compiled | `X2b-test-r3`: Pool tests did not compile (four test call sites passed `Option`; fixed) |
| `X2b-pool-r4` | + class f split, `account_key_or_zero`, registry value comparisons | exit 101 (a type path in a new helper; fixed) | not run | not compiled | not valid |
| `X2b-pool-r5` | r4 fixed | R5_CHARON | R5_AENEAS | R5_NATIVE | R5_TESTS |

R5_DETAIL

## Not done, and why

- Account-data writes (class 1, write side) have no accepted shape with this tool pair and the native library, in 17
  shapes tried (probes b to e). Every write site stays one native error: the four handlers' write paths
  (`process_pair_forest_deposit_with_runtime_v1`, `process_pair_forest_terminal_with_host_v1`,
  `process_pair_forest_checkpoint_with_runtime_v1`, `process_pair_forest_initialize_with_runtime_v1`). So none of the
  four handlers can elaborate natively with zero edits. Resolving it needs a change outside the Pool source (the
  Aeneas templates or the library's model of `RefMut<&mut [u8]>`), which this task's rules exclude. The generic
  by-value writer of probe d (d1 to d4) is the shape that would reduce it to one trait instance if such a change came.
- Initialize handler (`process_pair_forest_initialize_with_runtime_v1`): not rewritten (break to an outer loop; a loop
  pushing `RefMut` guards into a `Vec`, which is also a write-side case). Still opaque.
- `decode_lane_account_from_program_invariant_v1` (reached: the deployed feature `pair-forest-source-invariant-audit`):
  only its borrow is rewritten; its frontier loop with `?` and an early return in a function holding AccountInfo is
  not. Still opaque. The shape is known (the plain-data part into a helper over `&[u8]`, a `while` with a flag).
- `plan_pair_forest_terminal_dispatch_with_bytes_v1` (early return inside a loop): not rewritten, still opaque.
- `invoke_pair_forest_terminal_with_runtime_v1`: the conditional `push`/`insert` of the verifier checkpoint into the
  CPI vectors is still rejected (nested borrows at the join, run r3); not rewritten.
- Library crates: the `aspis_statement` items (`plan_pool_v1_pair_forest_checkpoint_v1`,
  `encode_pool_v1_pair_forest_checkpoint_v1`, `validate_with_empty_roots`, `PoolV1PairLeafWitnessV1::validate`,
  `ValidatedIncrementalMerkleTreeV1::append_one`) stay opaque, and the native errors in `aspis_statement` (poseidon2
  `iter_mut().enumerate()` loops, `RATE` closure instances, `decode_tree_image_unvalidated`, `pool_v1_empty_roots`,
  `POOL_V1_PAIR_EMPTY_ROOTS`, `decode_digest_canonical` and `decode_verifier_policy_v1` (`ok_or`), and the std iterator
  instances needing `map/all/any/sum`) are not rewritten. The accepted shapes for them are recorded under class 9.
- Single root: the configs still carry X2's 108 extra roots beside `processor::process_instruction`; the single-root
  run was not reached.
- `plan_legacy_withdrawal_transfer_from_identity_v1` emitter line break: not addressed separately.
- Differential tests: added for `require_unique_accounts`, `require_alias_free`, `encode_lane_from_authenticated_result_v1`,
  `pack_pool_v1_pair_forest_marker_seed_v1`, `note_commitment`, `decode_with_empty_roots`. Not added for the shift-type
  changes in `next_pair_forest_lane_v1` and `validate_pair_forest_request_accounts_v1` (type of the amount only) or
  for functions that hold accounts (covered by the Pool's existing tests).
- Silent-fault checks: the reversed-mutable-iterator search was re-run in every emission with a scan
  (`r0_transcript.rs:129` only, not emitted); no rewrite adds `rev()` or a `Box` written through (the new `Vec` and
  `Box` uses are X2's existing ones). Reading of the emitted Lean for the handlers' write paths: in every emission so
  far the write goes into the `RefMut` returned by `try_borrow_mut_data`, whose backward functions are discarded
  (`let (r, _, _) <- ...try_borrow_mut_data acc`), so the returned value does NOT contain the account-data writes:
  the AccountInfo is an opaque SDK value and the model drops the write. Recorded as "no" for every write path; seen in
  probe b (q6 to q9) and in `process_pair_forest_checkpoint_with_runtime_v1` of `X2b-pool-c12`. Not rechecked on r5.
- Host reachability: the build host became unreachable from this machine at about 11:45 UTC while `X2b-pool-r5` and
  `X2b-test-r5` were running; their results are not read here.

## Rerun

1. Copy `../host/fv_x2b_*.{sh,py}` and X2's `fv_x2_run.py` (with its `frz/` and `worker/` directories, as in X2's
   README) to `W/x2b/bin`, the configs to `W/x2b/config`. Build the rewrite tree: copy `W/src-frz-a` to `W/x2b/rw-tree`
   and apply `rewrites2/*.patch` (each against the frozen file; `patch -p1`).
2. Emission and native compile: `bash W/x2b/bin/fv_x2b_job.sh <name> 3000 W/x2b/<out> bash W/x2b/bin/fv_x2b_emit.sh
   W/x2b/config/<cfg>.json W/x2b/<out> charon,aeneas,scan native` (use `noabort` instead of `aeneas` for the full
   rejection list); with `fv_x2b_watch.sh <aeneas log> <status file>` running beside it for a memory stall.
3. Tests: `bash W/x2b/bin/fv_x2b_job.sh <name> 3000 W/x2b/tests bash W/x2b/bin/fv_x2b_test.sh W/x2b/rw-tree test-rw`.
4. Probes: the same `fv_x2b_emit.sh` with `fv_x2b_cfg_probe_{b..g}.json` and stages `charon,noabort native`.
5. Patches: `fv_x2b_patches.sh <frozen root> <rewrite root> <out dir>`.
