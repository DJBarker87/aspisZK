# Aspis verifier program: stage 2 rewrites continued (task X1b)

Status: target not yet established. A tool record. It says which rewrites of the frozen verifier program make the
Charon and Aeneas tools translate all of it from the single entry, and whether the RAW Aeneas output then compiles
against the native Aeneas Lean library. Nothing here is a proof. A translated, elaborated function is not a verified
function.

Source: frozen commit 3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de (`W/src-frz-a`, `W` = `~/project-offloads/future-version-20261111`
on the build host). Work trees: copies of X1's `W/x1/rw3` (frozen + X1's A, B2, C2, I; ELF byte-identical to the frozen
measurement ELF) under `W/x1b/`, one snapshot per item: `rw-tree` (C), `rw-D`, `rw-J`, `rw-F`, `rw-L`, `rw-K`, `rw-E`,
`rw-G` (final), `rw-F2` (an alternative F shape), `rw-0` (unmodified frozen copy). Nothing was applied to the
repository, to `W/src-frz-a` or to `W/x1`. Every heavy command ran in one `fv_slot.sh` scope at a time (MemoryHigh 6G,
MemoryMax 8G, no swap, receipts `W/receipts/X1b-*`); no memory event.

## Result in short

- Final tree `rw-G` (X1's rw3 + every patch in `rewrites2/`): Charon exit 0, Aeneas `-abort-on-error` exit 0 (139.5 s,
  peak 2,697,560 kB; LLBC d98a... for E, 51ecc0b8312a5dfa0e84041aac9e50c0b553a37548e8a4fa8ce5e878a0d7ba2a for G, 1316
  function declarations), from the single entry `process_r1_cost_probe_instruction`, with only two items opaque: the
  account write boundaries `write_zero_data` and `write_lamports`.
- The RAW Aeneas output compiles against the native library with zero edits: **0 errors** in all four modules
  (`Funs` 0:42.4, peak 3,495,084 kB). X1 left 44.
- Bodiless declarations (generated templates; no `axiom`/`opaque`/`sorry` in `Funs`): Aspis 2 (the two write
  boundaries), SDK and runtime 18, std 29. Emission flag added: `-max-recdepth 4096` (item M).
- ELF: not byte-identical after C (and after every later item). Compute on the two recorded payments (verifier CU,
  frozen Pool replay): frozen 1,184,299 / 1,181,418; final 1,185,533 / 1,182,652, **+1,234 / +1,234** (+0.10 %), all of
  it from F (+1,386); the other items together -152.
- Tests: on the final tree every X1b differential test passes (18); program lib tests give the same failing list as the
  frozen copy in both configurations (aspis: 25 two-transaction tests; two-transaction: 1,
  `owned_adapter_native_differential_six_fixtures_and_1200_mutations`, which fails identically on the frozen copy).

## Files

| File | Content |
|---|---|
| `rewrites2/*.patch` | one `diff -u` per changed source file, against the FROZEN file, cumulative over X1b's items (and X1's hunks in the same file, see below) |
| `rewrites2.tsv` | one row per rewritten function or site group: item, why rejected, change, prover-compiled, results, ELF, compute delta, trades-compute flag |
| `std-external-callers.tsv` | every std external left in the final emission and the Aspis functions calling it, with file and line |
| `target-os.tsv` | every `cfg(target_os)` site of the four crates (item H) |
| `compare-frza-diffs.txt` | fault check (e): the body diffs of every `different` row of X1's `compare-frza.tsv` |
| `x1b-gates/` | gate outputs (`gates-out/`), the per-run axiom and write-call lists, native error lists, depth-test logs, objdump totals (`elfdiff/`), and the sources of the reproducer crates `probe-crates/e` (item E) and `probe-crates/m` (fault 1) |
| `../host/fv_x1b_*` | scripts and configs |

Patches that supersede X1's: `r1-cost-probe__r1_pool_adapter.patch` contains X1's C2 hunks (supersedes
`rewrites/C-close_checkpoint.patch`, `rewrites/C-lifecycle_accounts.patch`); `aspis-r1-cost-probe__compact.patch` contains
X1's I rename (`encoded`) and replaces `rewrites/F-expand_values.patch` (X1's while form was not used, see F); the patches
of `one_tx.rs`, `weights.rs`, `pool_v1/pair_forest_copy_terminal.rs`, `pool_v1/pair_forest_semantic_terminal.rs` and
`state_only_poseidon.rs` contain X1's A (shift) hunks of those files. X1's other patches (A in other files, B) stay
as they are and are needed: the final tree is X1's rw3 plus these patches.

Prover-compiled patches (the client build compiles these crates and no function-level cfg excludes the rewritten
functions; for the privacy lead): `aspis-core__circle`, `aspis-core__state_only_hiding`, `aspis-core__state_only_prefix`,
`aspis-statement__atomic_statement`, `aspis-statement__pool_v1_pair_forest_copy_terminal`,
`aspis-statement__pool_v1_pair_forest_semantic_terminal`, `aspis-statement__state_only_poseidon`,
`aspis-r1-cost-probe__candidate`, `__compact`, `__one_tx`, `__r1_wire` (except the second `decode_k`, under
`validated-decode`, off in the client), `__verifier`, `__weights`. Each rewritten function keeps the same arithmetic
operations in the same order; each file's patch adds its differential test module at the end of the file.

## Runs

| Attempt (receipt) | What | Exit | Notes |
|---|---|---|---|
| `X1b-item-C` | emission C (abort), native probe, gates; program tests (aspis); build (failed: the build copy omitted `docs/`, fixed) | 0 | scope peak 3,360,632,832 B |
| `X1b-batch1` | SBF builds 0 (frozen copy, both configurations), C1, D (both), J, F, L; replays; item M depth test; item E reproducer | 0 | the frozen copy rebuilds 827aaec1... |
| `X1b-probe-e2` | item E reproducer with variants e5, e6 | 0 | |
| `X1b-batch2` | tests on rw-E (five configurations); builds C2 (both), K, E (both); replays; emission E (abort), probe, gates | 0 | scope peak 6,371,684,352 B, wall 22:59.75 |
| `X1b-batch3` | frozen test baselines; tests on rw-G; builds G (both), F2; replays; objdump comparison; emission G; gate validation | 0 (wall 9:53.70, scope peak 5,055,090,688 B) | |

Emission command: X1's (`fv_x1b_run.py` is `fv_x1_run.py` unchanged): `charon cargo --preset aeneas --mir built
--sysroot default --include core::option::Option --include core::result::Result --include core::option::_::ok_or
--start-from crate::process_r1_cost_probe_instruction --include aspis_r1_cost_probe --include aspis_statement --include
aspis_core --opaque crate::r1_pool_adapter::write_zero_data --opaque crate::r1_pool_adapter::write_lamports ...
--features aspis`, overflow checks off, the two deployment ids of the devnet build; `aeneas -diagnose-translation
-sequential -no-progress-bar -abort-on-error -max-recdepth 4096 -backend lean -namespace AspisX1 -split-files`. The X1
opaque flags on `deployment_ids::program_id`, `deployment_id`, `close_checkpoint`, `lifecycle_accounts` and
`aspis_core::field::_::inv` are all gone. Native compile (`fv_x1b_probe.sh`): X1's `fv_x1_probe.sh` with X1b paths: the
raw `Types.lean`, `Funs.lean` and the two generated templates (renamed to the module names they are imported under),
zero edits, Lean 4.36.0-rc2 against X3's library under `W/x3` by reference.

Native-library errors in `Funs` after each emission (other modules 0 errors throughout): X1 rw2b 44; C 44 (the C
functions elaborate; the count is unchanged because the 44 are elsewhere); E (C, D, J, F, L, K, E with the M flag)
**0**; G (final) **0**. Runs D, J, F, L, K were built and replayed but not emitted separately; the errors each item
removes are attributable by declaration (the C error list `probe/C/errors.tsv` names every failing declaration):
D removes 5 (`LifecycleKind::body_len`, `writable_prefix_len`, `lifecycle_init`, `_write`, `_finalize`), J 17 (one per
failing `ok_or` declaration), F 10 (the `ChunksExactMut` Iterator impl: 6; `expand_values` and its loop body: 4), L 10,
M 2 (`TABLE_A`, `TABLE_B`): 44 in all; E 0 (its two items were axioms, not errors).

## Item C: `close_checkpoint` and `lifecycle_accounts` (done)

Shape: value comparisons (`*checkpoint.owner != *program_id`; in `lifecycle_accounts` `*target.key == *authority.key`,
`*target.owner != *program_id`), X1's length check and indexing kept, the `ok_or` on the lamport sum as an explicit
match, and the three account writes moved into account write boundaries. Both functions translate and elaborate
natively (runs C and E).

Account write boundaries (program crate, `r1_pool_adapter.rs`, appended after the last test module so no earlier line
moves; opaque by name, axioms in the generated template):

    #[inline(always)]
    fn write_zero_data(account: &AccountInfo<'_>) -> ProgramResult {
        let mut data = match account.try_borrow_mut_data() { Ok(data) => data, Err(err) => return Err(err) };
        data.fill(0);
        Ok(())
    }

    #[inline(always)]
    fn write_lamports(account: &AccountInfo<'_>, lamports: u64) -> ProgramResult {
        let mut handle = match account.try_borrow_mut_lamports() { Ok(handle) => handle, Err(err) => return Err(err) };
        **handle = lamports;
        Ok(())
    }

Each is 5 lines of body including the signature line and the closing brace (3 statements); 10 lines of Aspis code
in write-boundary functions in the program crate in total (12 with the attributes). Grammar: one SDK borrow of one
account's mutable handle, the borrow error returned unchanged, one `<[u8]>::fill(0)` (core slice fill over the whole
data slice; it cannot panic) or one assignment of a parameter; no arithmetic, branch on data, loop or read of contents.
Contracts: `write_zero_data(a)`: after the call `a`'s data equals the old data with every byte set to 0; every other
field and every other account unchanged; a failed borrow is an error return with nothing changed.
`write_lamports(a, v)`: after the call `a`'s lamports equal `v`; every other field and every other account unchanged;
a failed borrow is an error return with nothing changed.

Frozen writes of `close_checkpoint` (frozen `r1_pool_adapter.rs`) and the boundary call that now performs each, in the
same order, same lines:
1. line 1053 `checkpoint.try_borrow_mut_data()?.fill(0);` -> `write_zero_data(checkpoint)?;` (line 1053)
2. line 1054 `**checkpoint.try_borrow_mut_lamports()? = 0;` -> `write_lamports(checkpoint, 0)?;` (line 1054)
3. line 1055 `**base.try_borrow_mut_lamports()? = total;` -> `write_lamports(base, total)?;` (line 1055)
The total (`base.try_lamports()? + checkpoint.try_lamports()?`, checked, `ArithmeticOverflow` on overflow) is computed
by `close_checkpoint` before any write, as in the frozen code. The second and third calls cannot overflow anything
(plain assignments). The pure caller's checks are the frozen checks at the frozen error values.

Checks. The emitted `close_checkpoint` (run E) calls `write_zero_data ai`, `write_lamports ai 0#u64`,
`write_lamports ai1 total` in that order, each followed by `Try.branch`; no translated function claims a write: the
write-route gate (`fv_x1b_writecalls.py` over the LLBC: every call from an Aspis body of `try_borrow_mut_data`,
`try_borrow_mut_lamports`, `RefCell` `borrow_mut`, `RefMut` `deref_mut`/`index_mut`) lists **no call** in run E or G
(in X1's rw2b and in run C it lists the three lifecycle handlers, the planted positive). The bodiless-Aspis gate
(`fv_x1b_aspis_axioms.py`) lists exactly `write_lamports` and `write_zero_data` in runs E and G. The axioms take the
`AccountInfo` and return only the result: the model does not represent the account effect at all, which is what the
boundary class records. Read-after-write: in `close_checkpoint` no account is read after the first boundary call
(source and emitted body). The Pool worker's grammar checker `fv_x2c_write_boundary_check` is not committed at the time
of writing; the grammar, route and order checks above were made by my own scripts and by reading.

Test (`x1b_close_checkpoint_rewrite`, appended to `r1_pool_adapter.rs`): the frozen body under `#[cfg(test)]` against
the rewritten one on 240 cases (the program-test fixture shape; wrong owner, not writable, executable, base not
signer, base lamports `u64::MAX` and `u64::MAX - rent`, one and three accounts, empty data; valid, wrong-seed,
non-UTF-8, empty-seed, tag 6 and tag 3 instructions; no held borrow, checkpoint data held, base lamports held,
checkpoint lamports held mutably): the same result and the same complete data and lamports of every account: passed.
Program lib tests with `--features aspis`: 67 passed, 25 failed; the same 25 as on the item-C tree (two-transaction
tests that fail under one-tx; the frozen baseline list is in batch 3: frozen copy `rw-0`: aspis 64 passed, 25 failed; two-transaction 88 passed, 1 failed; final `rw-G`: 68 / 25 and 94 / 1, the failing test names identical to the frozen ones; verifier crate (`--features aspis`) 50 passed; statement 273 passed and core 286 passed (2 ignored) on `rw-E`).

ELF: e1ee500c1fd4efdbe451a942905bd46058d65728eecd6e8c1916b356aea4e019 (not byte-identical). The ELFs carry no function symbols (`llvm-objdump -d` shows 3 symbol blocks), so the per-function comparison
the brief asks for is not possible from the binaries; the totals (`elfdiff/`): instructions frozen 115,229; after C 115,223
(-6); D 113,704 (-1,519: the lifecycle code); J 113,632 (-72); F 113,650 (+18); L 113,667 (+17); K 113,658 (-9); E the
same as K; G 113,615 (-43).
Compute on the two recorded payments: 0 / 0 (verifier CU 1,184,299 / 1,181,418, as frozen).

## Item D: lifecycle handlers (done: compiled out under one-tx)

`pool_route::admitted` (`pool_route.rs` 16-18) admits exactly `[3, 10]`, `[3, 11]`, data starting `ASQ8` and
`is_close_checkpoint` data (tag 7). `process_r1_cost_probe_instruction` returns `InvalidInstructionData` before any
account access when `admitted` is false (`lib.rs` 75-80), in every `pool-adapter` build (the deployed `aspis` and the
two-transaction `pool-adapter,private-leaf-salts`). `r1_pool_adapter::process` sends first bytes 4, 5, 6 to the
lifecycle handlers; none of the admitted forms has first byte 4, 5 or 6 (3, `A` = 0x41, 7). So the deployed program
cannot reach them, in either configuration (the existing test `r15_release_rejects_lifecycle_close_attempts_on_real_checkpoint_shape`
exercises this).

Shape: `#[cfg(not(feature = "one-tx"))]` on `LifecycleKind` and its impl, `lifecycle_accounts`,
`validate_lifecycle_header`, `validate_lifecycle_final_body`, the three handlers and the three dispatch arms, each on
the line of an existing attribute or arm (no line added); the lifecycle test `r15_lifecycle_requires_recorded_signer_to_upload_or_seal`
gated the same way. Two-transaction ELF: C2-2tx and D-2tx are both
2bff0bcf75e1c27b6be87f7a568770d61fc797326cf02b56d82d55ebed039ab0 (unchanged by D). One-tx ELF
84b98a13d13cb351b45098ce7e3dfdff5b73761c3e1917397588a3343e20dade. Compute: -3 / -3. In the emission the lifecycle code
is absent (0 occurrences of `lifecycle` in run E's Funs).

## Item J: `Option::ok_or` (done)

Native mismatch test: of `ok_or`, `ok_or_else`, `map_err`, `Result::map`, `and_then`, `copied`, `unwrap_or_else`,
`is_err`, only `ok_or` produced errors in the native compile of runs C and E (every other one occurs in the emission
and its call sites elaborate: no error names them; in run E `and_then`, `map_err`, `copied`, `unwrap_or_else` still
occur and run E has 0 errors). This agrees with the Pool worker (X2b, class 9).

Sites: the 30 `lift (core.option.Option.ok_or` sites of the emission, in 18 functions (rewrites2.tsv). Shape: `match o
{ Some(v) => v, None => return Err(e) }` (or `let Some(x) = o else { return Err(e) }`), the same error value (`?`
converted through `From<E> for E`, the identity). Line- and column-preserving: the `match` keyword is put into the
indentation, or at the end of the previous line with the old `let x =` replaced by spaces; no line is added. ok_or sites
outside the emission (test oracles, the two-transaction `scan_proof_buffer`/`stage2_owned`, the first `decode_k`,
`Reader::e/k`, the lifecycle code) are not touched. ELF c3abe8aa44352ff7e7c42deea90e9c7061d009e9e000ad6082f8598ff23e3fa0;
compute -116 / -116. Script `fv_x1b_rwJ.py`.

## Items F and K: iterator adapters (F done, trades compute; K done for 14 functions)

F, `compact::expand_values`: `for (k, c) in encoded.chunks_exact(16).enumerate()` with `let o = &mut out[32 * k..32 * k + 32]`
(the native library takes `chunks_exact` and `enumerate`; `chunks_exact_mut` and `zip` are what failed). Same bytes in
the same order. It removes the emitted `ChunksExactMut` Iterator impl (the `zip`/`fold`/`all`/`any`/`rev` field errors)
and the `Zip` destructuring errors. Hot path: yes (once per payment over 455 values: 426 semantic and 29 y1). Cost:
+1,386 CU on each recorded payment (one added range check per value; the frozen zip over two exact-chunk iterators
needed none). **Trades compute.** Alternative tried: X1's counted `while` with both slices indexed (`rw-F2`):
113,467 instructions (148 fewer than G) but +3,194 CU more than the final tree on each payment (1,188,727 / 1,185,846): rejected, the enumerate form is kept. No shape without an added check was found. Write check (emitted Lean, run E `Funs.lean` 4363-4400): the loop body writes the copy (`copy_from_slice`
through `index_mut_back1`) and the fill (through `index_mut_back2`) into `o`, puts `o` back into `out` with
`index_mut_back`, and returns `out1`; `expand_values` returns `(Ok (), out1)`: yes, both writes are in the returned value.

K: the iterator adapters the native `Iterator` lacks, where they occur in emitted Aspis bodies: `rev` (`for i in
(0..n).rev()` and `.iter().rev().fold`), `fold`, `any`, `RangeInclusive::contains`, `into_iter().fold`. Shapes: counted
`while` loops (`let mut i = n; while i > 0 { i -= 1; .. }`, the same visiting order), the same additions written out,
or a comparison with a zero array; line-preserving. 14 functions (rewrites2.tsv). Hot functions among them: none adds
per-iteration work (the loops are the same loops). Compute of all of K: -24 / -24. Not rewritten: `merkle_verdict`
(`chunks_exact(8).any`, once per tree over the unused tail of the node buffer: every rewrite found adds a check per word
or per byte; left as the std external `Iterator::any`), and the `core::array::map` sites (not an iterator method; 11
sites, several in the Poseidon evaluation, left as the std external `core.array.Array.map`). Writes through `&mut`
in K: `Selectors::expand` writes `weights[2 * index]` and `weights[2 * index + 1]` in the reversed inner loop; the order
is kept (index descending), the array is local and returned. No `rev()` over a mutable iterator is introduced.

## Item L: `authenticate_invariant_release_registry` (done)

The immutable-deployment branch and the v1 tail moved unchanged into `#[inline(always)]` helpers
`authenticate_release_registry_v2` and `authenticate_release_registry_v1` (same lines; `registry_program` passed by
value). Same checks in the same order, same error values. The 10 line-break errors are gone (run E). ELF
00c45eda2326e3b4d4108e8a58969d3434fb5f293296c00ff16ef3cacd1610eb; compute -7 / -7.

## Item M: `TABLE_A`, `TABLE_B` (done: emission flag)

`fv_x1b_recdepth.sh`: the emitted definitions alone under `maxRecDepth` 2048 fail ("maximum recursion depth"), under
4096, 8192 and 16384 elaborate (TABLE_A 17 s, peak 3.05 GB; TABLE_B 27 s at 4096, peak 3.13 GB). Emission flag:
`-max-recdepth 4096` (Aeneas writes `set_option maxRecDepth 4096` in the header). Runs E and G use it; both tables
elaborate there. No source change.

`COPY_PATTERNS` (privacy lead's question): not in the on-chain emission (no occurrence in the raw `Funs.lean` of runs
rw2b, C, E): the on-chain path uses the windowed pattern form (`pattern_values_windowed`), not the function that reads
`COPY_PATTERNS`. The constants module contributes only `COPY_LINKS` (an `Array.make 136` of structure literals), which
elaborates; the whole `Funs` module elaborates in 1:04.6 with peak 3.43 GB (run E). No rewrite candidate is needed on
chain; none is proposed.

## Item E: `deployment_ids` (done)

Reproducer crate `W/x1b/probe/crate-e` (source in `x1b-gates/probe-crates/e`; e5 and e6 include `common.rs`):
e0 frozen: `program_id` "Early returns inside of loops", `deployment_id` "Internal error" (the formatted const panic
`panic!("{}", error)`); e1 (error-code loop): `base58_digit` and `program_id` "Unreachable" (a slice index inside a
`while` condition with `&&`); e5 (`break` loops): `base58_digit` still "Unreachable"; e6 (digit by ASCII range, flag
loops, fixed panic text): every function translates, native compile 0 errors. Applied e6. Same result for every input
(test `x1b_decoder_rewrite`: digit table for all 256 bytes against the alphabet search; the three deployment ids, all
strings of one and two characters over the alphabet plus invalid characters, edge lengths and 20,000 random strings
against the frozen decoder: passed). Only the compile-time panic text changes (to a fixed message): a build-time
diagnostic, not program behaviour. The ELF is unchanged by E (K and E both fdca11fe...): the decoder runs at compile
time only.

Emitted form of the statics (run E): `AUDIT_POOL_PROGRAM := deployment_ids.deployment_id (some (toStr
"4hxEyoU8MC3oFMya8D8MAcvhCPhLfHKDP1Ji9byYycn1")) (Array.repeat 32 65#u8)` and `AUDIT_REGISTRY_PROGRAM := deployment_id
(some (toStr "9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q")) (Array.repeat 32 68#u8)`: definitions that compute the
value, not literals; no form was found in which Charon emits the evaluated bytes for a static of the local crate (a
`const` item referenced by the static, variant e4, is emitted as the same call). The values are the base58 decodings of
those strings (the Pool and registry ids of the devnet build); computing them in Lean is not done here.

## Item G: std externals (table done; error-log rewrite done)

`std-external-callers.tsv`: every std external of the final emission's template with each Aspis caller (LLBC edge
rule, `fv_x1b_callers.py`), file and line; the first rows are the named sites below. Classes left: array equality
(`eq` 24 call sites, `ne` 72; slice/array comparisons), `Option` `branch` (7), `array::map` (11), `Iterator::any` (1,
`merkle_verdict`), array `into_iter`/`next` (`r0_transcript` `scan`), `Ref` deref (2, `snapshot`), `black_box` (2,
the deployment-id reads), `first` (2), `starts_with`, `from_utf8`, `as_bytes`, `copied`, `unwrap_or_else`,
`Range::clone`, `Result::clone`, `Vec::into_boxed_slice`, `Vec::try_reserve_exact` (`heap::filled`).

Named sites:
- `Rev<I>::fold`: in X1's emission two callers, `verifier::polynomial` (`(0..7).rev()`, a range, no reference) and
  `reconstruct_10` (`view[..9].iter().rev()`, shared references). Neither is a mutable iterator. Both rewritten in K; no
  `Rev` remains in the final emission. Reversed-mutable-iterator check: no Aspis function of the final emission calls
  both a reversing adapter and a mutable slice iterator (gate `fv_x1b_mutiter.py`, it lists no function of runs E and G; on the planted crate it lists `rev_write` and `rev_write_slice` and not the forward control).
- `alloc::fmt::format` and `String` deref: one site, `error` in `programs/r1-cost-probe/src/lib.rs` 55,
  `msg!("r1:error:{:?}", e)`, called only through `.map_err(error)` on a verifier error, after which the instruction
  returns `InvalidInstructionData`: error/log path only, never on a path that ends in acceptance. Rewrite (G):
  `msg!(error_log(e))` with `error_log` a match to the eight literal strings `"r1:error:Parse"` .. `"r1:error:Allocation"`
  (the derived `Debug` of each unit variant); the logged text is unchanged (test `x1b_error_log`). ELF after G 33d66a28424051e56a2d33dadc5f29c717abbc5ff81e6023ada1987dd9d628ea (two-transaction 2678151e9b84855fd19e9fff7a9eecaa033c257b3941b8e9c34824a2bebcf5c3); compute -2 / -2; `alloc.fmt.format`, `String` deref and `must_use` are gone from the template (run G).
- `alloc::rc::Rc`: enters through the SDK type `solana_account_info::AccountInfo` (`lamports: Rc<RefCell<&mut u64>>`,
  `data: Rc<RefCell<&mut [u8]>>`, `Types.lean` 2109-2117); no Aspis function names `Rc`.

## Item H: target_os (done)

`target-os.tsv`: every `cfg(... target_os ...)` site of the four crates (78 rows: 72 host-only, 6 SBF-only), the gated
item, and whether it occurs in the final emission (a host build). Reached from the entry: only
`SolanaDigest::digest_into` (`programs/r1-cost-probe/src/lib.rs` 21-29), whose host branch is in the emission. Not
reached: the SBF-only allocator (lib.rs 32), the heap high-water logs (lib.rs 99, 172; inside `not(pool-adapter)`
code), the two `compile_error!` guards; the host-only sites are equality-trace hooks under the reference features
(off in the deployed build), `pub use` re-exports, host-side helpers and one manifest dependency table; `pool_v1` (lib.rs
40) is under `any(not(target_os = "solana"), feature = "pool-v1-kernel")` and the deployed build has `pool-v1-kernel`, so
it is in both builds.

Boundary-class item `SolanaDigest::digest_into` (owner decision: kept as it is, not changed):

    // Solana target (lib.rs 21-25), 3 statement lines:
    #[cfg(target_os = "solana")]
    #[allow(deprecated)]
    unsafe {
        solana_program::syscalls::sol_sha256(parts as *const _ as *const u8, parts.len() as u64, out.as_mut_ptr());
    }
    // host (lib.rs 26-29), 1 statement line:
    #[cfg(not(target_os = "solana"))]
    {
        *out = hashv(parts).to_bytes();
    }

Contract: after the call `out` holds SHA-256 of the concatenation of `parts`; nothing else changes. Realisations:
the `sol_sha256` syscall on Solana; `solana_sha256_hasher::hashv` on the host (the emitted branch: `hashv` and
`Hash::to_bytes` are SDK externals in the template). Grammar check (my own reading; the Pool worker's checker is not
committed): one runtime call whose arguments are the function's parameters (`parts`, `parts.len()`, `out`'s pointer),
no logic. The extension the grammar needs: a syscall taking raw pointers in place of an SDK borrow; the other rules
(one call, arguments from parameters only, no branch, no loop, no arithmetic) hold unchanged.

## Fault checks

- (d) Can this Charon read dependency crates from built MIR? No: `charon cargo --help`: "`--mir` ... This is only
  relevant for the current crate; for dependencies only MIR optimized is available". The three library crates are read
  from optimized MIR in this whole-program run, as X1 recorded. The only way to get built MIR for a library crate with
  this Charon is to make it the current crate (the per-crate freeze emission did that).
- (e) `compare-frza-diffs.txt` (`fv_x1b_frzadiff.py`): the unified body diff of all 51 rows of X1's `compare-frza.tsv`
  that are not identical: 42 "local bindings only", 4 "constant evaluated", 5 "called functions differ". Reading: the
  differences are hoisted or inlined constants (`QM31.ZERO` bound by `←` on one side and used directly on the other),
  evaluated constants, renamed temporaries, the std `ChunksExactMut` impl (more methods listed in X1), the loop helper
  name of `array_from_fn_copy`, and `heap::filled`'s `Global`. Counted mechanically, every write operation
  (`index_mut_back`, `Array.update`, `Slice.update`) present in one body is present in the other (two in
  `one_tx::coefficients` loop body, one in `equality_tables`); no body loses a write. This is a reading, not a proof.
- Writes in rewritten functions, read in the emitted Lean (run E): `expand_values` yes (above); `close_checkpoint`
  performs no write itself, its three writes are the boundary calls (above); `Selectors::expand` writes a local array
  and returns it: yes: the inner loop body (run G raw `Funs.lean` near 22279) updates `weights` at `2 * index1` and `2 * index1 + 1` with `Array.update` and returns the array; the outer loop and `expand` return it. No other rewritten function writes through `&mut`.
- Planted positives for the shared gates (privacy lead's tools, `W/x1b/gates/`, read only copies): 
  - `inventory_text.py`: on X1's off2 it reports exactly the five named gaps (CM31::inv, M31::inv, deployment_id,
    close_checkpoint, lifecycle_accounts) among Aspis items: fires. On run G: exactly the two write boundaries. My
    `fv_x1b_aspis_axioms.py` gives the same lists.
  - `mutiter_calls.py`: does not run on this Charon's LLBC (`c2_graph.py`: KeyError 'data' at `item_meta.span`; the spans
    are wrapped in `Untagged` and hash-consed as `{Value: [id, v]}`, calls as `Regular: {kind: {Fun: id}}`). Replaced by
    `fv_x1b_mutiter.py` (same families over `fv_x1b_llbc.py`): fires on the planted crate (`rev_write`,
    `rev_write_slice`), not on `fwd_write`; lists nothing in run G.
  - Fault 1 with this exact tool pair (control crate `W/x1b/probe/crate-m`, run `probe-m`, Aeneas without abort): the
    emitted loop body of `rev_write` (`for (i, x) in a.iter_mut().rev().enumerate() { *x = i as u32 }`) contains no
    write: the `some _` branch only continues with the iterator; the element's backward function is discarded. The
    write is dropped. (The forward control `fwd_write` fails the native compile on the `IterMut` instance, so it is not
    a clean comparison; the dropped write is read from the emitted text.) The source search finds no
    `iter_mut().rev()` in the final emission's code (only X1's `sampler.rs` comments/tests and `r0_transcript.rs:129`,
    not emitted).
  - `p2_bodycmp.py`: on runs E and G, which differ in one function (`error`, item G), it reports 1360 same, 1 differs, 2
    and 1 present on one side only (`error_log` added; the formatting instances gone): fires. On C against G: 40 differ.
  - Write-route check (`fv_x1b_writecalls.py`, my fourth check): fires on rw2b and run C (the three lifecycle handlers
    call `try_borrow_mut_data` and `RefMut::deref_mut`); no call in runs E and G.

## Final state

- Native-library errors: 0 (raw output, zero edits).
- Aspis functions opaque: `r1_pool_adapter::write_zero_data`, `r1_pool_adapter::write_lamports` (account write
  boundaries, opaque by flag). No Aspis function fails to translate, none is an axiom by failure, no `sorry`.
- Externals left by class: SDK and runtime 18 (AccountInfo borrows and lamports read, Clock, create_program_address,
  create_with_seed, Pubkey operations, set_return_data, sol_log, hashv, bpf_loader id, ProgramError clone/From);
  std 29 (`std-external-callers.tsv`).
- Boundary-class items: the two write boundaries (10 lines) and `SolanaDigest::digest_into` (item H).
- Compute: +1,234 CU per recorded payment against the frozen program, from F (`expand_values`, the only rewrite that
  trades compute).
- Not done: `merkle_verdict` and the eleven `array::map` sites stay as std externals (K); the Pool worker's
  write-boundary grammar checker was not available to run.

## Not checked

- The F alternative beyond `rw-F2`; any shape of `expand_values` with no added check.
- Differential tests for `wide_view`, `relation_view`, `final_rounds`, the second `decode_k`, `composition_parts`,
  `state_only_selected_mask_value`, `evaluate_state_only_poseidon_oracle_projected`, `scalar_factor`, `parse_shape`,
  `parse_packed_shape`, `decode_lane_from_pool_release`, `is_close_checkpoint`, `authenticate_invariant_release_registry`
  (covered only by the existing crate tests and the recorded-payment replays).
- Instruction-level comparison of the ELFs is by `llvm-objdump` function counts (below); no per-instruction proof of
  equal behaviour.

## Rerun

Copy `../host/fv_x1b_*` to `W/x1b/bin` (and X1's `fv_x1_rules.json` is referenced by path, unused with `lean: false`).
Tree: copy X1's `W/x1/rw3` (or `W/src-frz-a` plus X1's patches A and B2) and apply `rewrites2/*.patch` with `patch -p1`.
Emission, native compile and gates: `bash fv_slot.sh X1b-<name> 5400 bash x1b/bin/fv_x1b_job.sh <label> x1b/bin/fv_x1b_cfg_G.json`
(set `source` to the tree). Tests: `fv_x1b_test.sh <tree> program program2 verifier statement core`. Build and replay:
`fv_x1b_build.sh <tree> <n> both`, `fv_x1b_replay.sh <n> W/out/X1b-<n>/artifacts/aspis_r1_cost_probe_program.so`.

