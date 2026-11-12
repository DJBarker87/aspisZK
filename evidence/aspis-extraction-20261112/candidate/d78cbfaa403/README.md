# Aspis candidate d78cbfaa403: scripted clean-emission check of both on-chain programs (task X7)

Status: a tool record, paused by the owner. Nothing here is proved or established. A translated, elaborated
function is not a verified function. Target not yet established.

Candidate: `aspis-next` d78cbfaa4037634d91013f884ac89d2e6a718d4a. Host tree `W/src-x7-1` (`W` =
`~/project-offloads/future-version-20261111`), made with `fv_frz_tree.sh`; archive sha256
478770ba3f3400cd58fdb48a12adacf539c2c96775c395d7bf5b0fde3ad894d7 (the local `git archive` has the same hash), files
sha256 d51cbdbc78fe4929bce8fd65a8280f6d460743ce01dc8c8ff9c5dd48b31fbbb1, 1874 files. A second commit,
4dceeaab48e4adca2fef84970ca7842961507a37 (d78cbfaa403 plus the Pool follow-up in `pair_forest.rs`), ran through the
same driver with no edit: tree `W/src-x7-2`, archive sha256
ec976ec063949743a980bc24341c6cc75cafa6aca8a57260c7bcab85883218d0, files sha256
99fcad5e9d9398720e49f5809f321ac34a38d52837aa5398ead6b6daa190caf0.

The run outputs are on the host under `W/x7/runs/<label>/`, labels `d78cbfaa403`, `4dceeaab48e` and
`frz-3d700effcabe` (SBF builds of the frozen tree). They hold the tables (`<program>/rows.tsv`, `externals.tsv`),
`MANIFEST.json`, `constants.json`, `shared.tsv`, the gate outputs (`gates/`), the stack comparison and the receipts.
None of them was copied to this directory before the pause. The emitted Lean stays on the host, and its sha256 values
are in each run's `MANIFEST.json`. The figures below are copied from command output read during the run.

## Driver

`../../host/fv_emit_candidate.sh <tree> <label> [--ref <label>] [--sbf-only] [--no-sbf] [--post <n>]` is the
driver. It runs one `fv_slot.sh` scope at a time: `X7-<label>-emit` (`fv_emit_job.sh`), then `X7-<label>-sbf`
(`fv_emit_sbf.sh`), then `X7-<label>-post<n>` for a rerun of the gates. Its helpers are all named `fv_emit_*` in
`../../host/`. The two program configurations are `fv_emit_cfg_verifier.json` and `fv_emit_cfg_pool.json`. They
carry X1b's run-G flags (`-max-recdepth 4096`, two write boundaries opaque) and X2c's run-c9 flags (the boundary,
`runtime_stack_height_v1` and `solana_rent::Rent` opaque), with the deployed features and overflow checks off.

The SBF builds copy the lead's `fv_frz_build.sh` and `fv_pool_build.sh` recipes. Only the output and cargo target
directories change, to new directories under `W/x7` that are deleted after each build. The reason is that
`W/target/sbf-pool-src-frz-a` already holds a finished build, so reusing it would print no compiler message.

## Results on d78cbfaa403

Emission scope `X7-d78cbfaa403-emit`: exit 1, caused only by the driver's own final grep. That defect is fixed and
the later post phases exit 0. Wall 16:44.06, peak RSS 3,484,716 kB, cgroup peak 3,076,206,592 B, no memory event.

| | verifier program | Pool |
|---|---|---|
| Charon | exit 0, 1:39.14, LLBC 65ca132d3ad22320758a0e2b67151c2b42532333439524619d1bdb5045626abe, 1316 functions | exit 0, 1:29.49, LLBC afca33a5926ed5bdef4bc246fbb0f7623ad7e04049435b07dc302a39ef31041a, 969 functions |
| Aeneas `-abort-on-error` | exit 0, 4:16.73, peak 2,657,548 kB, 0 `[Error]` lines | exit 0, 4:49.07, peak 2,412,544 kB |
| raw output against the native library, zero edits | 0 errors in all four modules (Funs 1:54.92, 3,484,716 kB) | 0 errors in all four modules (Funs 0:29.62) |
| bodiless Aspis declarations | `r1_pool_adapter.write_zero_data`, `r1_pool_adapter.write_lamports` | `account_write.write_account_data_v1`, `processor.runtime_stack_height_v1` |
| rows (bodiless) / not elaborating | 1355 (2) / 0 | 766 (2) / 0 |
| externals | 50 | 69 |
| against the worker's own final emission | identical to X1b run G in all 1635 declarations | differs from X2c run c9 in one declaration, `aspis_statement.atomic_statement.decode_digest_canonical` (merged in the verifier worker's form); 1006 identical |

Gates. The last completed post phase is post 4. Every gate line printed pass:

- (i) bodiless: pass for both programs. Counts: verifier aspis 2, sdk 18, std 30; Pool aspis 2, sdk 41, std 26. No
  `sorry`.
- (ii) completeness: pass for both programs, 0 FAILURE rows. Every function not emitted is drop glue, a derived
  impl, or not in Charon's ordered declarations (31 in `aspis_core` for the verifier: the `r0::scalar` macro impls,
  `pow`, `neg`, two `wide_exact` items).
- (iii) `fv_x1b_mutiter.py`: it fires on X1b's planted crate (`rev_write`, `rev_write_slice`) and lists none in either
  LLBC.
- (iv) `fv_x1b_writecalls.py`: it fires on X1's rw2b (the three lifecycle handlers) and lists no call in either LLBC.
  The cfg-aware source search finds only the boundary sites, and the two sides agree.
- (v) read before write and write order: pass. The verifier's `close_checkpoint` calls `write_zero_data`, then
  `write_lamports ai 0`, then `write_lamports ai1 total`, the same order as X1b run G. One flag in
  `r1_pool_adapter.process` was examined in the emitted body: tag 7 leads to `close_checkpoint` and the default arm to
  `stage2`, which are exclusive. The Pool sequences equal X2c's c9 sequences, and its two flags are X2c's examined
  ones.
- (vi) grammar: X2c's planted cases behave as before. Eight new form-H negatives fail and the positive passes. The
  boundary modules and `digest_into` pass. Form H is a separate fourth form in `fv_emit_boundary_check.py`, and X2c's
  checker is imported unchanged.
- (vii) target_os: pass, 84 sites. Reached difference sites are only `digest_into` (both branches) and
  `runtime_stack_height_v1` (both branches). SBF-only items are the allocator and two `use` imports.
- (viii) X2d's branch- and call-following read-after-write check: the planted positives are reported (6 of 6) and the
  negatives pass (3 of 3). The Pool's four handlers and `process_instruction` pass, and the verifier's
  `close_checkpoint` passes.
- Shared functions: 272 `aspis_statement` / `aspis_core` declarations occur in both emissions, and all 272 are
  identical after normalisation.
- Constants, from builds: `AUDIT_POOL_PROGRAM` 3710c11e1e66920cf6a12837d1b2394cd43a05fde46a4d91b85b375af040fa4e and
  `AUDIT_REGISTRY_PROGRAM` 8309a3c9992d23debd688be0b9604887e2586a440a9c3c48521c3531e392e8ab. These were evaluated by
  rustc from the tree's `deployment_ids.rs` and agree with a Python base58 decoding. `bpf_loader_upgradeable`
  02a8f6914e88a1b0e210153ef763ae2b00c2b93d16c124d2c0537a1004800000, and the other loader ids, came from a build of
  solana-sdk-ids 2.2.1. They agree with the decoded `declare_id!` strings.
- SBF stack offsets: the frozen tree and the candidate print the same messages in the same functions with the same
  offsets, 34 in the verifier program and 28 in the Pool. By name, none of these functions is in the program's LLBC.
  Verifier ELFs: the frozen tree gives 827aaec1cbd92e37767d3d76b9fc6174ef2851a498e2e7935e1b55bc68ccb12b, which
  reproduces the frozen measurement ELF. The candidate gives
  33d66a28424051e56a2d33dadc5f29c717abbc5ff81e6023ada1987dd9d628ea, the same as X1b's ELF after G.

## Results on 4dceeaab48e (driver unchanged)

Emission scope `X7-4dceeaab48e-emit`: wall 18:31.53, cgroup peak 3,048,189,952 B. Charon and Aeneas exit 0 for both
programs. The native compile gives 0 errors in all modules of both programs. Gates (i), (ii), (iii), (iv), (vi), (vii)
and (viii) pass, and the verifier's (v) passes. The stack offsets are the same as the frozen tree's (34 and 28). The
verifier emission is identical to X1b run G.

**The Pool's gate (v) FAILS.** Its order check compares the argument text of each boundary call with X2c's c9
emission. The follow-up restructures the page writes into a new `write_root_page_v1`, adds four helpers and
`RootPageWriteV1`, and renames locals. As a result, `write_deposit_accounts_v1`, `write_terminal_accounts_v1` and the
checkpoint handler no longer match the reference text, and `write_terminal_page_v1` is gone. The gate's
read-before-write part has only the two examined flags. Gate (viii) passes on this emission. The write order of
4dceeaab48e against the frozen handlers is therefore not checked by this driver. Its reference sequences need a new
reference, the follow-up's own emission. The gate was not loosened.

## Finding about the shared LLBC reader

Charon 454586e9 hash-conses each kind of value in its own table: types, spans, constants, clauses and layouts. The
tables use overlapping ids. X1b's `fv_x1b_llbc.py` merges them into one table, so a `Deduplicated` id can resolve to a
value of another kind. That reader is used by `fv_x1b_mutiter.py`, `fv_x1b_writecalls.py`, `fv_emit_tables.py` (call
spans) and `fv_emit_complete.py` (item spans). Their results above were not rechecked against a context-aware reader.
`fv_emit_gate_types.py` resolves ids by context instead.

## Paused (owner, 12 November)

Phases completed:

- d78cbfaa403: emission, native compile, gates (i) to (viii), tables, shared comparison, constants, manifest, SBF
  builds and stack comparison (post phase 4 is the last completed one). All gates pass.
- 4dceeaab48e: the same phases, with the Pool's gate (v) failing as described above.
- Frozen tree: SBF builds only.

State of the two type-based gates:

- (iii') `fv_emit_gate_types.py iter` and (iv') `fv_emit_gate_types.py state` are written.
- Both were tested locally on the privacy lead's control2 LLBC (`fv_emit_plant/ctl2-whole.llbc`, from
  `ctl2-out/whole`). (iii') fires on the direct `iter_mut().rev()`, on `into_iter().rev()`, on the helper-returned
  `IterMut`, and on the split shape (at `helper_rev`). It does not fire on the forward walk, `next_back`,
  `rchunks_mut` or the cell functions. `next_back` and `rchunks_mut` are listed as information.
- (iv') fires on `Cell::set`, `RefCell::replace` and `borrow_mut`/`deref_mut`, and on nothing else in the control.
- They are wired into `fv_emit_job.sh` (steps `g3t`, `g4t`). The planted crate `fv_emit_plant/` and its runner
  `fv_emit_plant.sh` (crate form, dependency form, control2) have not run with the type gates.
- Neither type gate has run on either program's LLBC. A post phase that would run them (`X7-d78cbfaa403-post5`, then
  `X7-4dceeaab48e-post1`) was launched just before the pause. Whether it started is unknown, because the ssh session
  dropped. If it ran, its outputs are in `W/x7/runs/<label>/gates/iii-t-*.txt`, `iv-t-*.txt` and `plant-table.txt`.

Jobs that may remain on the host: the chain logged in `W/x7/runs/chain5.log`, with attempts `X7-d78cbfaa403-post5`
and `X7-4dceeaab48e-post1`. It writes `W/x7/runs/chain5.done` when it finishes. No other X7 job is running.

What to run next:

1. Read `W/x7/runs/chain5.log` and `W/x7/runs/*/gates.txt`. If chain5 did not run, run
   `bash W/x7/bin/fv_emit_candidate.sh src-x7-1 d78cbfaa403 --post 5 --ref frz-3d700effcabe`, then the same command
   for `src-x7-2 4dceeaab48e --post 1`.
2. Report gate (iii') and (iv') for both programs, and `gates/plant-table.txt`. That table shows which scan fires on
   each planted shape in each form.
3. Copy the run outputs (tables, gates, `MANIFEST.json`, `constants.json`, `shared.tsv`, `stack-compare.tsv`, steps,
   receipts) into this directory and into `../4dceeaab48e/`.
4. Give the Pool's gate (v) a reference that matches the follow-up. Run the emission order check against X2d's emission
   (`pool/followup/runs/pool-2`), then compare by hand with the frozen order in `write-boundary.md`.
5. Recheck the `fv_x1b_llbc.py` users with a context-aware hash-cons reader.

To rerun everything on another commit: make the tree with `git archive <commit> crates programs tools Cargo.toml
Cargo.lock | ssh host 'bash W/fv_frz_tree.sh <tree> <commit>'`, then run
`bash W/x7/bin/fv_emit_candidate.sh <tree> <label> --ref frz-3d700effcabe`.

## Not checked

- The fidelity run of PIN-RULES section 3, which needs recorded payments executed through the emitted definitions.
- The stack-offset reachability is checked by name only.
- Reads in (v) and (viii) are textual or emitted-Lean analyses, not proofs.
- The type gates on the programs. They were not run before the pause.
