# Worst-case CU upper bound for the R1 two-transaction path (2026-10-19)

Pre-registration followed: `design/PREREG-CU-UPPER-BOUND-20261019.md` (method
steps 1-5, PASS/FAIL/INCOMPLETE, labels). Criteria unchanged.

Labels used throughout: **[measured]** = a LiteSVM replay CU of a concrete
transaction; **[analytical]** = derived from source/ELF and the Agave cost
schedule; **[swept]** = maximum over the randomised step-5 sweep.

## Verdict

**FAIL.** B_stage1 = 1,357,041 (transfer) / 1,358,920 (withdrawal);
B_settlement = 6,204,876 (transfer) / 6,986,751 (withdrawal) [analytical
bound = max saved-fixture CU + sum of site maxima, method step 3]. Both
exceed 1,300,000 for both kinds. Every site has a code-cited cap, so the
result is not INCOMPLETE; steps 1-5 were run. No sweep value exceeds its
bound (step 5). Swept maxima: stage 1 1,239,161 / 1,237,878; settlement
1,231,724 / 1,245,323 (the latter two from targeted bump-search inputs;
random-only maxima 1,192,252 / 1,206,877) [swept].

Dominant sites:
1. **Pool PDA bump searches (settlement).** The Pool calls
   `sol_try_find_program_address` 11-12 times per transfer settlement and
   13-14 times per withdrawal [measured, traces]. Agave charges 1,500 CU per
   attempt and allows 255 attempts, so each call can cost up to 381,000 CU
   more than the one-attempt path (S-BUMP). Seeds include the spent
   nullifier (marker PDA, derived twice), the page number and the
   checkpoint sequence, so the attempt counts vary per transaction. A
   ground nullifier needing 19 attempts at the marker (derived twice: 2 x 18
   x 1,500 = 54,000 CU analytical) gave settlements 46-60k above the
   ungrounded p255 runs [measured, `target-*-marker12/16`; the baseline
   seeds differ]. Without this site, B_settlement is
   still 1,632,876 / 1,652,751, because of the Pool page-mode branches and
   loops (zero scan and write of an 8,256-byte page; 245-250k across R1
   and R3) and the bit-dependent lane loops (163k).
2. **Stage-1 split `[3,11]` (stage 1).** 40,536 / 40,673 CU [swept range].
   All saved fixtures used `[3,10]`; `[3,11]` is admitted and runs 11
   queries in stage 1 (swept stage 1 up to 1,239,161).
3. **Value-dependent field-reduction branches (both transactions).** About
   54k CU of R1 slack in stage 1 and 36k in stage 2; 79% of it is
   one-instruction `x >= P` canonical-reduction branches. A further 50-53k
   (stage 1) of one-sided R3 branches is included conservatively.

Stage 1 fails even on the narrowest reading: without the conservative R3
class, B_stage1 is 1,306,717 (transfer).

## 0. Target pin

Source: research `bee5825f0` (this branch's base), shipped to the build host
as a `git archive` of the Rust workspace and `tools/r1-cost-probe`.
Toolchain: `cargo-build-sbf` 3.1.13, platform-tools v1.52 (as all prior R1
CU receipts). Rebuilt on the host from `bee5825f0` [measured, receipts in
`receipts/`]:

| Artifact | Features | SHA-256 | Note |
|---|---|---|---|
| verifier (deployed) | `pool-adapter,private-leaf-salts` | `a70f30bd...cfea01a` | identical to the cu-savings final ELF |
| verifier (linked, symbols) | same | `a8789ded...0344125` | identical to candidate14 `linked.elf` |
| verifier with `cu-profiling` | `+cu-profiling` | `40d544ee...91330f` | step 4 only |
| Pool (deployed) | `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit` | `b33302fd...2975e5` | identical to the `pool-asq8-nodirect` ELF of every saved fixture |
| Pool (linked) | same | `e394d02b...0237ea6` | audit input |
| registry | (pinned, not rebuilt) | `7ad46f0d...67d01ab` | from `active-mask-basis .../aux-current` |

So the measured fixtures, the merged research source and the analysed ELFs
are the same bytes. The Pool source of the fixture ELF
(`active-mask-basis-sbf-20261017/candidate/programs/aspis-pool/src`) is
byte-identical to research `programs/aspis-pool/src`; `aspis-core` is
identical; `aspis-statement` differs only in host-side trace writers.
No ELF/.so/binary is committed; SHA-256 and size only.

## 1. Settle-early questions (a) (b) (c)

All citations are to research `bee5825f0` unless a host path is named.

**(a) Rollover pair count.** "Pairs" is the selected output lane's
`next_leaf_index` before the spend (the fixtures' `--pairs` populates that
many leaves). A rollover happens when `next_leaf_index + 1` starts a new
256-root history page (`root_history.rs:16-17,61-64`, capacity 2^8). The cap
of 1023 is a **driver** limit only (`tools/r1-cost-probe/src/bin/pool_gate.rs:319`,
`ensure!(pairs <= 1023)`). The programs admit any
`next_leaf_index < POOL_V1_PAIR_CAPACITY = 2^20` (`format.rs:28`,
`pair_tree_profile.rs:33-35`; Pool `pair_forest.rs:1036` rejects
`>= CAPACITY` with `TreeFull`; the verifier adapter rejects
`> CAPACITY` at `r1_pool_adapter.rs` `decode_lane_from_pool_release`). The
largest admitted rollover position is therefore **1,048,575** (`2^20-1`,
page 4095 -> 4096), not 1023. CU is **not monotone** in pairs in the saved
fixtures [measured, cu-savings FINAL-RESULT]: settlement 13 < 1023 < 255
for both kinds (transfer 1,137,397 / 1,171,579 / 1,174,671). The position
enters through bit-dependent work (frontier empty-root comparisons on zero
bits, page mode Genesis/SamePage/Rollover, page-number seeds of PDA
derivations), so the cap must be measured directly (section 6).

**(b) Verifier-side challenge samplers and parsers.**
- Query sampler: `aspis-core/src/r0_transcript.rs:305-318` always hashes
  eight squeeze/advance pairs (16 fixed sha256 calls,
  `transcript.rs` `queries`), then scans at most `QUERY_MAX_DRAWS = 64`
  words (`r0_transcript.rs:48`, check at `:204`), each draw doing a
  `contains` over at most `QUERY_COUNT = 22` accepted values. Data-dependent
  but capped: draws 22..64.
- Field samplers (`aspis-r1-cost-probe/src/sampler.rs`): fixed eight/four
  long divisions; one data-dependent branch (`gamma_sample` `wrapped`,
  `add_small_base_p` at most twice). No retry.
- Circle OOD points (`r0_transcript.rs` `circle_sample`, used via
  `r1_wire` `circle_validated`): one fallback branch, no retry
  (`transcript.rs:286-296`).
- Parsers (`verifier.rs` `View::parse_shape/parse`, `r1_wire.rs`
  `Prefix::parse`, `aspis-statement` decoders): every record and the proof
  have fixed lengths (`verifier.rs:31-38` proof length equality,
  `r1_wire.rs:65-83` record length equality); loops have constant trip
  counts; error branches only reject.
- Stage-1 split: the admitted stage-1 data are `[3,10]` and `[3,11]`
  (`pool_route.rs:4`). `k` queries run in stage 1 and `22-k` in stage 2
  (`verifier.rs` `tx1_finish`, `tx2_authenticated`; the checkpoint carries
  `a.next=k`, `resume` accepts `bytes[9] <= 22`). **All six saved fixtures
  used `[3,10]`**; `[3,11]` moves one query from settlement into stage 1 and
  is a data-dependent site of its own (section 2, S-SPLIT).
- **Pool bump searches (data-dependent retry loop).** The Pool settlement
  path derives PDAs with `Pubkey::find_program_address`
  (`aspis-pool/src/nullifier.rs:32` nullifier marker from the spent
  nullifier; `history.rs:38` root page from the page number;
  `pair_forest.rs:208,222,233` master/lane/checkpoint). Each call is the
  `sol_try_find_program_address` syscall, which charges
  `create_program_address_units = 1500` once and again for every failed
  bump, up to `u8::MAX = 255` attempts (`solana-syscalls-4.2.1/src/lib.rs:893-929`,
  `for _ in 0..u8::MAX`). An accepted call needs a bump, so the extra cost
  over the one-attempt path is at most `254 * 1500 = 381,000` CU per call.
  The cap is code-cited (Agave), so this is not INCOMPLETE, but it is
  larger than the whole 1.3M headroom. The verifier adapter, by contrast,
  uses `create_program_address` with stored bumps only
  (`r1_pool_adapter.rs` `authenticate_*`, "neither search for a bump").

**(c) Variable-length syscalls; Agave cost schedule.** LiteSVM 0.16.0 with
`solana-program-runtime =4.2.1` (`tools/r1-cost-probe/Cargo.toml`), i.e.
Agave 4.2.1. Constants (`solana-program-runtime-4.2.1/src/execution_budget.rs:200-225`):
`sha256_base_cost 85`, `sha256_byte_cost 1`, `mem_op_base_cost 10`,
`create_program_address_units 1500`, `invoke_units 946`,
`cpi_bytes_per_unit 250`, `syscall_base_cost 100`, `sysvar_base_cost 100`,
`log_64_units 100`, `heap_cost 8`. sha256 per call:
`85 + sum_slices max(10, floor(len/2))`
(`solana-syscalls-4.2.1/src/lib.rs:2553-2596`). Every sha256 call site in
the verifier hashes slices whose lengths are compile-time constants (fixed
record/proof layout, fixed checkpoint length, 32-byte digests, fixed
domain tags); no input-dependent length reaches a syscall (section 2 lists
each site with its constant cost). CPI charges depend on instruction-data
and account-data lengths (`cpi.rs:358-362,930-938,1014-1019,1050-1057`);
every account passed on the measured path has a length pinned by an
equality check (proof buffer `scan_proof_buffer`, checkpoint
`require_verifier_checkpoint`, lane/page/master/checkpoint decoders,
registry decoders), so CPI byte charges are constant.

## 2. Site enumeration and maxima (method steps 1-2)

All sites with source location, ELF location, maximum extra CU, maximum
count and cap citation are listed in `sites.json`. Per-kind values come
from `bound.json` [analytical; ELF classes use traced counts].

| Site | Tx | Transfer max extra | Withdrawal max extra | Count cap (citation) |
|---|---|---:|---:|---|
| S-SPLIT `[3,11]` | stage 1 | 40,536 | 40,673 | k in {10,11}, `pool_route.rs:4` |
| ELF-R1 value branches | stage 1 | 53,821 | 53,774 | per-site traced count (fixed by code; split at 11) |
| ELF-R3 one-sided branches | stage 1 | 50,324 | 53,438 | traced count |
| LOOP lane-position loops | stage 1 | 333 | 309 | <= 20 = `POOL_V1_PAIR_TREE_DEPTH` (`format.rs:28`) |
| S-QSCAN duplicate draws | stage 1 | 8,400 | 8,400 | 42 extra draws, `QUERY_MAX_DRAWS=64` (`r0_transcript.rs:48`) |
| S-CIRCLE fallback | stage 1 | 3,940 | 3,940 | 2 rows; 1,970 instr each (traced inclusive cost) |
| ELF-R1 value branches | settlement (verifier) | 36,118 | 36,114 | traced count |
| ELF-R3 one-sided branches | settlement (verifier) | 9,336 | 9,457 | traced count |
| ELF-R1 Pool (page mode) | settlement (Pool) | 104,841 | 105,696 | page modes Genesis/SamePage/Rollover |
| ELF-R3 Pool | settlement (Pool) | 139,652 | 144,680 | traced count |
| LOOP Pool page/fill/bits | settlement (Pool) | 163,258 | 163,308 | <= 256 roots (`root_history.rs:16-17`), <= 20 bits |
| S-MARKER-PREFUNDED | settlement | 5,000 | 5,000 | <= 2 extra System CPIs |
| S-BUMP find_program_address | settlement | 4,572,000 (12 x 381,000) | 5,334,000 (14 x 381,000) | 255 attempts, `solana-syscalls-4.2.1/src/lib.rs:893-929` |

Constant sites (no extra): sha256/memcpy/memset/memcmp lengths (fixed
layouts; traced counts constant per kind and split), seven verifier
`create_program_address` calls (flat 1,500 CU each), CPI byte charges
(account lengths pinned by equality checks), and the gamma `wrapped` branch
(inside ELF-R3). The verifier has no bump search.

## 3. ELF control-flow audit (method step 1, ELF part)

**Method.** The linked (unstripped) ELFs have byte-identical `.text` to the
deployed ELFs (checked by `harness/sbf_slack.py`). A LiteSVM build with
`litesvm/register-tracing` recorded every executed instruction (pc and
registers) of stage 1, the nested stage-2 verifier and the Pool program for
12 accepted runs: the four saved fixtures transfer/withdrawal 13/255 and
eight seeded runs (pairs 2^20-1 with split 11, pairs 0 with a zeroed genesis
page, pairs 777 split 11, pairs 300000). Traced CU equals untraced CU on
the same inputs [measured]. For every conditional branch executed in any
trace the tool builds the containing function's CFG, finds the immediate
post-dominator, and computes the longest and shortest instruction paths of
each arm to it (calls weighted by the observed inclusive cost of the callee).
Branches are analysed per transaction kind (6 traces each) and classified:

- **R1** both arms taken and the per-site decision sequence differs between
  traces: a value-dependent site; extra = (longest - shortest) x max count.
  Almost all are M31/QM31 canonical-reduction branches (`if x >= P`), which
  SBF lowers to a jump because it has no conditional move.
- **R0** both arms taken but an identical decision sequence in all traces of
  the kind (Vec growth, unrolled index tests): positional, extra 0.
- **R2** one arm never taken and it cannot be longer than the taken arm
  (mostly `?` early returns): extra 0.
- **R3** one arm never taken and possibly longer: kept as a site
  conservatively (covers rare value branches such as the final reduction in
  `reduce_u64`, which random inputs essentially never take).
- **R4 / U1** the untaken arm calls a panic/abort/alloc-failure routine:
  the transaction aborts (rejected, out of scope).
- **U2** untaken Vec-growth arms: every Vec on the path has a compile-time
  length per kind, so growth is positional; never needed in any trace.
- **U3** route/kind dispatch (lifecycle tags, stage1/stage2, the other
  payment kind), **U4** error constructors, **U5** proof-variant branches
  (variant pinned to S2 by `View::parse_shape`): constant for an accepted
  transaction of a given kind and stage.
- **U6** `circle_fallback_point` (never executed): costed as source site
  S-CIRCLE. **U7** prefunded nullifier-marker path (System
  transfer+allocate+assign instead of create): costed as S-MARKER-PREFUNDED.
- **R5** loop branches. Loops whose trip count varies between traces of the
  same split are data-dependent; all are lane-position loops (trailing ones
  or zero bits of `next_leaf_index`, at most 20 by `POOL_V1_PAIR_TREE_DEPTH`;
  Pool page fill, at most 256 by `POOL_V1_ROOT_HISTORY_CAPACITY`; page mode).
  The traces include both extremes (pairs 0 and 2^20-1, fill 0 and 255),
  so each is costed as the max-min instruction range of its functions.

**Coverage.** Every conditional branch executed in the stage-1 and stage-2
verifier traces is classified (no residual). In the Pool, 69 branch sites
inside one `core::ops::FnOnce::call_once` monomorphization call a callee
never executed in any trace and are not classified; that function holds
1.2-3.0% of Pool instructions per trace (0.1-0.3% of settlement CU). Every
other Pool branch is classified. Syscalls are identified through the
deployed ELF's `R_BPF_64_32` relocations: the verifier makes no
`sol_try_find_program_address` call; the Pool makes 11 (same page, genesis)
to 12 (rollover) calls in a transfer and 13-14 in a withdrawal. sha256,
memcpy, memset and memcmp counts are constant per (kind, split), and the
lengths come from fixed layouts.

**Fraction audited.** 100% of the verifier's executed instructions (stage 1
and stage 2, both kinds) lie in functions whose every executed branch is
classified; for the Pool it is at least 97% of its instructions. Measured
syscall CU (sha256, PDA, CPI) is costed from source and the Agave schedule.

## 4. Bound B_tx (method step 3)

B_tx = max saved-fixture CU (the six cu-savings fixtures, reproduced
exactly by this job's controls) + the sum of the site maxima in section 2.

| | Transfer | Withdrawal |
|---|---:|---:|
| fixture max, stage 1 | 1,199,687 | 1,198,386 |
| **B_stage1** | **1,357,041** | **1,358,920** |
| fixture max, settlement | 1,174,671 | 1,188,496 |
| **B_settlement** | **6,204,876** | **6,986,751** |
| B_settlement without S-BUMP (information only) | 1,632,876 | 1,652,751 |

These bounds are conservative. Each site maximum is the extra cost over the
cheapest path times the maximum count, as pre-registered, so part of each
site is already in the measured fixture and is counted twice. A tighter
bound is possible but would not change the verdict: S-BUMP alone exceeds
the settlement headroom, and stage 1 exceeds 1.3M without the R3 class.

## 5. Profiling consistency check (method step 4)

The `cu-profiling` verifier (`40d544ee...`) replayed 22 accepted runs: the six
fixtures plus 16 seeded runs (both kinds, splits 10/11, pairs 0
with a genesis page, 255, 256, 4095, 31337, 777777 and 2^20-1). Per-phase CU
is in `profile-phases.json`. Across (kind, split, transaction) groups, 196
phases vary, with summed ranges of 1-2k CU per group. The largest are
`r1:semantic` (up to 1,436, from lane-position loops and value branches),
stage-2 `r1:parsed` (673, the adapter's lane decode on zero bits) and the
Merkle and query phases (<= 70 each). `phase-attribution.json` maps each
varying phase to the functions that run in it and checks that its range is
at most the listed site maxima in those functions (or names the source
site): **0 phases are unexplained**. The Pool has no phase markers; its
variation is attributed at function level from the traces (page-mode
branches, page loops, bump searches).

## 6. Randomised and targeted sweep (method step 5)

**Time plan (recorded before launch).** No proof-system code is rebuilt
beyond the pinned verifier ELF. Expected time: (1) one cold optimized
native build of the sweep driver (`tools/r1-cost-probe`, LiteSVM + Agave
4.2.1 + prover crates), 15-30 min of compilation, once, plus one variant
with `litesvm/register-tracing`; (2) per run, OS-masked S2 proof generation
plus two LiteSVM transactions, about 5 s per run (the p3 OS-masked runs
recorded 5.0 s wall each, `p3-private-leaf-salts-20261013/p3-pool-13/*-os-run.json`);
lane construction is closed-form (`--uniform-lane`, at most 20*257 Poseidon
parents) so tree position does not add time. 2 kinds x 300 random runs plus
about 40 targeted runs is about 55 min of proof generation and replay, well
inside 3 h, so no down-sampling is needed. Stage 1 and settlement are both
measured in every run, so each run counts once per transaction kind.

Harness: `harness/patch_driver.py` derives the sweep driver from the exact
driver source that produced the saved fixtures (sha256 `606a80ae...`,
embedded in `decision1h-rollover-measurements-20261019/driver-source.json`);
all additions are opt-in and a no-option run is checked to reproduce the
saved fixture CU. `harness/sweep.py` runs every case sequentially inside one
capped scope and records command, exit, wall, RSS and swaps per run.

**Results [swept].** 658 accepted runs in total, with no failures and no
rejections (`sweep.jsonl`; `set` = control/targeted/trace/profile/random):

- 6 controls: the saved fixtures replayed with the new driver reproduce every
  stage-1, settlement and nested CU exactly.
- 600 random runs, 300 per kind. Each has a fresh OS-masked proof and a
  random witness (input value, outputs, membership path, super-root path,
  `selected_second`), so the nullifier, and with it the output lane (all 8
  lanes hit) and the marker PDA, are random. Checkpoint sequence and lane
  position are also random: pairs uniform on [0, 2^20), rollover positions,
  small positions, near-cap, and specials. Split is random 10/11; 172 runs
  are rollovers.
- 52 targeted runs (26 per kind): the cap 2^20-1 and 2^20-2, a zeroed genesis
  page, pairs 0/1/255/256/511/1023/65535/524287 at both splits, and
  marker-bump grinding (19 attempts). A first attempt of these 52 failed at
  witness compilation because the seeded checkpoint sequence exceeded
  `POOL_V1_LEAF_CAPACITY` (`payment_relation.rs` `validate_common`). The
  generator was fixed (anchor sequence < 2^20), the driver rebuilt, and the
  set rerun; the failed ledger is kept as `targeted-attempt1-anchor-seq`.
- 12 traced and 22 profiled runs (sections 3 and 5).

| Kind | Split | Stage 1 min-max | Settlement min-max (random) |
|---|---|---|---|
| transfer | 10 | 1,198,625-1,199,982 | 1,101,607-1,192,252 |
| transfer | 11 | 1,237,692-1,239,161 | 1,061,719-1,149,636 |
| withdrawal | 10 | 1,197,205-1,198,648 | 1,113,707-1,206,877 |
| withdrawal | 11 | 1,236,243-1,237,878 | 1,074,162-1,182,833 |

Maximum over all runs: stage 1 1,239,161 (T) / 1,237,878 (W), settlement
1,231,724 (T) / 1,245,323 (W, marker grinding), all below their bounds.
Three classes of accepted transaction exceed the measured fixtures and the
old 1.2M line: stage 1 with `[3,11]`, random withdrawal settlements
(1,206,877), and marker-ground settlements.
Random sweep time: 0.82 h of run wall time in total, peak RSS 259 MiB,
0 swaps.

## 7. Run ledger

Every run's command, exit status, wall time, peak RSS, swaps and cgroup caps
are in `receipts/run-ledger.jsonl` (sweep, targeted, trace and profile runs)
and `receipts/build-and-analysis-receipts.json` (SBF builds, native driver
builds including the failed first attempt with a missing `include!`
source, and trace analyses). All ran on the NUC under `systemd-run --user
--scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64`
with `-j 4` and optimized profiles. Peak build RSS was 0.65 GB and peak
analysis RSS 1.4 GB; all runs had 0 swaps. No Lean compilation ran, so
`#print axioms` is N/A. Binaries are not committed; SHA-256 and sizes are in
`artifacts-sha256.txt`. Host workspace:
`/home/dombarker/project-offloads/codex-r1-cu-bound-20261019`, with task
keys retained there privately (0700/0600). The register traces (2.5 GB)
were deleted after analysis.
