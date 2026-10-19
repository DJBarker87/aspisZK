# Worst-case CU upper bound for the R1 two-transaction path (2026-10-19)

Pre-registration followed: `design/PREREG-CU-UPPER-BOUND-20261019.md` (method
steps 1-5, PASS/FAIL/INCOMPLETE, labels). Criteria unchanged.

Labels used throughout: **[measured]** = a LiteSVM replay CU of a concrete
transaction; **[analytical]** = derived from source/ELF and the Agave cost
schedule; **[swept]** = maximum over the randomised step-5 sweep.

## Verdict

(pending)

## 0. Target pin

(pending)

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

## 2. Site enumeration (method step 1-2)

(pending)

## 3. ELF control-flow audit

(pending)

## 4. Bound B_tx (method step 3)

(pending)

## 5. Profiling consistency check (method step 4)

(pending)

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

(results pending)

## 7. Run ledger

(pending)
