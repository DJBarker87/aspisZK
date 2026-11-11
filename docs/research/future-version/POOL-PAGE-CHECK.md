# Aspis Pool: cheap zero checks of the root-history pages

Status: v2 (slice equality) is the final page-check form; final Pool ELF for the freeze built from head 965955709cc and gated (last section). All gates passed. Tests and measurements only. Nothing here is proved, committed or deployed.

Scope (owner's approval of 2026-11-11): the byte-by-byte zero checks of the Pool's root-history pages are
replaced by a cheaper check of the same predicate. The checks cover the unused tail of the current page,
the whole next page at rollover and the zeroed page 0 at genesis. Each replacement returns the same error
at the same point in the control flow. Account layouts, instruction formats, account writes, required
accounts and every other check stay as they are. The verifier, the prover and `crates/` are not touched.

## Predictions (written 2026-11-11T21:19:07Z, before any measurement)

Candidates: **A**, one `sol_memcmp` call (the region against itself shifted by one byte) plus a first-byte
test. **A2**, the same written as slice equality. **B**, an index loop over 8-byte words read as `u64`, then
the remaining bytes. The predictions are for the X1 verifier ELF and the one-lamport marker. "Pool's own" is
the Pool's inclusive cost minus the nested verifier's. The old figures are the deployed Pool's, taken from
WORST-CASE-COMPUTE.md.

| Scenario (withdrawal unless stated) | Old Pool's own | Predicted new Pool's own, A | Band |
|---|---:|---:|---|
| Rollover, n = 255 | 140,305 | 74,300 | 73,000 to 76,000 |
| Rollover, n = 1023 | 140,243 | 74,250 | 73,000 to 76,000 |
| Same page, nearly full, n = 254 (64-byte tail) | 71,639 | 71,300 | 70,500 to 71,700 |
| Same page, young, n = 3 (8,064-byte tail) | 109,865 | 59,000 | 55,000 to 64,000 |
| Same page, n = 1 | not measured; 110,200 predicted | 59,000 | 55,000 to 64,000 |
| Genesis (n = 0, zeroed page 0) | 110,837 | 45,000 | 42,000 to 50,000 |
| Transfers, same positions | | withdrawal − 9,400 | ± 300 |

Basis: the next-page scan costs 66,048 (8 instructions per byte, from the trace), the tail scan about 6.3
instructions per byte (from the difference between n = 3 and n = 254 after the decoding of 251 more
roots at about 49 instructions each), and one `sol_memcmp_` of 8,255 bytes is charged
max(10, 8,255 / 250) = 33 plus about 20 instructions of setup.

Whole transaction: the saving equals the Pool's saving (the verifier is unchanged). The heaviest case
stays the rollover withdrawal (the rollover keeps its decode of 256 roots, its page write, one more
address derivation and one more account): seed 60, one-lamport marker, 1,354,102 − 66,000 = about
1,288,100. New worst case with the X1 allowance of 10,697: about 1,298,800, headroom about 101,200.

Other candidates: A2 within 100 of A if the compiler lowers the slice comparison to the `sol_memcmp_`
syscall, otherwise much slower; B at the rollover saves 40,000 (band 5,000 to 61,000), depending on whether
the eight byte reads become one 8-byte load.

Behaviour: every positive run succeeds with the same final state under the old and the new Pool, every
run one unit below its cost fails with no state change, and every negative scenario is rejected by both
Pools with the same error and no state change.

## The change

Patch: `docs/research/future-version/pool-page-check/pool-page-check.patch`, sha256
`2e23d8682d504cf64ed8c6405e004d7c72b224608be6571aa99cbdab19f0f16b` (`diff -ruN` of
`programs/aspis-pool` against `src-xp1`, the head source 4045ecbdda3 with the X1 rewrites). It touches two
files. The code changes are four replaced lines and one new helper. Everything else in the patch is
test-only. No `unsafe`, no feature flag, and no change to `Cargo.toml` or to any other file.

New helper, `history.rs` 52-70: doc comment 52-60, `#[allow(deprecated)]` at 61, function 62-70. The
hash below covers lines 62-70:

```rust
pub(crate) fn page_bytes_are_zero(data: &[u8]) -> bool {
    data.is_empty()
        || (data[0] == 0
            && solana_program::program_memory::sol_memcmp(
                &data[..data.len() - 1],
                &data[1..],
                data.len() - 1,
            ) == 0)
}
```

Form: one SDK call, no loop. A non-empty region is all zero iff its first byte is zero and every byte
equals the next one. `sol_memcmp` is given two slices of length `len - 1` and `n = len - 1`, so it reads
only bytes of `data`. The helper is `pub(crate)`, not private, because `pair_forest.rs` calls it. It is
called only from the four functions below.

Functions whose body changed. Body hash = sha256 of the function's text from its `fn` line to its closing
brace, with a trailing newline:

| File | Function | Lines before | Lines after | sha256 before | sha256 after |
|---|---|---|---|---|---|
| history.rs | `page_bytes_are_zero` (new) | — | 62-70 | — | `e5d86c6cc28c0a638ebffc26fdeee0633927990d959059cd81a8aaaccf14401e` |
| history.rs | `validate_root_page_bytes` (tail check, one line) | 119-175 | 139-195 | `76e35fad9075217df312a10a24f13d103409fd920ffdcd5d269e52770d6a67f2` | `733339d6c485733a5594ce585e7e4b2b2ecc1d1129fa240cf6c9350212db414a` |
| history.rs | `validate_new_page_account` (one line) | 284-297 | 304-317 | `5f7c389802769211d037a5f14251054710a31ba3a0ddb0f3fc647df1f7b27750` | `b7e0747507ca48085ff5d5838127bdc9fe218530b5e7e364e8e8dde5656d1ea7` |
| pair_forest.rs | `require_program_owned_zeroed` (one line) | 400-415 | 400-415 | `6f0a6e4a2f4af8e06657ad695dbd335a0b3525bbc3ad412a2e7f067a3e9cbaf0` | `8de47156762705ad866f715003f827e793fb12eb226766340ac6ac995bcef3a3` |
| pair_forest.rs | `account_is_zeroed_program_page` (one line) | 806-815 | 806-815 | `b5b2ab0b63d8602595138e9d9a095a7c60e1b3bdbd4be0cf85f278bdfccee214` | `4dd1bb792a639b45978c5b33e7d3606d06d551978539fe43d6ebe9c344d9deea` |

Each replaced line keeps its place in its function, so the order of checks and the errors are unchanged:
- `validate_root_page_bytes`: header, then pool, page, first sequence and fill, then the canonical roots,
  then the tail, which gives `InvalidAccountData`.
- `account_is_zeroed_program_page`: the owner and length test still returns `false` before any borrow. The
  only error still comes from `try_borrow_data`, and the temporary borrow ends inside the statement.
- `require_program_owned_zeroed`: owner, writability, length, zero bytes, then rent, giving
  `InvalidFreshAccount`.
- `validate_new_page_account`: length, then zero bytes, giving `InvalidAccountData`.

Every other function in `programs/aspis-pool` has a byte-identical body:
- `pair_forest.rs` has the same 60 top-level functions with identical bodies and line ranges. The
  planner `plan_pair_forest_spend_layout_v1` (1218-1319, `6aa1e7b1…c051`), the terminal handler
  `process_pair_forest_terminal_with_verifier_v1` (1615-1821, `b27ff42d…781e`), `validate_lane_current_page`
  (817-860) and `process_pair_forest_terminal_v1` (1823-1841) are untouched.
- **No line number in `pair_forest.rs` moved.** Lines 1-5794 differ only at 409 and 814. The test module
  is appended after line 5794.
- In `history.rs`, the eight unchanged functions after line 50 moved down by 20 lines (the new helper
  and its comment). Their bodies are identical.
- No other file changed.

Why `require_program_owned_zeroed` is included: it is the deposit path's zero check of a fresh history
page (genesis and rollover). It is the same predicate as the terminal path's check, and it also guards
the fresh master, lane and checkpoint accounts at initialize. `validate_new_page_account` is the same
check on the older pair path.

Candidates measured (the comparison runs below): A, the call above; A2, the same as slice equality; and
B, an index loop over `u64` words with the result carried in a variable. A2 compiles to the same
syscall (A and A2 differ by at most 4 CU). A is chosen because the call is explicit in the source rather
than left to the compiler's lowering. B saves only 7,741 at the rollover and costs 9,057 more than the
old code on the young page (its eight byte reads stay eight loads). B is rejected.

## Gates

Host receipts (8 GiB cap, no swap, all in `evidence/future-version-20261111/pool-page-check/receipts/receipts.txt`):
`PL-build-base`, `PL-build-a2`, `PL-build-b`, `PL-build-final`, `PL-tool-build`, `PL-test-*`, `PL-W-*`,
`PL-R-*`, `PL-RD-final`. Host scripts: `evidence/future-version-20261111/host/fv_pool_build.sh`,
`fv_pool_cands.sh`, `fv_pool_tool.sh`, `fv_pool_test.sh`, `fv_pool_worst.sh`, `fv_pool_replay.sh`.

**0. Baseline reproduced.** The unchanged Pool source (a copy of `src-xp1`) was built with the deployed
recipe: cargo-build-sbf 3.1.13, features
`r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`,
`--locked`, offline, `-j 4`, without the recorded diagnostics `RUSTC_WRAPPER`. The ELF is byte-identical
to the deployed one: `e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc`, 345,648 bytes
(`PL-build-base`, exit 0, 3:52, 644,248 kB). Four dependency files of `src-xp1` differ from the deployed
build's recorded sources: `aspis-core` `Cargo.toml`, `digest.rs` and `field.rs` (default-off
`future-*` features and a defaulted trait method) and `aspis-statement`'s
`pair_forest_semantic_terminal.rs`. The ELF is unaffected by them.

**1. Differential tests** (in the Pool crate; the old checks are kept verbatim as test-only oracles):
- for the helper (seven tests): the empty region; all-zero regions of every length 0..8,256, the
  257 tail lengths and the whole page, also at an odd offset; one non-zero byte (1, 0x80, 0xff) at every
  position of an 8,256-byte page; one non-zero byte at every position of the tails for fills 0, 1, 2, 3,
  4, 31, 127, 128, 200, 254 and 255; a non-zero first byte and a non-zero last byte at every length
  1..8,256; uniform non-zero regions; 100,000 pseudo-random regions (all zero, sparse, near either end,
  dense);
- for the changed functions, each against a verbatim copy of its old body:
  - `validate_root_page_bytes`, for fills 0..256 with one byte planted at every tail position;
  - `validate_new_page_account`;
  - `account_is_zeroed_program_page`, every position, wrong owner, wrong lengths;
  - `require_program_owned_zeroed`, every page position plus master, lane and checkpoint sizes, wrong
    owner, not writable, below rent.

All agree. On the host, `sol_memcmp` runs the SDK's Rust stub. The syscall itself is exercised only in
the LiteSVM runs (gates 3 and 4).

**2. Pool crate tests**, `--release`. Deployed feature set: 78 passed, 0 failed
(`PL-test-src-pool-final-deployed`, exit 0). Defaults: 45 passed, 0 failed (`PL-test-src-pool-final-default`, exit 0;
`pair_forest` is not compiled without the features). The 11 new tests are among them, and so are the
crate's own deposit and initialize tests.

**3. Real path, old Pool ELF against new Pool ELF, X1, extended `one_tx_worst`.** The tool extension is
`tools/r1-cost-probe/src/bin/one_tx_worst.rs`, sha256
`35f3a0e3a154613dd665131b9b9682cb1244eea84c40963bfc502757449763e1`. It adds the `neg-<tail|next|genesis>-<first|mid|last>` modes and a
post-state hash for every run; the existing modes are unchanged. The runs cover 14 positive scenarios:
- genesis, transfer and withdrawal;
- n = 0 (initialised page), 1, 3, 254, 255 and 1023, transfer and withdrawal (no transfer at n = 0);
- withdrawal at n = 255 with seed 60.

Each positive scenario runs in the three marker states plus once one unit under its cost (56 runs per
Pool). The 18 negative scenarios plant one byte at the first, middle and last position of:
- the tail at n = 3 (transfer and withdrawal);
- the tail at n = 254;
- the next page at n = 255 (transfer and withdrawal);
- page 0 at genesis.

Results (`old-pos.json`, `new-pos.json`, `old-neg.json`, `new-neg.json`; `compare.py` → `compare.txt`:
`ALL_RUNS_AGREE_AND_AS_EXPECTED True`):
- every run of the old and the new Pool has the same proof, the same error and the same post-state
  hash of every watched account;
- all 42 settling runs write the independently expected lane, pages, marker and token movement;
- all 14 runs one unit under their cost fail with `ProgramFailedToComplete` and leave everything but the
  payer's fee unchanged;
- all 18 negative scenarios are rejected by both Pools with the same error and no state change: tail
  `InvalidAccountData`; next page `Custom(1095966773)`; genesis `Custom(1095966721)`, because a non-zero
  page 0 takes the same-page branch and fails the header check.

Deposit and initialize are not reachable with this tool. They are covered only by the unit tests
above and the crate's own tests.

**4. Replays with the new Pool** (`final-transfer.json`, `final-withdrawal.json`,
`final-redirect-withdrawal.json`). The deployed-Pool baselines are `replays-v5/X1-rewrites-*.json` and
`replays-redirect/X1-rewrites-withdrawal.json`; they were not rerun.
- Same outcomes as the baseline. Both one-transaction settlements complete. The changed certificate
  and the pinned-format buffer are rejected with no state change. The marker variants settle.
- Every state-difference list is empty, including `control_vs_recorded`: with the new Pool, the control
  (deployed two-step verifier) ends in the recorded devnet final state.
- `one_tx_replay` exits 1 because `control_reproduces_recorded` is now false. That check compares the
  control's Pool CU with the recorded devnet figure (1,139,872 → 1,091,132 transfer, 1,155,430 →
  1,106,690 withdrawal), which the cheaper Pool changes by design. The JSON is written before that
  check.
- Redirect: the four attempts are rejected with the same errors as before, and the honest and
  other-payer settlements pay the recorded destination.

## Measured against predicted (X1, one-lamport marker; "Pool's own" = Pool inclusive − nested verifier)

| Scenario | Old Pool's own | New Pool's own | Predicted (band) | Verdict | Whole tx old → new |
|---|---:|---:|---|---|---|
| Withdrawal, rollover n = 255, seed 1 | 140,305 | 73,779 | 74,300 (73,000-76,000) | in band, 521 below | 1,342,968 → 1,276,442 |
| Withdrawal, rollover n = 1023 | 140,243 | 73,717 | 74,250 (73,000-76,000) | in band | 1,348,925 → 1,282,399 |
| Withdrawal, n = 254 | 71,639 | 70,947 | 71,300 (70,500-71,700) | in band | 1,279,352 → 1,278,660 |
| Withdrawal, n = 3 | 109,865 | 61,505 | 59,000 (55,000-64,000) | in band, 2,505 above | 1,316,637 → 1,268,277 |
| Withdrawal, n = 1 | 110,194 (predicted 110,200) | 61,454 | 59,000 (55,000-64,000) | in band | 1,314,850 → 1,266,110 |
| Withdrawal, n = 0, initialised page | 110,451 | 61,533 | — | — | 1,321,070 → 1,272,152 |
| Withdrawal, genesis | 110,837 | 61,346 | 45,000 (42,000-50,000) | **miss**. The old genesis scan cost 49,500, not the 66,000 I assumed from the next-page loop | 1,321,456 → 1,271,965 |
| Transfer, same positions | | withdrawal − 9,401 (rollover − 9,451) | withdrawal − 9,400 ± 300 | held | |
| Heaviest: withdrawal n = 255, seed 60 | 140,305 | 73,779 | | | 1,354,102 → **1,287,576** (predicted about 1,288,100) |
| Candidate A2 against A | | | within 100 | held (4) | |
| Candidate B, saving at the rollover | | | 40,000 (5,000-61,000) | in band, point missed by 32,259 | |

Recorded devnet payments, one transaction with X1: transfer 1,306,700 → 1,257,960, withdrawal 1,313,188 →
1,264,448 (−48,740 each).

**New worst case** (same method and allowance as WORST-CASE-COMPUTE.md): the heaviest measured case is
still the rollover withdrawal with seed 60 and a one-lamport marker, 1,287,576. Adding the X1 allowance
of 10,697 gives **1,298,273, headroom 101,727** (before: 1,364,799, headroom 35,201; gain 66,526). The
rollover remains the heaviest Pool path (73,779 against 70,947 for a nearly full page and about
61,500 for a young one).

**ELF:** `78b28e1494d01545f58113c347407b7a8fcf97bd6eb74709779f150617b4e15b`, 345,936 bytes
(`PL-build-final`), 288 bytes more than the deployed 345,648. A new deployment whose program-data
account is sized to the ELF locks 288 × 5,080 = **1,463,040 lamports more** (about 0.0015 SOL). The
change needs a new Pool deployment either way.

## v2, the final form: slice equality

**Why the form changed.** The soundness lead chose slice equality over the SDK call. Std slice
equality already has a modelled external in the Lean gate library, so the Pool uses only items that are
already trust rows. `sol_memcmp` would be a new SDK external to add and justify. The cost is the same
(form A2 above). The sections above describe v1 (form A, committed in 958241d3b80). v2 replaces it.

**The v2 change.** Tree `src-pool-final2` = `src-pool-final` with one edit in `history::page_bytes_are_zero`:

```rust
pub(crate) fn page_bytes_are_zero(data: &[u8]) -> bool {
    data.is_empty() || (data[0] == 0 && data[..data.len() - 1] == data[1..])
}
```

The name, signature and visibility are unchanged, and both borrows are shared. `#[allow(deprecated)]`
is dropped because the SDK path is no longer used, and the doc comment is updated. The four call sites,
the tests and every other line are as committed.

- **Patch:** `docs/research/future-version/pool-page-check/pool-page-check-v2.patch`, sha256
  `465a7bb5df06145edc31154bebc2ddc3e5e3470f942bdda19c98c237ebc20e2d`. It is the full change against
  `src-xp1`, restricted to `programs/aspis-pool`: 439 lines added, 4 removed.
- **ELF:** `2152a068a916169239138770cf27d272ba3c7dc72160564c245e4bebef50bb8a`, 345,720 bytes
  (`PL2-build`, exit 0).

**Per-function table for v2.**

| File | Function | Lines before (deployed) | Lines in v2 | sha256 in v2 |
|---|---|---|---|---|
| history.rs | `page_bytes_are_zero` (new) | — | 60-62 (doc comment 52-59) | `7c2e3da6235aaf3c3cb8e3c39a695e84240e28f2083a82970f1521e5fef2c17d` |
| history.rs | `validate_root_page_bytes` | 119-175 | 131-187 | `733339d6c485733a5594ce585e7e4b2b2ecc1d1129fa240cf6c9350212db414a` |
| history.rs | `validate_new_page_account` | 284-297 | 296-309 | `b7e0747507ca48085ff5d5838127bdc9fe218530b5e7e364e8e8dde5656d1ea7` |
| pair_forest.rs | `require_program_owned_zeroed` | 400-415 | 400-415 | `8de47156762705ad866f715003f827e793fb12eb226766340ac6ac995bcef3a3` |
| pair_forest.rs | `account_is_zeroed_program_page` | 806-815 | 806-815 | `4dd1bb792a639b45978c5b33e7d3606d06d551978539fe43d6ebe9c344d9deea` |

- The four functions' body hashes are **unchanged from v1**. Only the helper's body hash changed
  (v1 `e5d86c6c…401e`).
- The before-hashes are as in the v1 table.
- `pair_forest.rs` is identical to v1: no line moved, and the planner and the terminal handler are
  byte-identical to the deployed source.
- In `history.rs`, every function after the helper sits 12 lines below its deployed position (v1: 20).

**The comparison is the memory-compare syscall.** Confirmed from the built ELF by disassembly
(`evidence/future-version-20261111/host/fv_pool_memcmp_calls.py`, output in
`evidence/future-version-20261111/pool-page-check/v2/memcmp_calls.txt`). In each ELF, the script takes
the `sol_memcmp_` relocation sites (`llvm-readelf -r`) and the function that contains each site, then
counts the `call` instructions that target that function:
- deployed ELF: the only syscall site is in the compiler's `memcmp` wrapper (0x4e528), called from 1 site;
- v2 ELF: the only syscall site is in the same wrapper (0x4e570), which is four instructions plus
  the syscall and no loop, now called from **5** sites. These are the deployed 1 plus the 4 page-check
  call sites.

The CU confirms it independently. An inlined byte loop over 8,255 bytes would cost at least about
16,000, whereas v2 costs the same as form A to within 4.

**v2 gates** (attempts `PL2-*`; receipts in `evidence/future-version-20261111/pool-page-check/v2/receipts/receipts.txt`,
host script `evidence/future-version-20261111/host/fv_pool_v2.sh`). The old Pool and form A results are
the v1 runs above, not rerun.
1. **Differential and oracle tests:** all 11 pass.
2. **Pool crate tests,** `--release`. Deployed feature set: 78 passed, 0 failed. Defaults: 45 passed,
   0 failed.
3. **Old Pool against v2,** same 14 positive scenarios (three marker states and the run one unit under
   its cost each) and the same 18 negative scenarios (`new2-pos.json`, `new2-neg.json`;
   `compare_v2.py` → `compare_v2.txt`: `ALL_RUNS_AGREE_AND_AS_EXPECTED True`):
   - every run has the same proof, error and post-state hash under the old Pool, form A and v2;
   - every settling run writes the expected state;
   - every under-limit run fails with no change;
   - every negative scenario is rejected with the same error and no change.
4. **Replays and redirect attempts** (`final2-*.json`): same outcomes as the deployed Pool and as form
   A, and every state-difference list is empty (including the control against the recorded devnet
   final state). Redirect: the same errors, and the honest settlements pay the recorded destination.
   `one_tx_replay` exits 1 for the same reason as in v1, because the control's Pool CU differs from the
   recorded figure.
5. **Compute** (X1, one-lamport marker; whole transaction, old / form A / v2):

| Scenario | Old | Form A | v2 | v2 − A |
|---|---:|---:|---:|---:|
| Withdrawal, rollover n = 255, seed 60 (heaviest) | 1,354,102 | 1,287,576 | 1,287,572 | −4 |
| Withdrawal, rollover n = 255 | 1,342,968 | 1,276,442 | 1,276,438 | −4 |
| Withdrawal, rollover n = 1023 | 1,348,925 | 1,282,399 | 1,282,395 | −4 |
| Withdrawal, n = 254 | 1,279,352 | 1,278,660 | 1,278,662 | +2 |
| Withdrawal, n = 3 | 1,316,637 | 1,268,277 | 1,268,279 | +2 |
| Withdrawal, n = 1 | 1,314,850 | 1,266,110 | 1,266,112 | +2 |
| Withdrawal, n = 0 (initialised page) | 1,321,070 | 1,272,152 | 1,272,153 | +1 |
| Withdrawal, genesis | 1,321,456 | 1,271,965 | 1,271,968 | +3 |
| Transfers, same positions | | | | −4 to +3 |
| Recorded transfer, one transaction | 1,306,700 | 1,257,960 | 1,257,962 | +2 |
| Recorded withdrawal, one transaction | 1,313,188 | 1,264,448 | 1,264,450 | +2 |

On every settling run, v2 is at most 3 CU above form A (largest difference +3, at genesis) and up to
4 below it at the rollover.

**New worst case (v2):** 1,287,572 + 10,697 = **1,298,269, headroom 101,731**.

**Rent (v2):** 345,720 − 345,648 = 72 bytes more than the deployed ELF, so 72 × 5,080 = **365,760 lamports
more** for a deployment sized to the ELF.

## For review before deployment (applies to v2, the final form)

- The slice comparison compiles to the compiler's `memcmp`, which makes one `sol_memcmp_` syscall
  over two overlapping regions (`data[..n-1]` and `data[1..]`). agave 4.2.1 in LiteSVM accepts this,
  and all runs depend on it. Check that the cluster runtime that will run the Pool has no overlap check
  on `sol_memcmp_`. If one were added, every page check would abort, every payment would fail, and no
  state would change (availability, not soundness). The deployed Pool already reaches `sol_memcmp_`
  through the same `memcmp` wrapper.
- Deposit, initialize and the older pair path are covered by unit tests and the crate's own tests only,
  not by a LiteSVM run.
- Only fixture witnesses were used, with lane positions up to 1023.

## Separate proposal, not implemented: the strict decode of the filled roots

At the rollover, `validate_root_page_bytes` decodes all 256 roots through `decode_digest_canonical`
(about 12,500 CU). The same predicate ("every 4-byte limb of the filled region is below P") could be
checked by one index loop over the `8 × filled` little-endian `u32` limbs, with the result carried in a
variable, without building `Digest` values. The error and its position stay the same: after the header
checks and before the tail check, `InvalidAccountData`. Estimated saving: up to roughly 8,000 at the
rollover. Not measured. It needs the same differential gate, including limbs equal to P − 1, P and
2^32 − 1 at every position.

Target status: unchanged, not yet established. These are tests and compute measurements, not a proof.

## Final Pool for the freeze (head 965955709cc)

The Pool to be frozen is the v2 page check plus tonight's reshaped functions in `aspis-statement` and
`aspis-core`, which the Pool links. It was built from `src-head3` (git archive of 965955709cc on the
host, not modified here) with the deployed recipe and its own target directory (`PL3-build`, exit 0,
2:10, 644,200 kB, 8 GiB cap, no swap).

**ELF: `0553a8bd5ef5c5ff93023b1923f96f9651a23f5aa4e50855baebe29109799cec`, 340,320 bytes.** It is
5,328 bytes smaller than the deployed ELF, so a deployment sized to the ELF locks
5,328 × 5,080 = 27,066,240 lamports less.

**What differs from the v2 ELF.** The Pool program directory is identical to v2. In the linked crates,
`wide_exact.rs` (core) and eight `aspis-statement` files differ. The function-level comparison of the
two unstripped ELFs is `evidence/future-version-20261111/host/fv_pool_fndiff.py`, output
`final/fndiff-v2-vs-head3.txt`. It compares `llvm-objdump` per symbol, with call and `lddw` immediates
and jump labels blanked. Of 284 functions:
- three have a different normalised body:
  - `decode_pool_v1_pair_forest_master_v1` (196 → 173 instructions);
  - `decode_pool_v1_pair_forest_checkpoint_v1` (188 → 188);
  - `decode_pool_v1_pair_verified_afterstate_v1` (833 → 103);
- one is new: `decode_afterstate_frontier_v1` (78);
- every other function is equal. Code inlined into a caller would show as a change in that caller, and
  none does.

The semantic-side functions (`external_linear_lazy`, `pattern_values_windowed`, `composition_parts`)
and `WideExact::to_le_bytes` leave no trace in the Pool ELF.

**Gates.** "Old" is the deployed Pool `e0e49c34…` and "new" is `0553a8bd…`. Both run against the
head's verifier ELF `out/BASE2/artifacts/aspis_r1_cost_probe_program.so`
(`7540abe6c5f07827011b11d3313fe5594816a32fa05963195ee4a1f5cf7856b5`). Tool `one_tx_worst.rs` sha256
`a52346355b68dad0e81ca758309ee9b2d2586552fce7c2e05c8e7514a2c0c159`, extended with
`neg-<master|checkpoint|lane>-<byte>`, which XORs one byte of that account with 0x01. Host script
`fv_pool_final.sh`; results and receipts in `evidence/future-version-20261111/pool-page-check/final/`.
1. **Pool crate tests in `src-head3`,** `--release`: deployed features 78 passed, 0 failed;
   defaults 45 passed, 0 failed (all 11 page-check tests among them).
2. **The 14 positive scenarios** (three marker states and the run one unit under its cost each, 56 runs
   per Pool) **and the 18 planted-byte scenarios**. `compare_final.py` → `compare_final.txt`:
   `ALL_RUNS_AGREE_AND_AS_EXPECTED True`.
   - Every run has the same proof, error and post-state hash under both Pools.
   - Every settling run writes the expected state.
   - Every under-limit run fails with no change.
   - Every planted byte is rejected with the same error and no change.
3. **Account corruptions** (withdrawal, n = 3), 15 scenarios at field starts:
   - master bytes 0 (magic), 40, 49, 64, 320 and 383 (last);
   - checkpoint bytes 0, 8, 72, 80, 112 and 191 (last);
   - lane bytes 0, 40 and 80.

   Both Pools behave identically in all 15: same error or outcome, same post-state. Thirteen are
   rejected with no state change. **Two settle under both Pools:** master byte 320 (low byte of the
   first last-sequence value) and checkpoint byte 112 (low byte of the first lane-sequence value). The
   payment completes and the post-state is identical under old and new. This behaviour predates
   tonight's change. These fields are not checked against this payment, and someone should confirm
   that this is intended. The decoders' own oracle tests (about 1.2 million single-byte corruptions)
   stand as recorded by their worker.
4. **Replays and redirect attempts,** old and new Pool with BASE2:
   - same outcomes, and every state-difference list is empty for both, including the control against
     the recorded devnet final state;
   - the redirect attempts are rejected with the same errors, and the honest settlements pay the
     recorded destination;
   - recorded payments in one transaction: transfer 1,280,964 → 1,232,533, withdrawal
     1,287,485 → 1,239,054;
   - the new Pool's `one_tx_replay` exits 1 only because the control's Pool CU differs from the
     recorded devnet figure.

**Compute at the head** (BASE2 verifier; Pool's own = Pool inclusive − nested verifier; whole
transaction; old → new):

| Scenario | Marker | Pool's own, old → new | Whole transaction, old → new |
|---|---|---:|---:|
| Withdrawal, rollover n = 255, seed 60 | absent | 136,208 → 69,985 | 1,324,151 → 1,257,928 |
| | one lamport | 140,305 → 74,082 | 1,328,248 → **1,262,025** |
| | full rent | 138,690 → 72,467 | 1,326,633 → 1,260,410 |
| Withdrawal, rollover n = 255, seed 1 | absent | 136,208 → 69,985 | 1,313,265 → 1,247,042 |
| | one lamport | 140,305 → 74,082 | 1,317,362 → 1,251,139 |
| | full rent | 138,690 → 72,467 | 1,315,747 → 1,249,524 |
| Transfer, rollover n = 255 | one lamport | 130,854 → 64,631 | 1,309,787 → 1,243,564 |
| Withdrawal, rollover n = 1023 | one lamport | 140,243 → 74,020 | 1,323,213 → 1,256,990 |
| Withdrawal, nearly full n = 254 | absent / one lamport / full rent | 67,542 / 71,639 / 70,024 → 67,159 / 71,256 / 69,641 | 1,249,531 / 1,253,628 / 1,252,013 → 1,249,148 / 1,253,245 / 1,251,630 |
| Transfer, n = 254 | one lamport | 62,238 → 61,855 | 1,244,516 → 1,244,133 |
| Withdrawal, young n = 3 | absent / one lamport / full rent | 105,768 / 109,865 / 108,250 → 57,717 / 61,814 / 60,199 | 1,286,839 / 1,290,936 / 1,289,321 → 1,238,788 / 1,242,885 / 1,241,270 |
| Transfer, n = 3 | one lamport | 100,464 → 52,413 | 1,285,652 → 1,237,601 |
| Withdrawal, genesis | absent / one lamport / full rent | 106,740 / 110,837 / 109,222 → 57,559 / 61,656 / 60,041 | 1,291,589 / 1,295,686 / 1,294,071 → 1,242,408 / 1,246,505 / 1,244,890 |
| Transfer, genesis | one lamport | 101,436 → 52,255 | 1,282,718 → 1,233,537 |

The Pool's own cost at the head is v2's plus 307 on every settling run (for example 73,775 → 74,082 at
the rollover). The other worker measured the same +307 for the reshaped decoders.

**Worst case at the head:** the heaviest measured case is the rollover withdrawal with seed 60 and a
one-lamport marker, 1,262,025. Adding the 10,697 allowance (the X1 figure, used here as instructed for
BASE2) gives **1,272,722, headroom 127,278**.
