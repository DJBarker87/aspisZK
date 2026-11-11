# Aspis: optimisation rounds on the one-transaction verifier

Status: in progress. Measurements and tests only; nothing here is proved and nothing here is adopted.

Baseline: build X1 (branch head 7dffe3e2a93, ELF
`7a77273b1dc64689a0eed1cc267c6e81c9f6d0ad2e17fe0be316243d3ae9a3d5`). Worst case 1,364,799 =
heaviest measured 1,354,102 (withdrawal at the page rollover, n = 255, fixture seed 60, marker funded
with one lamport) + 10,697 allowance (WORST-CASE-COMPUTE.md). Headroom 35,201. Target: recover at
least 25,000 CU at that worst case.

Rules applied to every candidate: implementation only (no change to the proof format, the transcript,
the order or number of digest calls, the prover or anything it calls, the Pool, or the direct
`sol_sha256` call; no new `unsafe`); it must stay translatable; same verdicts as X1 on the mutation
campaign; measured on the two recorded payments and at the worst case. One profiling pass, then at most
two rounds.

## 1. Profile of X1 at the worst case

Host scripts: `evidence/future-version-20261111/host/fv_opt_prof.sh` (builds and runs),
`fv_opt_dbg.sh` (debug-line build of a tree), `fv_opt_hot.py` (execution counts beside the
disassembly), `fv_opt_sys.py` (executed syscalls by name), `fv_opt_callers.py` (call sites of a
function), `fv_opt_loops.py` (hot loops of a stripped program). Receipts `OPT-dbg-x1`, `OPT-prof-x1`,
`OPT-trace-tool`, `OPT-trace-run`, `OPT-phase-run`, `OPT-trace-profile`, `OPT-hot-1`, `OPT-sys-1`,
`OPT-callers-1`, `OPT-pool-loops-1`, all exit 0.

Two profiling ELFs, neither of them a candidate:

- a debug-line build of the X1 source (`OPT-dbg-x1`, stripped ELF
  `7870747f8dbc161451186ef897e3cbe701110dd7d7e9a0d3cc836c74e961f5fe`, not byte-identical to X1). In
  the traced rollover withdrawal its nested verifier uses 1,215,432 CU against X1's 1,213,441 (+1,991,
  0.16%), and the Pool's own cost is identical (136,208, marker absent). It is used for attribution
  only. Trace: 1,045,191 executed instructions in the verifier, 112,505 in the Pool, 105 in SPL Token.
- a phase-marker build (`cu-profiling`, `detail-phases`; `OPT-prof-x1`, ELF
  `4f013a7182baa92c212154ba1d56f3a80d1211c016d550680dccc4db119ea62c`). Its verifier uses 1,224,627
  CU on the same scenario, 11,186 more than X1 for 23 markers (about 490 each). Each interval below
  contains one marker.

The scenario is the worst-case one: withdrawal, lane leaf count 255 (page rollover), fixture seed 60
(897 Merkle parent digests, nodes 292/292/250, 112 + 112 insertion-sort exchanges), the `one_tx_worst`
tool built with LiteSVM register tracing (`opt/one_tx_worst-trace`), deployed Pool ELF
`e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc`.

**Whole transaction, X1, one-lamport marker: 1,354,102.**

| Part | CU | Source |
|---|---:|---|
| Compute-budget instructions and transaction overhead outside the Pool | 356 | X1 run |
| Pool's own work, including its CPI and syscall charges (marker absent 136,208; one-lamport marker adds 4,097) | 140,305 | X1 run |
| of which: zero check of the 8,256-byte next history page, byte by byte (8 instructions per byte) | 66,048 | Pool trace |
| of which: strict decode of the 256 roots of the full current page (and other digests) | about 12,500 | Pool trace (305 decodes of 28 instructions, 256 loop steps of 15) |
| of which: other Pool instructions | about 33,950 | Pool trace (112,505 executed in all) |
| of which: syscalls and CPI charges (System, verifier and SPL Token calls, address derivations, marker) | 27,800 | 140,305 − 112,505 |
| Nested verifier | 1,213,441 | X1 run |

Verifier phases (phase-marker build; X1 is 11,186 lower in total):

| Phase | CU |
|---|---:|
| Adapter entry | 1,476 |
| Statement reconstruction and checks, shape check, canonical scan | 42,619 |
| Semantic: expansion and prefix parse | 22,541 |
| Semantic: public transcript and first challenges | 18,984 |
| Semantic: sumcheck rounds | 59,929 |
| Semantic: claims and terminal evaluation | 256,822 |
| Semantic: mask value and terminal equality | 8,846 |
| Semantic: circle challenges and finish | 8,192 |
| Preparation (challenges, queries, gamma powers, claim) | 90,146 |
| Query geometry and fold coefficients | 30,606 |
| 26 base-field lanes and their first-fold terms | 152,213 |
| Three QM31 lanes, first-fold close | 83,419 |
| Second fold | 61,303 |
| Relation round checks | 11,929 |
| Final sumcheck: lambda and six rounds | 12,325 |
| Equality tables | 12,825 |
| Final-message extension | 20,830 |
| `Weights::new` and the weight extension | 92,335 |
| Query-weight extension | 28,250 |
| Final equality | 1,157 |
| Merkle authentication (66 leaf and 897 parent digests) | 201,426 |
| Result encoding and return | 6,454 |
| **Total (phase-marker build)** | **1,224,627** |

Syscalls executed by the verifier (debug-line build, from the relocation of each call site and the
trace): `sol_sha256` 1,099 (897 in the Merkle parent loop, 202 through `hashv`: 66 leaves and 136
transcript digests); `sol_memcpy_` 400; `sol_memset_` 77; `sol_create_program_address` 7 (the
adapter's account checks, 1,500 each, 10,500); one each of clock, memmove, memcmp, and two
return-data calls. Syscall charges in all: 170,241.

Digests, count × cost (from the agave 4.2.1 rule: 85 per call plus, per input slice,
max(10, length / 2)):

| Digests | Count | CU each | CU |
|---|---:|---:|---:|
| Merkle parents, parts (1 tag byte, 32, 32) | 897 | 127 | 113,919 |
| C1 leaves, parts (2, 480, 32) | 22 | 351 | 7,722 |
| C2 and folded leaves, parts (2, 128, 32) | 44 | 175 | 7,700 |
| Transcript and semantic transcript | 136 | about 190 | about 25,800 (remainder) |

Instructions around the 897 parent digests: 55,112 in `merged_level` (61 per parent). The disassembly
shows the eighteen level calls of each tree unrolled inline, with most loop variables kept on the stack.

Largest functions by executed instructions (debug-line build; "self" excludes outlined callees):

| Function | Inclusive | Self |
|---|---:|---:|
| `aspis_statement` terminal evaluation (`terminal_qm31`) | 254,067 | (several) |
| `fused::fold_sums` | 308,079 | 151,822 |
| `fused::base_lanes_tight` | 123,247 | 122,842 |
| `verifier::Prepared::new` (claim dots 60,690) | 85,966 | 78,764 |
| `weights::Weights::mle_at` | 73,855 | 37,627 |
| `fused::merged_merkle` (`merged_level` 55,112) | 71,482 | 69,291 |
| `r1_semantic::semantic_value` | 38,890 | 38,890 |
| `fused::query_weight_mle_pairs` | 27,556 | 27,556 |
| `fused::summed_final_checks` | 160,712 | 25,583 |
| `candidate::canonical_scan_pinned` | 16,879 | 8,282 |

Inside `base_lanes_tight`: the per-query lane loop is 185 instructions per lane and query (572 of
them, 105,820), and the periodic fold of the 416 accumulators is 10 instructions per entry, run seven
times (2,912 entries, 29,120).

## 2. Candidates

Classes: (V) verifier implementation only, allowed; (X) needs a format, transcript or call-order
change, or touches code the prover calls, excluded, listed only; (P) Pool, not implemented, sized.

| Id | Class | Candidate | Basis |
|---|---|---|---|
| A1 | V | `merged_level` out of line (`#[inline(never)]`), body unchanged | 61 instructions per parent digest, mostly stack traffic from the unrolled inline copies |
| B1 | V | `base_fold` eight entries per loop step | 10 instructions per entry, of which about 4 are loop overhead |
| B2 | V | `base_query` reordered: the lanes' signed sums first, then each coefficient's four limbs held across all lanes | 185 instructions per lane and query against about 120 for the same products with the limbs in registers |
| A2 | V | merged traversal over one scratch structure (indices and both digest buffers), the next index carried | further cut of the per-parent stack traffic, if A1 leaves it high |
| A3 | V (translator risk) | Merkle tag byte stored in front of each digest so a parent digest has two input slices (33, 32) in place of three (1, 32, 32) | 10 CU per parent digest whose left input is a computed digest (the per-slice minimum of 10 for the 1-byte tag). Needs a 33-byte view of a buffer that also takes the 32-byte output, which the translator's library may not model |
| X1t | X | Same slice merging in the transcript (row header 2 + 4 bytes; the `[1]` and `[2]` suffixes) | 10 CU per small slice, about 2,000 to 3,000 in all; `Transcript` is called by the prover, so excluded |
| Xs | X | `aspis_statement` terminal evaluation (254,067 instructions) | shared with the prover and the R1 statement crate; excluded |
| Xp | X | Adapter address checks by one SHA-256 instead of `create_program_address` (7 × 1,500) | about 9,000; not the same function: it would accept a key equal to an on-curve hash, which `create_program_address` rejects. Rejected under rule 3 |
| P1 | P | Pool: word-wise (or one `sol_memcmp` over the page against itself shifted by one byte) zero check of the next page and of the unused page tail | see section 5 |

### Round 1 predictions (written 2026-11-11T20:44:30Z, before any candidate build)

Whole-transaction saving against X1, same at the recorded payments and at the worst case unless
stated (the Merkle saving scales with the parent count: 897 at the worst case, fewer on the recorded
payments).

| Candidate | Predicted saving, worst case | Band | Recorded payments |
|---|---:|---|---|
| A1 Merkle level out of line | 10,000 | 3,000 to 20,000 | about 9,000 |
| B1 fold eight per step | 8,000 | 3,000 to 12,000 | same |
| B2 base query reordered | 15,000 | −5,000 to 30,000 | same |
| R1 = A1 + B1 + B2 | 30,000 | 10,000 to 50,000 | about 29,000 |

Kept for round 2 only if it saves at least 1,000 at the worst case and passes every gate.

### Round 1 results

Builds: recipe and feature set of X1 (`fv_build_adapter_src.sh`, `fv_round7.sh` features), each from
its own copy of `src-xp1` and its own target directory. Host script `fv_opt_round.sh r1 a1 b1 b2 r1
r1x2`, receipts `OPT-B-*`, `OPT-R-*`, `OPT-RD-*`, `OPT-W-r1`, all exit 0. Worst-case scenario as in
section 1 (`withdrawal:255:60:full`, 897 parent digests), run once with X1 and every round-1 ELF in the
same tool run.

| Build | ELF sha256 | Bytes | Transfer | Withdrawal | Worst case, one-lamport marker | Saving at the worst case |
|---|---|---:|---:|---:|---:|---:|
| X1 | `7a77273b1dc64689a0eed1cc267c6e81c9f6d0ad2e17fe0be316243d3ae9a3d5` | 972,024 | 1,306,700 | 1,313,188 | 1,354,102 | |
| A1 | `9253d35da02d9cfe3cb67e2822756f045929273684f6ac52629017cc1af04337` | 972,528 | 1,307,924 | 1,314,323 | 1,355,572 | −1,470 |
| B1 | `8f9bd85c37df351e24bac60caa205783664aa6aa9793823ce6eb5c94e74a5178` | 972,416 | 1,298,041 | 1,304,529 | 1,345,443 | 8,659 |
| B2 | `7456a8223f604cad825236738e2b6d34bb50d0a4073785fe78ecc2d58007976e` | 972,160 | 1,308,867 | 1,315,355 | 1,356,269 | −2,167 |
| R1 = A1 + B1 + B2 | `6f28d940f220b1ec3a123a7ee1e7e36fce782704621ef22017eec20ebba5094d` | 973,008 | 1,300,260 | 1,306,659 | 1,347,908 | 6,194 |
| R1 with the SDK `hashv` in `digest_into` (information only) | `0f29a01486d458e0faa448ecb276dbf85f91dec2f205cb29836ca7d56c5ee93d` | 973,096 | 1,323,750 | 1,329,825 | 1,372,127 | −18,025 |

The X1 row of the worst-case run reproduces `w3.json` exactly (1,354,102, and 1,350,005, 1,352,487 for
the other two marker states). For every build, all four runs of the worst-case scenario end as expected
(the three marker states settle with the expected lane, page, next page, marker and token movement; the
run one unit below its own cost fails with `ProgramFailedToComplete` and changes nothing but the
payer's fee), both replays complete with the control's final state, the changed certificate and the
pinned-format buffer are rejected with no state change, and the four redirect attempts are rejected
cleanly with the honest payment settling to the recorded destination.

Against the predictions (20:44:30Z):

| Candidate | Predicted | Measured | Verdict |
|---|---:|---:|---|
| A1 | 10,000 (3,000 to 20,000) | −1,470 | **miss**, wrong direction. One out-of-line copy with pointer arguments costs more than the unrolled inline copies with frame-relative addresses. Rejected |
| B1 | 8,000 (3,000 to 12,000) | 8,659 | in the band. Kept |
| B2 | 15,000 (−5,000 to 30,000) | −2,167 | **miss**, regression. Rejected. As in round 2 of the experiment, a limb product with its accumulator in memory costs about six instructions whatever the loop order |
| R1 | 30,000 (10,000 to 50,000) | 6,194 | **miss** (it carries A1 and B2) |

Round 1's best single candidate is B1 at 8,659, above the 5,000 stop line, so round 2 runs.

Gates on B1 (`fv_opt_gates.sh b1`, `fv_opt_xo.sh b1 src-opt-b1`):

- mutation campaign, deployed feature set, own target directory: verdict file byte-identical to X1's
  (`e3659a53d3b4e308711668d82715cd981e8d3bdc7ba859c9ff3bdaa1e3c9e2b9`, 156,706 lines);
- statement-binding and equivalence tests with the deployed feature set: 11 passed, 0 failed; the
  fused-verifier and multiproof library tests (kernel equivalence including
  `tight_lane_kernels_equal_the_first_kernels_on_arbitrary_and_edge_inputs`, the six fixtures, every
  region mutated, slot bounds): 21 passed, 0 failed;
- translator: Charon and Aeneas (second pair, XP-C12 roots and boundaries) list the same rejected
  functions as on the X1 source (the five known "Arrow types" signatures; only line numbers moved); the
  emitted Lean has the same four failing declarations as X1 (`base_lanes_tight` and the three
  `factored_s2_libra_weights` items, both known from the probe) out of 308; `base_fold`, its loop and
  loop body translate and elaborate.

### Round 2 predictions (written 2026-11-11T20:54:03Z, before any round-2 build)

| Id | Class | Candidate | Basis |
|---|---|---|---|
| C1 | V | The QM31 values of the three extension lanes read from their limbs without a second canonicality check (`scanned_k`); the canonical scan that runs first has already accepted exactly these bytes, as the base-lane kernel already relies on | 264 reads through the checked decoder at about 46 instructions each (the closure is 12,232 instructions in the profile) against about 8 |
| A2 | V | Merkle level loop with the next index carried from the step before (each index read once), still inlined | about 6 instructions of index reloads and address arithmetic per parent |
| R2 | V | B1 + C1 + A2 | |

| Candidate | Predicted saving, worst case | Band |
|---|---:|---|
| C1 | 8,000 | 3,000 to 12,000 |
| A2 | 3,000 | −2,000 to 9,000 |
| R2 = B1 + C1 + A2 | 19,500 | 10,000 to 30,000 |

Not attempted in round 2, with the reason: A3 (tag byte merged into the left input slice, about 10 CU
on roughly half the parent digests, so about 5,000) needs a 32-byte output buffer inside a 33-byte
record, which in safe Rust means converting `&mut [u8]` to `&mut [u8; 32]` (or `as_flattened`), the
conversion the translator's library has no model for (EXTRACTION-PROBE.md section 5, `base_lanes_tight`).

**Round 2, in-round correction (written 2026-11-11T20:58:35Z, after the C1 and A2 replays and before
any C1b build).** The two recorded replays of the first round-2 builds came back first: C1 costs 18,846
more than X1 on the transfer and 18,842 more on the withdrawal, a regression far larger than the reads
it removed. (This paragraph first said that A2 also cost 2,140 and 2,103 more. That was my misreading
of the sign: A2 costs 2,140 and 2,103 *less* than X1; corrected at 21:03Z, see the results below. A2 is
not rejected.) My reading of C1: `scanned_k` indexed a
variable-length slice byte by byte, so each of the 16 bytes of a value got its own bounds check and the
four bytes of a limb were not combined into one load. C1b is the same change written as the base-lane
kernel reads its limbs: each opening viewed once as `&[u8; 608]` (one length check per query, as
`base_accumulate` does with `&[u8; 480]`), the limb offsets then constant. This is a correction inside
round 2, not a third round.

| Candidate | Predicted saving, worst case | Band |
|---|---:|---|
| C1b | 6,000 | −3,000 to 11,000 |
| R2b = B1 + C1b | 14,500 | 6,000 to 20,000 |

**Round 2, final combination (written 2026-11-11T21:07:05Z, after the C1b replays and before the R2c
build).** C1b replays at 15,074 (transfer) and 15,078 (withdrawal) below X1, above its band. A2 is
cheaper than X1 by 2,140 and 2,103 on the replays and 2,246 at the worst case. The round's combined
patch is therefore R2c = B1 + A2 + C1b (R2 and R2b each lack one of the three).

| Candidate | Predicted saving, worst case | Band | Basis |
|---|---:|---|---|
| R2c = B1 + A2 + C1b | 26,000 | 22,000 to 28,000 | sum of the measured parts (8,659 + 2,246 + about 15,100), the three touching different loops |

## 3. Round 2 results

Host script `fv_opt_round.sh`, three invocations (`r2`: C1, A2, R2 and R2 with `hashv`; `r2b`: C1b,
R2b and R2b with `hashv`; `r2c`: R2c and R2c with `hashv`), receipts `OPT-B-*`, `OPT-R-*`, `OPT-RD-*`,
`OPT-W-r2`, `OPT-W-r2b`, `OPT-W-r2c`, all exit 0. Each worst-case run includes X1 again as its control,
and each reproduces X1's 1,354,102 exactly.

| Build | ELF sha256 | Bytes | Transfer | Withdrawal | Worst case, one-lamport marker | Saving at the worst case |
|---|---|---:|---:|---:|---:|---:|
| X1 | `7a77273b1dc64689a0eed1cc267c6e81c9f6d0ad2e17fe0be316243d3ae9a3d5` | 972,024 | 1,306,700 | 1,313,188 | 1,354,102 | |
| C1 | `57f686610f50a43bb2065ef91aed2c95b4973af486713ab25d4c9d345d113e05` | 972,680 | 1,325,546 | 1,332,030 | 1,372,956 | −18,854 |
| A2 | `f8d4ba304391e7bc00a415af353de2244583d1ace78494fb8fb198ebbf8685c0` | 973,728 | 1,304,560 | 1,311,085 | 1,351,856 | 2,246 |
| R2 = B1 + C1 + A2 | `8ea41f6e7db6254da78ef0f166812a83fd1dc5d4113c706b07b548aed0fa5a28` | 974,776 | 1,314,747 | 1,321,268 | 1,362,051 | −7,949 |
| C1b | `642cd2118c34e29114eb97a6812ec19cfc6ef6dda23b09cd8759ae5c5ebf2a84` | 970,544 | 1,291,626 | 1,298,110 | 1,339,016 | 15,086 |
| R2b = B1 + C1b | `98664c4f3889c8fb77ad13e7f3fc16b7de40fc36543214cacca92cca5bbbdae8` | 970,936 | 1,282,967 | 1,289,451 | 1,330,357 | 23,745 |
| **R2c = B1 + A2 + C1b** | `639642a06c0aeef10e8a9bb60660757febbf8df768d103504ec9a7a35916ff78` | 972,640 | **1,280,827** | **1,287,348** | **1,328,111** | **25,991** |
| R2 with `hashv` (information) | `d69f547ec558a915a4ed658d20901b16a8120c6c53e9ef8b3a0b55267903c2ff` | 975,712 | 1,341,112 | 1,347,271 | 1,389,245 | −35,143 |
| R2b with `hashv` (information) | `3f48d537df390bb10a49e86dfa059c7a9fbb4a85e4c56fb20abb7d72297a351f` | 971,456 | 1,307,585 | 1,313,729 | 1,355,746 | −1,644 |
| **R2c with `hashv` (information)** | `3953456a88cf9f0663207448c0ed917313b33faca174830e7f59d8c6788d749c` | 973,576 | 1,307,192 | 1,313,351 | **1,355,305** | −1,203 |

"With `hashv`" is the candidate source with `programs/r1-cost-probe/src/lib.rs` taken from X2 (the SDK
`hashv` call in `SolanaDigest::digest_into` in place of the direct `sol_sha256` call). These builds are
not candidates under rule 1; they show what the cleaner hash-call option costs on top of each candidate.

For every build in the table: the three marker states of the worst-case scenario settle with the
expected lane, page, next page, marker and token movement, the run one unit below its own cost fails
with no state change but the fee, both replays complete with the control's final state, the changed
certificate and the pinned-format buffer are rejected with no state change, and the four redirect
attempts are rejected cleanly.

Against the predictions:

| Candidate | Predicted | Measured at the worst case | Verdict |
|---|---:|---:|---|
| C1 (20:54:03Z) | 8,000 (3,000 to 12,000) | −18,854 | **miss**, regression. Rejected |
| A2 (20:54:03Z) | 3,000 (−2,000 to 9,000) | 2,246 | in the band. Kept |
| R2 (20:54:03Z) | 19,500 (10,000 to 30,000) | −7,949 | **miss** (carries C1) |
| C1b (20:58:35Z) | 6,000 (−3,000 to 11,000) | 15,086 | **miss**, above the band. Kept. My estimate of the checked decoder's cost per read was low: the replaced path was an outlined call per value with its own slice checks and an error branch |
| R2b (20:58:35Z) | 14,500 (6,000 to 20,000) | 23,745 | **miss**, above the band (carries C1b) |
| R2c (21:07:05Z) | 26,000 (22,000 to 28,000) | 25,991 | in the band |

The three kept parts add almost exactly: 8,659 + 2,246 + 15,086 = 25,991.

One defect of mine, found by the gates: the A2 differential test as first written used the `vec!`
macro, which this `no_std` crate does not import, so the library tests of A2 did not compile (receipt
`OPT-TL-a2`, exit 101). The test was corrected (`Vec::new` and `push`) in the A2 and R2c trees and
rerun (`OPT-TL2-a2`). The change is inside `#[cfg(all(test, feature = "prover"))]` and does not enter
the program; the R2c tree with the corrected test was rebuilt (`OPT-B2-r2c`) to confirm the measured
ELF (result in section 4). The R2 and R2 `hashv` patches keep the uncorrected test; they are rejected.

## 4. Outcome

| | Heaviest measured | Allowance | Worst case | Headroom under 1,400,000 |
|---|---:|---:|---:|---:|
| X1 (baseline) | 1,354,102 | 10,697 | 1,364,799 | 35,201 |
| After round 1 (B1) | 1,345,443 | 10,697 | 1,356,140 | 43,860 |
| After round 2 (R2c = B1 + A2 + C1b) | 1,328,111 | 10,697 | **1,338,808** | **61,192** |
| R2c with `hashv` (information) | 1,355,305 | 11,036 | 1,366,341 | 33,659 |
| X2 (X1 with `hashv`, for comparison) | 1,379,491 | 11,036 | 1,390,527 | 9,473 |

The allowance is kept at X1's (and X2's) value. Its parts are the 12-digest gap at the fitted
per-digest slope, the insertion-sort and sampler instruction-count estimates and the fit residual; none
of the changed functions is the sort or the sampler, and A2 lowers the per-digest cost slightly, so
keeping the old figure is on the high side. The slope was not refitted for R2c.

Recovered at the worst case: **25,991**, against the 25,000 asked for. With R2c and the SDK `hashv`
call together, the heaviest measured payment is 1,355,305, which is 1,203 above X1's 1,354,102 and
24,186 below X2's 1,379,491; worst case 1,366,341 against X1's 1,364,799.

Provenance of every function R2c changes (soundness lead's rule: functions settled or translatable as
is at the pin c7593d23fdc must stay byte-identical). Checked with `git show c7593d23fdc:<file>`:

| Part | File | Function | Exists at c7593d23fdc | Row in ONCHAIN-PATH-EXTRACTION-STATUS-20261111.md |
|---|---|---|---|---|
| B1 | `crates/aspis-r1-cost-probe/src/fused.rs` | `base_fold` | no (the file does not exist at the pin) | none |
| C1b | same | `extension_lane` (changed), `scanned_k` (new), one new test | no | none |
| A2 | `crates/aspis-r1-cost-probe/src/multiproof.rs` | `merged_level` (changed), one new test with two test helpers | no: the file exists at the pin, but neither `merged_level` nor `verify_counting_merged` is in it | none |

No settled or translatable-as-is R1 function changes text. `fast_pairing.rs`, `fast_dots.rs`,
`weights.rs`, `verifier.rs`, `r1_wire.rs`, `candidate.rs` and `aspis-core` are untouched.

Gates on R2c at the time of reporting (2026-11-11, about 21:35Z): replays, redirect attempts and the
worst-case runs as above, all as expected. The parts were gated separately: B1, A2 and C1b each give a
mutation verdict file byte-identical to X1's (`e3659a53d3b4e308711668d82715cd981e8d3bdc7ba859c9ff3bdaa1e3c9e2b9`);
statement-binding and equivalence tests 11 of 11 for each; library tests 21 of 21 (B1), 22 of 22 (A2,
after the test fix, including `merged_traversal_equals_the_reference_on_random_sets`), 22 of 22 (C1b,
including `scanned_extension_values_equal_the_checked_decoder_on_canonical_openings`). Translator:
B1, A2 and C1 (same functions as C1b, first form) give the same Aeneas rejections and the same four
failing Lean declarations as X1; `base_fold`, `merged_level` and `scanned_k`'s caller `extension_lane`
translate and elaborate. Gates on the combined R2c tree, all finished: mutation verdict file byte-identical to X1's
(`OPT-MU-r2c`); statement-binding and equivalence tests 11 of 11 (`OPT-T-r2c`); library tests 23 of
23 including both new equivalence tests (`OPT-TL-r2c`); translator (`XO-*-r2c`, the run that covers
C1b's final text): same Aeneas rejections as X1, 309 Lean declarations with the same four failing as
X1, and `scanned_k`, `extension_lane`, `base_fold` and `merged_level` translate and elaborate. The
rebuild of the R2c tree with the corrected test (`OPT-B2-r2c`, exit 0) gives the measured ELF
`639642a06c0aeef10e8a9bb60660757febbf8df768d103504ec9a7a35916ff78` again.

Recommendation (not adopted by me): R2c is implementation only, Aspis-only code, same verdicts on the
campaign for each part, and brings the hash-call choice to a wash: with R2c, the SDK `hashv` route costs
1,203 more than X1 does today at the heaviest measured payment. Not recommended: A1, B2, C1 (measured
regressions), A3 (needs a std model for a mutable slice-to-array conversion), Xp (not the same
function), and anything touching the transcript or the statement crate (shared with the prover). The
larger lever is the Pool's zero check (section 5), which is the owner's decision.


## 5. The Pool (P1): sized, not implemented

From the Pool's register trace of the worst-case withdrawal (`OPT-pool-loops-1`, `fv_opt_loops.py`
over the deployed Pool ELF `e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc`, which
has no symbols, so loops are found as runs of equal execution counts): the Pool executes 112,505
instructions, and one loop of 8 instructions runs exactly 8,256 times, once per byte of the next
history page. That is the rollover's zero check of the fresh page,
`pair_forest.rs` 806-815 (`account_is_zeroed_program_page`, `iter().all(|byte| *byte == 0)`), called at
1277 for the next page (and at 1032 and 1233 for the genesis path). It costs **66,048 CU, 47% of the
Pool's own cost at the worst case** (140,305 with the one-lamport marker). The strict decode of the 256
roots of the full current page costs about 12,500 more (305 digest decodes of 28 instructions, 256 loop
steps of 15).

On a same-page payment the same kind of loop scans the unused tail of the current page,
`history.rs` 166 (`data[unused_start..].iter().any(|byte| *byte != 0)`), which is about 8,000 bytes on a
young page. Not traced; from the measured Pool costs in WORST-CASE-COMPUTE.md, filled 4 against filled
255 differs by 38,226, to which the decoding of 251 more roots in the fuller page adds about 10,800 by
the rule above, so the tail scan on a young page is roughly 38,000 to 49,000.

Smallest change that would remove most of it (information for the owner; Pool source not touched):

| Option | Change | Estimated cost of an 8,256-byte check | Estimated saving at the worst case |
|---|---|---:|---:|
| P1a | in `account_is_zeroed_program_page` and at `history.rs` 166, compare the bytes eight at a time (`chunks_exact(8)`, one `u64` test each) | about 5,000 (1,032 words at about 5 instructions; not measured) | about 61,000 |
| P1b | the same two places, as `data[0] == 0 && data[..len - 1] == data[1..]` (every byte equals its successor and the first is zero, so all are zero), which compiles to one `sol_memcmp_` call charged max(10, length / 250) | about 50 (33 for the syscall plus setup; not measured) | about 66,000 |

Both are the same predicate on every input. Either changes the Pool ELF, so the Pool's deployment and
its proofs (the probe found `history::validate_root_page_bytes` untranslatable as written, section 8 of
EXTRACTION-PROBE.md) would have to be redone; P1b also brings in `sol_memcmp_` as a trusted runtime
item. With P1 the rollover would stop being the heaviest Pool path: the young same-page payment
(109,865 before, about 38,000 to 49,000 of it in the tail scan) would lose about the same amount, and the
worst case would move by roughly 60,000 to 66,000, more than twice this exercise's target. Not measured.
