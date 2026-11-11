# One-transaction verification: measured experiment, 11 November 2026

Status: experiment on branch `future-version`. Nothing here is adopted, proved
or part of the pinned R1 verifier. The pinned entrypoints (`tx1`, `tx2`,
`tx2_authenticated`) and the Pool release surface are unchanged; every new code
path is reachable only from a measurement build without `pool-adapter`.

Result against the target: **one transaction is not established.** The best
measured verifier is about 1.60M CU before the Pool and adapter are added,
against a transaction limit of 1.40M.

Criteria were not pre-registered before these measurements were taken. The only
gate applied is the external one (does the invocation complete inside
1,400,000 CU). The numbers below are measurements on six saved fixtures, not
all-input bounds; the 20 October all-input argument put its bounds 7 to 8%
above the fixture maxima.

## What was built

Base: `d7142292c48` (the PIN2 pin `c7593d23fdc` plus its tools). The published
`main` branch was tried first and cannot be used as a development base: it
lacks `tools/r1-cost-probe`, the prover's included research files and
`refine/diffharness/tests/glue_gen.rs`, so host builds of `aspis-statement`
fail there.

- `crates/aspis-r1-cost-probe/src/fused.rs`
  - `verify` (stage A): the pinned checks of `tx1` then `tx2` in one
    invocation, with no checkpoint.
  - `verify_batched` (stage C): the second fold rearranged exactly, and the 22
    first-fold equalities replaced by one equality batched with the existing
    challenge `rho`, accumulated in QM31 before any WideExact product.
  - `input_evaluation_probe`, `unit_cost_probe`, `relation_probe`: cost probes
    that verify nothing.
- `fast_pairing.rs`: `KbyKDot`, `k_mul_sixteen` (additive).
- `weights.rs`: `pair_marked`, profiling builds only.
- `aspis-core`: default-off feature `future-fast-kmul`, which replaces the body
  of `QM31::mul` (nested Karatsuba) by the sixteen-product form with one
  reduction per limb. Same field product.
- `programs/r1-cost-probe`: measurement tags 8 (fused), 9 (batched), 10, 11, 12
  (probes) on the three-account entry. The Pool surface rejects them.
- `tools/r1-cost-probe/src/bin/fused_probe.rs`: LiteSVM driver.
- `docs/research/future-version/lean/TwoFamilyResidualBatch.lean`.

## Totals

Verifier program CU, LiteSVM 0.16.0 / Agave 4.2.1, `cargo-build-sbf` 3.1.13
with platform-tools v1.52, build without `pool-adapter` and without profiling
markers. "Pinned" is stage 1 plus stage 2 at the real 1.4M limit; the fused
rows are diagnostic runs at an elevated limit, and each was also run at the
real limit, where none completes.

| Fixture | Pinned stage 1 | Pinned stage 2 | Pinned sum | Fused | Fused + batched |
|---|---:|---:|---:|---:|---:|
| transfer-13 | 1,206,856 | 1,027,069 | 2,233,925 | 2,090,624 | 1,860,972 |
| transfer-255 | 1,207,902 | 1,029,884 | 2,237,786 | 2,094,461 | 1,864,886 |
| transfer-1023 | 1,204,474 | 1,030,753 | 2,235,227 | 2,091,942 | 1,862,357 |
| withdrawal-13 | 1,208,933 | 1,025,398 | 2,234,331 | 2,091,035 | 1,861,214 |
| withdrawal-255 | 1,204,870 | 1,031,004 | 2,235,874 | 2,092,549 | 1,862,728 |
| withdrawal-1023 | 1,204,834 | 1,030,652 | 2,235,486 | 2,092,185 | 1,862,481 |

The same with `future-fast-kmul`:

| Fixture | Pinned stage 1 | Pinned stage 2 | Pinned sum | Fused | Fused + batched |
|---|---:|---:|---:|---:|---:|
| transfer-13 | 1,051,484 | 824,566 | 1,876,050 | 1,747,872 | 1,602,695 |
| transfer-255 | 1,052,613 | 827,406 | 1,880,019 | 1,751,838 | 1,606,608 |
| transfer-1023 | 1,049,137 | 828,244 | 1,877,381 | 1,749,201 | 1,604,063 |
| withdrawal-13 | 1,053,451 | 822,845 | 1,876,296 | 1,748,118 | 1,602,820 |
| withdrawal-255 | 1,049,472 | 828,263 | 1,877,735 | 1,749,559 | 1,604,268 |
| withdrawal-1023 | 1,049,494 | 828,115 | 1,877,609 | 1,749,430 | 1,604,178 |

For comparison, the devnet run of 11 November recorded 1,211,602 (stage 1) and
1,043,169 (stage 2) for the deployed verifier through its adapter, and Pool
settlement of 96,703 (transfer) and 106,104 (withdrawal) on top of stage 2. A
fused Pool path was not built. Adding the adapter and Pool overheads observed
on devnet (about 120k) to the best measured core gives a projection of about
1.72M, roughly 320k over the limit.

Differences:

| Change | Saving | Kind |
|---|---:|---|
| Fusion (no checkpoint, one parse, one geometry batch) | about 143k | exact |
| Sixteen-product `QM31::mul` on the pinned pair | about 358k (155k stage 1, 202k stage 2) | exact |
| Batched first fold and rearranged second fold, Karatsuba kernel | about 230k | changes the acceptance predicate |
| The same with the fast kernel already in | about 145k | changes the acceptance predicate |

## Phase profile

Profiling build with `detail-phases`, transfer-13; markers add a few thousand CU
in total. Intervals in CU.

| Phase | Fused, pinned kernel | Fused, fast kernel | Fused + batched, fast kernel |
|---|---:|---:|---:|
| Entry, statement decode, shape and canonical scan | 25,934 | 25,936 | 25,934 |
| Semantic: expansion and prefix parse | 22,542 | 22,542 | 22,541 |
| Semantic: public transcript and first challenges | 19,021 | 19,021 | 19,021 |
| Semantic: ten sumcheck rounds | 131,291 | 85,633 | 85,633 |
| Semantic: claims and terminal evaluation | 376,095 | 332,762 | 332,762 |
| Semantic: mask value and terminal equality | 16,232 | 15,549 | 15,549 |
| Semantic: circle challenges | 10,254 | 9,540 | 9,540 |
| Preparation (challenges, queries, gamma powers, claim) | 116,267 | 92,593 | 92,585 |
| Merkle, queries 0..10 | 129,185 | 129,185 | 129,182 |
| Merkle, queries 10..22 | 149,781 | 149,781 | 149,781 |
| 22 queries | 704,000 | 612,834 | 464,055 |
| Relation | 384,434 | 246,317 | 242,212 |
| Final dot product | 21,441 | 21,441 | 21,441 |
| Total | 2,106,704 | 1,763,361 | 1,610,462 |

The batched query phase splits into: geometry inversion and coefficients
37,505; the 26 base-field lanes 164,129; the three QM31 lanes and the first
cubic 86,803; the second fold and the right-hand sum 67,482; the final-weight
accumulation 108,136.

The relation phase with the pinned kernel splits into: two round checks 19,551;
`Weights::new` 36,711; fold powers 8,464; the three regular rows 166,857; the
two shared-point rows 46,508; the inactive row 58,780; the Libra row 30,668;
kappa powers and sum 17,487. With the fast kernel the same eight are 11,591,
18,325, 4,945, 110,713, 35,087, 39,993, 16,965 and 9,456.

Unit costs, 512 chained operations each, loop overhead included:

| Operation | Pinned kernel | Fast kernel |
|---|---:|---:|
| `QM31::mul` | 320 | 136 |
| `WideExact::mul` | 1,157 | 584 |
| `WideExact::mul_qm31` | 639 | 289 |
| `M31::mul` | 21 | 20 |
| Sixteen-product multiplication with both operands checked | 151 | 155 |

The two dot-accumulator rows of that probe pushed loop-invariant operands and
were hoisted by the compiler; they are not unit costs and are not used.

## The multiplication kernel

`QM31::mul` is nested Karatsuba: nine M31 products, each reduced separately,
with canonical additions and subtractions between them. On SBF every
instruction costs one unit, so saving multiplications at the price of extra
additions, branches and reductions loses. The sixteen-product form with one
reduction per output limb is the multiplication the verifier crate already
uses inside its private dot accumulators (`canonical::Q::mul`).

The change is one function body. It is exact: `future_fast_kmul_tests` compares
it with the Karatsuba form on 20,000 edge and random operand pairs, the 280
`aspis-core` library tests and the 25 verifier library tests pass with the
feature on, and all six fixtures are accepted on chain in every mode by the
ELF built with it. Its overflow bound is stated for canonical limbs, as is the
Karatsuba form's (its `CM31::mul` multiplies two unreduced sums on the same
assumption), so the precondition is of the same kind, but the proof that no
intermediate wraps is a new one.

It is a change to frozen `aspis-core` source and so to the pin, the ELF and the
source-level proofs that mention `QM31::mul`, `CM31::mul` and
`WideExact::mul`. That is an owner decision. It is independent of the
one-transaction question: applied to the deployed two-transaction verifier it
lowers stage 1 from about 1,207k to 1,051k and stage 2 from about 1,027k to
825k.

## Stage C: what changes and what it rests on

For query `i`, write `F_i` for the pinned first fold of the gamma-combined
opening, `b_i` for the authenticated folded value it must equal, `G_i` for the
pinned second fold and `e_i` for the final polynomial at the query's node. The
pinned verifier checks `F_i = b_i` for each `i` and
`sum_i rho^i (e_i - G_i) = 0`. Stage C checks

    sum_i rho^i (F_i - b_i) = 0   and   sum_i rho^i (e_i - G_i) = 0

as two separate equalities. The second is the pinned check with its sums
reordered. The first is new: a proof whose first-fold residuals are nonzero and
vanish at `rho` is accepted by stage C and rejected by the pinned verifier. The
test `rho_dependent_cancellation_passes_the_batched_check_and_fails_the_pinned_one`
constructs such data for a known `rho`, and shows it is rejected at a different
challenge.

The argument for keeping the bound is that both residual vectors are functions
of committed data and of challenges drawn before `rho` (the transcript derives
the queries from the final message and then `rho`; `Prepared::new`). If either
vector is nonzero, take the first whose polynomial is nonzero; acceptance
requires `rho` to be one of its at most 21 roots in QM31. So the pair has at
most 21 bad challenges, not 42, and the `rho` row keeps its cap
`21 * ceil(2^256/|K|)/2^256`.

Proved here, algebra only: `bad2_card_le_21` and
`all_zero_of_both_evals_zero_outside_bad2` in
`lean/TwoFamilyResidualBatch.lean`. The bad set is a function of the two
vectors alone; outside it, the two batched equalities imply all 44 coordinate
equalities. Compile: `lake env lean -M7000` on that one file in `AspisFormal`
(Lean 4.32.0, prebuilt Mathlib), exit 0, 1.98 s wall, 1,772,290,048 bytes peak
RSS, swap not measured on the Mac, source revision the commit that adds this
note; `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` for
both.

Not proved, and required before any claim:

1. The `rho` row now depends on the binding of the C1 and C2 trees as well as
   the folded tree, because the first-fold residual reads all three. No new
   numerical term is expected (the same binding event is already charged), but
   the row's hypotheses change and its bridge theorem
   (`QueryResidualBridge`) has to be restated for two families.
2. The Fiat-Shamir placement: one `rho` per transcript prefix, with the pair of
   residual vectors determined by that prefix.
3. Source correspondence of the new kernels. None of the existing source-level
   proofs of `four_dots`, the circle fold or the query loop applies to them.
   The base-lane kernel also reads M31 limbs without re-checking them and
   relies on the canonical scan of the same buffer in the same invocation.
4. The all-input cost argument.

Stage C does not change the proof bytes, the prover or the transcript.

## The certificate proposal

The second proposal was one sumcheck or GKR certificate for all of the
verifier's public arithmetic, with the semantic layer included. Three
measurements bear on it.

First, the certificate verifier has to evaluate its public input itself.
`input_evaluation_probe` measures the cheapest form of that for the openings
and the final message only (2,288 M31 values, 264 QM31 values, 152 WideExact
values as QM31 coordinates, product-form QM31 weights): about 154k to 155k CU
for the kernel, plus 18,228 (fast multiplication) or 38,667 (pinned) for the
weight tables. It does not cover the semantic prefix or the public
statement. It has the same multiplication count (9,152 limb products for the
base lanes) as stage C's direct check of the batched first fold, so on the
query region a certificate cannot cost less than checking directly.

Second, the semantic terminal is 333k to 376k of straight-line evaluation of
the constraint composition at one point. Its wiring is irregular. A GKR
verifier pays for wiring it cannot evaluate in closed form, on the order of the
circuit size, unless the wiring is committed in advance, which is a second
proof system.

Third, proof size. The 16 upload transactions are full except the last, which
has about 1.9 KB free. Each further 3.8 KB of certificate is one more upload
transaction; a certificate of a few hundred rounds is 10 to 20 KB. The
certificate would add more transactions than the one it removes.

On these grounds the certificate is not pursued. The terminal-relation sumcheck
of the first proposal (six rounds, about 576 bytes, fits in the free space)
remains a possible local experiment on a 242k phase; it adds Fiat-Shamir rows
and a prover change, and was not built.

## Where this leaves the one-transaction target

With every measured change applied, the verifier core is about 1.60M. The
remaining phases are the semantic layer (485k, of which the terminal 333k),
the batched queries (464k), Merkle authentication (279k), the relation (242k),
preparation (93k) and parsing (26k). The limit, less the Pool and adapter, is
about 1.28M, so about 320k more would have to go on fixtures, and more than
that for an all-input bound.

Estimates, not measurements, of what is left: tightening the stage C kernels
(the base-lane kernel spends about three times the probe's tight loop per
product) perhaps 100k to 130k; decoding the final message once and the
terminal-relation sumcheck perhaps 60k to 100k; one 22-query multiproof per
tree in place of two perhaps 20k to 40k, with a format change. That does not
reach 320k without a large reduction in the semantic terminal, which has not
been profiled internally. Earlier analytical cost estimates in this project
have run low, so none of these should be relied on before measurement.

The exact changes are worth more to the deployed two-transaction design than
to this target: the multiplication kernel alone gives each transaction 155k to
202k of headroom.

## Reproduction

Host workspace `/home/dombarker/project-offloads/future-version-20261111`
(source snapshots by rsync of this worktree; scripts in
`evidence/future-version-20261111/host/`). Every build and run was one systemd
scope with `MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`; admission
required fewer than five other scopes and a summed `MemoryMax` of at most
55 GiB. All scopes exited 0 with zero swap.

| ELF | Source | Features | SHA-256 | Build wall, peak |
|---|---|---|---|---|
| B1-plain | `44751d4afe7` | `private-leaf-salts` | `b56c79f8…34ac726` | 48.0 s, 1.45 GB |
| B2-profile | `44751d4afe7` | + `cu-profiling` | `d4ee5750…7af1aff` | 2.8 s, 0.13 GB |
| B3-detail | `44751d4afe7` | + `detail-phases` | `f3730f18…41320f7` | 8.6 s, 0.17 GB |
| B4-detail2 | `d5f46723c61` | as B3 | `53b445be…f7712bc` | 6.6 s, 0.17 GB |
| B5-plain2 | `d5f46723c61` | as B1 | `50b0f399…2474f38` | 6.6 s, 0.17 GB |
| B6-plain-fastk | `9c82845beab` | B1 + `future-fast-kmul` | `2aeb5c5d…ca73b67` | 22.9 s, 1.01 GB |
| B7-detail-fastk | `9c82845beab` | B3 + `future-fast-kmul` | `783b77ba…e5b5819` | 5.3 s, 0.16 GB |

The driver was built with Rust 1.94.1, `--release --offline --locked`
(1 min 57 s, 2.19 GB peak). Build command, per `docs/r1/BUILD.md` without
`pool-adapter`:

    cargo-build-sbf --manifest-path programs/r1-cost-probe/Cargo.toml \
      --sbf-out-dir <out> --features <features> \
      --skip-tools-install --offline -j 4 -- --locked

Run: `fused_probe <elf> <proof> <public> <out.json> <label>` on the fixtures in
`docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/`.
The JSON records, receipts and exact environments are in
`evidence/future-version-20261111/`.

Host tests:

    cargo test -p aspis-r1-cost-probe --release --offline --lib \
      --features detail-phases fused
    cargo test -p aspis-core --release --offline --lib \
      --features r0,future-fast-kmul

Nine fused tests pass: the three verifiers accept the six fixtures and reject
the same 20 single-byte mutations; the batched sums equal the pinned per-query
kernels on 40 random and edge cases and on maximal limbs; the batched equality
alone rejects single opening changes; the cancellation vector; the probes equal
their naive forms.

## Round 2: pre-registration (written and committed before any round-2 measurement)

Round 1 above was measured without pre-registered criteria. This round fixes
them first.

**Question.** How much of the remaining cost is removable by exact changes
(same acceptance predicate, same proof bytes, same hash inputs in the same
order), and does that, with the batched first fold, bring the verifier inside
the one-transaction budget?

**Baseline W0.** Fused + batched + `future-fast-kmul`, ELF B6
(`2aeb5c5d…ca73b67`, source `9c82845beab`): 1,602,695 to 1,606,608 CU on the
six fixtures. Every saving in this round is measured against W0, cumulatively,
not against the deployed verifier.

**Budget lines.** Verifier core at most 1,275,000 CU (the 1.4M limit less
125,000 for the Pool and adapter) and at most 1,175,000 (a 1.3M target), on
all six fixtures.

**Inventory first.** One register trace of W0 per fixture for transfer-13 and
withdrawal-255, with executed instructions attributed to source lines of an
ELF whose instruction stream is identical to B6's. The inventory is used only
if at least 95% of executed instructions map to a source line and the
instruction count plus the syscall charge reproduces the program CU.

**Candidates.** All exact:

- E1: `PreparedQm31Multiplier::mul` through the sixteen-product kernel.
- E2: `QM31::square` through a delayed-reduction form.
- E3: decode already-validated semantic records without re-validating.
- E4: one Merkle traversal per tree (count while verifying, zero check after)
  and one index schedule shared by C1 and C2.
- Any further exact candidate the inventory exposes. Each is added to this
  list, with its predicted saving written as executions times saving per
  execution less new overhead, before its ELF is measured.

**Keep or drop.** Candidates are applied cumulatively in the order listed. One
is kept if it lowers program CU by at least 3,000 on every one of the six
fixtures, and dropped on a smaller saving or a regression. A kept candidate
must also pass the existing host tests with its feature on, an equivalence
test against the form it replaces on edge and random inputs, and acceptance of
the six fixtures with rejection of the 20 mutations.

**Outcome wording, fixed now.** If the final cumulative build exceeds
1,275,000 on any fixture: "one transaction is not supported by exact changes
plus batching", with the measured gap. If it is within 1,275,000 on all six:
"fits the hard-cap budget on six fixtures", which is still not an all-input
bound and not a release claim. Only measured savings count; no estimate is
added to a total.

### Round 2: inventory result and candidate predictions (committed before the candidates' ELFs are measured)

**Deviation from the pre-registration.** The debug-line build B8 (same source
and features as B6, plus `CARGO_PROFILE_RELEASE_DEBUG=line-tables-only`, own
target directory) does not have B6's instruction stream: its `.text` is 864
bytes longer and its stripped hash is `d7021af9…e1e9e3d9`. The inventory is
therefore of B8 itself (traced and symbolised against its own unstripped ELF),
whose program CU is 1,601,929 on transfer-13 against B6's 1,602,695, a
difference of 766. It is used for attribution only. All totals and all
keep-or-drop decisions are measured on builds without debug information.

**Inventory, transfer-13, batched (tag 9).** 1,442,577 executed instructions
and 159,352 CU of syscall charges (1,540 syscalls: 1,098 SHA-256 calls, 354
`memcpy`, 80 `memset`, 8 others); 100% of instructions map to a source line.
Inclusive instruction counts of the outlined functions: semantic layer 457,016
(terminal 326,803; ten rounds 76,178); batched folds 336,776; relation
263,215; Merkle 145,843; final-weight accumulation 101,588; preparation
84,833. By source file, `aspis-core/src/field.rs` is 550,423 of the
instructions: canonical M31 addition 144,428, subtraction 66,164, the
reduction routine about 141,000.

**Predictions** (executions times saving per execution, less overhead; every
one is an estimate to be replaced by a measurement):

| Candidate | Basis | Predicted saving |
|---|---|---:|
| E1 prepared multiply | about 270 calls, nested form about 250 against about 136 | 30k |
| E2 square | 162 calls, about 226 against about 110 | 16k |
| E3 validated decode | 426 values, about 18 against about 6 | 5k |
| E4a Merkle: count while verifying | `node_count` is 36,401 instructions in six calls | 36k |
| E4b Merkle: digest written in place, pair test and sibling read tightened | about 880 parents at about 81 instructions | 20k |
| E5 base-lane kernel | 572 lane-query steps at 232 instructions; the probe's loop is 94 | 50k |
| E6 QM31-lane kernel on raw limbs with one reduction | 264 products at about 248 | 30k |
| E7 final-weight accumulation | 101,478 instructions for 5,632 limb products and 1,386 M31 products | 40k |
| E8 semantic boundary sum with one reduction | 280 QM31 additions at about 39 | 9k |
| E9 final message decoded once for relation and final check | about 256 repeated WideExact decodes at about 38 | 9k |

Sum of predictions: about 245k, which would put the verifier near 1.36M. That
is above the 1,275,000 line, so the predicted outcome is "not supported by
exact changes plus batching". E5, E6 and E7 change only this branch's own
stage C kernels; the others change pinned source behind default-off features.
Candidates are measured in the order E1, E2, E3, E4a, E5, E6, E7, E8, E9, E4b.

### Round 2: results

**Outcome, in the wording fixed beforehand: one transaction is not supported
by exact changes plus batching.** The final cumulative build is 1,438,749 to
1,442,350 CU on the six fixtures, 163,749 to 167,350 above the 1,275,000 line.

Cumulative program CU of the batched verifier (builds without profiling or
debug information; source `f764b9f3167` for W1 to W3 and `b6dfdb9d58b` after):

| Build | transfer-13 | transfer-255 | transfer-1023 | withdrawal-13 | withdrawal-255 | withdrawal-1023 | Saving on the previous build |
|---|---:|---:|---:|---:|---:|---:|---:|
| W0 (B6) | 1,602,695 | 1,606,608 | 1,604,063 | 1,602,820 | 1,604,268 | 1,604,178 | |
| W1 = W0 + E1 | 1,542,489 | 1,546,726 | 1,544,310 | 1,543,133 | 1,544,721 | 1,544,765 | 59,413 to 60,206 |
| W2 = W1 + E2 | 1,523,799 | 1,528,045 | 1,525,633 | 1,524,421 | 1,526,025 | 1,526,056 | 18,677 to 18,712 |
| W3 = W2 + E3 | 1,507,796 | 1,512,042 | 1,509,630 | 1,508,418 | 1,510,022 | 1,510,053 | 16,003 |
| W4 = W3 + E4a | 1,470,304 | 1,473,877 | 1,471,864 | 1,470,658 | 1,471,980 | 1,472,037 | 37,492 to 38,165 |
| W5 = W4 + E5 | 1,462,716 | 1,466,289 | 1,464,290 | 1,463,080 | 1,464,390 | 1,464,451 | 7,574 to 7,590 |
| W6 = W5 + E6 | 1,467,684 | 1,471,220 | 1,469,252 | 1,468,015 | 1,469,358 | 1,469,366 | regression of 4,915 to 4,968 |
| W7 = W6 + E7 | 1,451,851 | 1,455,387 | 1,453,419 | 1,452,182 | 1,453,525 | 1,453,533 | 15,833 |
| W8 = W7 + E8 | 1,443,717 | 1,447,281 | 1,445,305 | 1,444,050 | 1,445,390 | 1,445,395 | 8,106 to 8,138 |
| W9 = W8 without E6 | 1,438,749 | 1,442,350 | 1,440,343 | 1,439,115 | 1,440,422 | 1,440,480 | |

| Candidate | Predicted | Measured | Decision |
|---|---:|---:|---|
| E1 prepared multiply | 30k | 59.4k to 60.2k | kept |
| E2 square | 16k | 18.7k | kept |
| E3 validated decode | 5k | 16.0k | kept |
| E4a Merkle single traversal | 36k | 37.5k to 38.2k | kept |
| E5 base-lane kernel | 50k | 7.6k | kept |
| E6 QM31-lane kernel | 30k | regression of 4.9k | dropped |
| E7 final-weight accumulation | 40k | 15.8k | kept |
| E8 boundary sum | 9k | 8.1k | kept |
| E9 final message decoded once | 9k | not implemented | not measured |
| E4b Merkle parent loop | 20k | not implemented | not measured |

The predictions for the pinned-source candidates were low or close; the
predictions for this branch's own kernels (E5, E6, E7) were high by a factor
of two to six. A limb product with its accumulator in memory costs about six
instructions on SBF whatever the loop shape, which the predictions for E5 and
E7 did not allow for. E7 was measured on top of E6 and W9 confirms that
removing E6 returns exactly its regression. E9 and E4b were not built; their
predictions sum to 29k, which would not change the outcome.

W9 is ELF `52b05716…c229e19`. Every build accepted all six fixtures in the
pinned, fused and batched modes. Host tests with every kept feature on: 30
verifier library tests and 281 `aspis-core` library tests pass, including one
equivalence test per candidate against the form it replaces (60,000 operand
pairs for E1 and E2; every validated semantic value of every fixture for E3;
every slot of every fixture under a changed node, changed padding, both, a
short slot and a malformed index set for E4a, with the error kind compared;
30 random and edge cases plus maximal limbs for E5; all fixtures for E7;
2,000 polynomials for E8). `aspis-statement` has 258 passing tests and one
failure, `format_binding_pins_existing_primitives`, which fails identically at
the pin without any feature of this branch.

**The same build on the pinned mathematics** (E1 to E3, E4a and E8 apply to
it; E5 and E7 do not):

| | Stage 1 | Stage 2 | Sum | Fused, pinned mathematics |
|---|---:|---:|---:|---:|
| Deployed (B1) | 1,204k to 1,209k | 1,025k to 1,031k | 2,234k to 2,238k | 2,091k to 2,094k |
| All kept exact changes (W9) | 931k to 935k | 804k to 808k | 1,738k to 1,742k | 1,610k to 1,614k |

So the exact changes alone take about 496k (22%) off the two-transaction
verifier with no change to what it accepts.

**Inventory of W9** (debug-line build of the same features, transfer-13,
1,278,574 instructions and 159,365 CU of syscall charges). Inclusive
instructions: semantic layer 354,633 (terminal 254,444, of which the copy
terminal 116,953 and Poseidon 49,032; ten rounds 57,583); batched folds
326,236 (base lanes 123,266); relation 262,545; Merkle 111,046 plus 21,960 in
the SHA wrapper; final-weight accumulation 85,972; preparation 84,833. By
source file, `field.rs` is still 448,976 instructions: canonical addition
about 103k, subtraction about 32k, reductions about 119k. What remains is
spread over many small kernels; no single exact change of the size of E1 or
E4a is visible in it.

**Reading.** After this round the verifier is 1.44M, or about 1.56M with the
Pool and adapter, against 1.40M. Closing the remaining 165k with further exact
changes would mean rewriting the terminal's arithmetic to carry unreduced
sums, which is a change to about 2,500 lines of pinned statement code, with
no measured basis yet for its yield. The one non-exact candidate with a
budget of the right size is the terminal-relation sumcheck (the relation is
262k instructions). Neither has been measured, so neither is counted.

## Round 3: one verifying transaction (owner direction, 11 November: push for a single transaction that does all verification)

### Stage D: one sumcheck over the final message (design and pre-registration, committed before the code)

**What it replaces.** After the two relation round checks the pinned verifier
makes two checks against the 64 final-message values `f_j`:

- the relation pairing `sum_j f_j W_j = claim`, where `W_j` is the folded
  weight vector of the seven functionals combined with powers of `kappa`
  (`Weights::pair`, about 213k instructions);
- the query check `sum_j f_j w_j = rhs`, where `w_j = sum_i rho^i b_j(x_i)` is
  accumulated over the 22 queries (about 86k) and then contracted (about 18k).

Both are inner products of `f` with a public, structured vector. Stage D proves
both with one six-round sumcheck over the 64 coefficient positions.

**Protocol addition.** After `rho`, on a transcript seeded from the post-`rho`
state (new rows 33 to 39, domain-separated by the existing row byte):

1. Row 33 absorbs the two claimed sums (`claim` and the batched second-fold sum
   `rhs2`, 64 bytes) and yields `lambda` in QM31. The combined claim is
   `C = claim + lambda * rhs2` and the combined vector `u_j = W_j + lambda * w_j`.
2. For rounds `b = 0..5` the prover sends two WideExact values `(c0, c2)`, the
   constant and quadratic coefficients of the round polynomial
   `s_b(X) = sum over the remaining positions of f~ * u~`. The verifier derives
   the linear coefficient from the running claim (`s_b(0) + s_b(1) = C_b`),
   draws `r_b` in QM31 from row `34 + b` over those 64 bytes, and sets
   `C_{b+1} = s_b(r_b)`. Variable `b` is bit `b` of the coefficient index.
3. The verifier accepts if `C_6 = f~(r) * (W~(r) + lambda * w~(r))`, computing
   the three multilinear extensions itself: `f~(r)` from the 64 final-message
   values; `W~(r)` from the weight structure (five product rows over three
   base-four digits, the inactive row's twelve groups, the Libra row's four
   positions); `w~(r) = sum_i rho^i prod_b (1 + r_b (t_{i,b} - 1))` with
   `t_{i,0}` the query's node and `t_{i,b+1} = 2 t_{i,b}^2 - 1`.

The certificate is 12 WideExact values, 384 bytes, canonical encodings
required. It is a deterministic function of data already public in the proof,
so it adds nothing to the privacy argument's view beyond a function of that
view; this is stated, not proved here. It fits the 1.9 KB free in the last
upload transaction.

**Soundness accounting (sketch, to be turned into rows before any claim).** If
either pinned equality fails, the combined claim is false unless `lambda` is
the one bad value: at most `1/|K|`. A false combined claim survives six
degree-two rounds with probability at most `12/|K|`. Seven new Fiat-Shamir
rows, each far below the present largest row (the query row, about
`2^-105.14`), total at most `13/|K|`, about `2^-120.3` per transcript before
the oracle-query factor. `rhs2` is fixed before `lambda` on the same binding
hypothesis as the `rho` row. Not proved: the rows, their placement in the
adaptive argument, the sampler statement for rows 33 to 39, and source
correspondence of the new evaluator.

**Pre-registration.**

- Baseline W9: 1,438,749 to 1,442,350 CU (ELF `52b05716…c229e19`).
- Build W10 = W9 features with the stage D path (measurement tag 13), plain
  build, six fixtures, honest certificates generated on the host from the
  public proof data.
- Prediction: saving of about 150k (348k of instructions replaced by about
  195k: rounds 15k, the 64-entry equality table 11k, `f~` 17k, `W~` 30k plus
  the retained weight preparation 55k, `w~` 33k, rest retained). My estimates
  for my own kernels were high by two to six times in round 2.
- Kept if it saves at least 3,000 on every fixture.
- Tests required before measurement counts: acceptance of the six fixtures;
  the three extensions equal the direct sums over explicit 64-entry vectors
  at random points; every single-byte change of the certificate is rejected;
  an honest-prover certificate for a false relation claim and for a false
  query claim is rejected.
- Outcome wording: if W10 exceeds 1,275,000 on any fixture, "one transaction
  not yet supported; gap N"; if within, "fits the hard-cap budget on six
  fixtures", which is not an all-input bound and not a release claim.

### Stage D: result

Measured on W10 (W9 features with the stage D path, source `a708dd7ec58`, ELF
`33f81522…d7092ea`), honest certificates computed on the host from the public
proof data:

| | transfer-13 | transfer-255 | transfer-1023 | withdrawal-13 | withdrawal-255 | withdrawal-1023 |
|---|---:|---:|---:|---:|---:|---:|
| W9, batched | 1,438,749 | 1,442,350 | 1,440,343 | 1,439,115 | 1,440,422 | 1,440,480 |
| W10, summed | 1,285,779 | 1,289,389 | 1,287,371 | 1,286,131 | 1,287,485 | 1,287,505 |
| Saving | 152,970 | 152,961 | 152,972 | 152,984 | 152,937 | 152,975 |

Predicted 150k; kept. **One transaction not yet supported; gap 10,779 to
14,389** against the 1,275,000 line. The verifier alone now completes inside a
real 1,400,000 CU transaction on all six fixtures (the acceptance runs, not
only the diagnostic ones), and a certificate with one flipped byte is rejected
on chain.

Stage D phases (profiled build, transfer-13): relation round checks 11,938;
`lambda` and six rounds 12,477; equality tables 12,828; `f~(r)` 20,830;
`Weights::new` and `W~(r)` 104,493; `w~(r)` 42,741.

### Round 3, second set: predictions (committed before measurement)

Baseline W10. Applied cumulatively in this order, same keep-or-drop rule.

| Candidate | Basis | Predicted saving |
|---|---|---:|
| D1 inactive row of `W~` through its tensor form | the row's weight is a subset sum of `ap0 x ap1` products; fold the group sums into sixteen QM31 values and contract with `ap0`, then `ap1`: sixteen WideExact-by-QM31 products and four WideExact products in place of sixteen WideExact products, 81 WideExact additions and twelve products | 11k |
| D2 `w~(r)` with the six factors expanded in pairs | each pair is `1 + r_b a_b + r_{b+1} a_{b+1} + r_b r_{b+1} a_b a_{b+1}` with base-field `a`: twelve limb products and one reduction per limb in place of two QM31-by-M31 products and a QM31 product; about 1.15k per query against 1.94k | 17k |
| E4b Merkle parent loop writing each digest straight into the next level's buffer through the syscall, with no by-value digest | about 908 parents; 17 instructions of copies and about 12 of wrapper each | 26k |

D1 and D2 are exact changes to this branch's stage D evaluator. E4b is an
exact change to the Merkle traversal (same hash inputs in the same order) and
adds a provided method to the digest trait and a direct syscall call in the
measurement program.

### Round 3, second set: result

Cumulative program CU of the summed verifier (source `11212d3e6b9`):

| Build | transfer-13 | transfer-255 | transfer-1023 | withdrawal-13 | withdrawal-255 | withdrawal-1023 | Saving on the previous build |
|---|---:|---:|---:|---:|---:|---:|---:|
| W10 | 1,285,779 | 1,289,389 | 1,287,371 | 1,286,131 | 1,287,485 | 1,287,505 | |
| W11 = W10 + D1 | 1,274,910 | 1,278,522 | 1,276,512 | 1,275,313 | 1,276,606 | 1,276,628 | 10,818 to 10,879 |
| W12 = W11 + D2 | 1,260,414 | 1,264,024 | 1,262,017 | 1,260,814 | 1,262,111 | 1,262,131 | 14,495 to 14,499 |
| W13 = W12 + E4b | 1,226,151 | 1,229,212 | 1,227,553 | 1,226,317 | 1,227,376 | 1,227,416 | 34,263 to 34,812 |

Predicted 11k, 17k and 26k; all three kept. W13 is ELF `63591cc2…d6966be`.

**In the wording fixed beforehand: the verifier fits the hard-cap budget on six
fixtures** (1,226,151 to 1,229,212 against 1,275,000). This is not an
all-input bound, not a measurement of a transaction that includes the Pool,
and not a release claim. What it rests on that is unproved: stage C (batched
first fold), stage D (final-message sumcheck), and source correspondence of
every changed kernel.

Still to establish before "one transaction" means anything:

1. A measured transaction that contains the Pool settlement, the adapter and
   this verifier, at the real 1,400,000 limit.
2. An all-input cost argument with margin. The 20 October argument put its
   bounds 7 to 8% above fixture maxima.
3. The soundness rows for stages C and D, and the prover and proof format
   carrying the 384-byte certificate.

### Round 3, third set: inventory of W13 and predictions (committed before measurement)

Trace of the W13 feature set (debug-line build, transfer-13, summed path):
1,063,192 instructions and 162,155 CU of syscall charges, program CU
1,225,347. Inclusive instructions: semantic layer 354,633 (terminal 254,444;
ten rounds 57,583; record parse 16,509); batched folds 326,236 (base lanes
123,266); stage D final checks 162,356 (`W~` 75,172; `Weights::new` 17,553;
`w~` 27,551; equality tables 12,086); preparation 84,833; Merkle 76,723;
canonical scan 16,879; query geometry 16,207.

The Pool's own cost was 97k to 106k on the 13-pair devnet payments and up to
about 154k on the 255- and 1,023-pair fixtures of 19 October (settlement minus
nested verifier). With about 21k of adapter work that makes the 125k allowance
too small for the larger cases, so more margin is wanted before a Pool-fused
build is attempted.

Baseline W13. Applied cumulatively in this order, same keep-or-drop rule. All
exact.

| Candidate | Basis | Predicted saving |
|---|---|---:|
| G1 record validation as "low half canonical QM31 and high half zero" | 15,342 instructions in `parse_record`, which decodes eight limbs and then compares the high half | 7k |
| G2 sumcheck round evaluation with one reduction per Horner step | 270 steps at about 171 (multiply 136, canonical add 35) | 8k |
| G3 canonical scan two limbs per 64-bit word, four words per branch | 4,796 limbs at about 3.5 | 6k |
| G4 stage D scale factors through the dot accumulator | ten calls at about 1.9k, four WideExact-by-QM31 products each | 7k |
| G5 claim dots over one copied row per point | 174 pushes at about 340, of which the per-term match and bounds work is about 40 | 7k |
| G6 second fold with the two edge products shared | per query two WideExact-by-M31 products and four pushes in place of six pushes and five coefficient products | 7k |

### Round 3, third set: result

Cumulative program CU of the summed verifier (source `263f67ed05c`):

| Build | transfer-13 | transfer-255 | transfer-1023 | withdrawal-13 | withdrawal-255 | withdrawal-1023 | Saving on the previous build |
|---|---:|---:|---:|---:|---:|---:|---:|
| W13 | 1,226,151 | 1,229,212 | 1,227,553 | 1,226,317 | 1,227,376 | 1,227,416 | |
| + G1 lean record validation | 1,226,065 | 1,229,126 | 1,227,467 | 1,226,231 | 1,227,290 | 1,227,330 | 86 |
| + G2 fused multiply-add | 1,218,626 | 1,221,723 | 1,220,070 | 1,218,787 | 1,219,832 | 1,219,870 | 7,397 to 7,460 |
| + G3 word-wise scan | 1,223,800 | 1,226,897 | 1,225,244 | 1,223,961 | 1,225,006 | 1,225,044 | regression of 5,174 |
| + G4 scale factors through the dot | 1,222,316 | 1,225,432 | 1,223,777 | 1,222,504 | 1,223,543 | 1,223,574 | 1,457 to 1,484 |
| + G5 claim rows | 1,221,758 | 1,224,874 | 1,223,219 | 1,221,946 | 1,222,985 | 1,223,016 | 558 |
| + G6 shared second-fold products | 1,210,972 | 1,214,075 | 1,212,445 | 1,211,173 | 1,212,212 | 1,212,259 | 10,757 to 10,799 |

Predicted 7k, 8k, 6k, 7k, 7k, 7k. Kept: G2 and G6. Dropped under the 3,000
rule: G1, G4, G5 (too small) and G3 (regression). The kept set is W13 + G2 +
G6; it was not measured as a non-adapter build of its own and is measured
below inside the adapter.

## One transaction through the Pool: replay of the recorded devnet settlements

**What was run.** The two settlement transactions of the 11 November devnet
run (transfer `4QKVyJYb…`, slot 520963524; withdrawal `4pQ2aWTw…`, slot
520964933) were replayed in LiteSVM from their recorded pre-state: every
account of the transaction with its recorded data, the deployed Pool ELF
(`e0e49c34…8cfe09dc`), the recorded slot, the recorded instruction data and
account list, and the real 1,400,000 CU limit with a 256 KiB heap. Signature
verification is off because the recorded payer's key is not available;
nothing else is changed. Tool: `tools/r1-cost-probe/src/bin/one_tx_replay.rs`.

**Control.** With the deployed verifier ELF (`2284239e…0fbd6278`) the replay
reproduces the recorded Pool compute units exactly: 1,139,872 (transfer) and
1,155,430 (withdrawal), with nested verifier 1,043,169 and 1,049,326.

**One transaction.** The verifier at the same address is replaced by the
adapter build with `future-one-tx` and the kept feature set (ELF
`99daf718…48a5ed5`, source `edafb9f09c7`, built with the devnet pool and
registry identifiers). Its settlement entry does not resume a checkpoint: it
validates the reconstructed statement and verifies the whole proof in this
invocation (stage C and stage D), reading the 384-byte certificate from the
start of the verifier-owned seventh account. Stage 1 never runs. The
certificate is computed by the tool from the recorded public statement and
proof.

| | Transfer | Withdrawal |
|---|---:|---:|
| Whole transaction | 1,328,287 | 1,337,700 |
| Pool program (inclusive) | 1,327,931 | 1,337,344 |
| Nested verifier | 1,231,228 | 1,231,240 |
| Margin to 1,400,000 | 71,713 | 62,300 |
| Recorded two-transaction total, for comparison | 2,351,586 | 2,360,824 |

Both complete and return the same result bytes the recorded settlement
returned. With one certificate byte changed the transaction fails; with the
recorded checkpoint bytes in place of a certificate it fails.

**What this is and is not.** It is one transaction that performs all
verification and the Pool settlement inside the real limit, on the two
recorded devnet payments, in a local replay. It is not:

- a devnet or mainnet transaction, or a signed one;
- an all-input result: two payments, both on a young Pool; the Pool's own
  cost grows with history (the October fixtures showed up to about 50k more),
  and the margin here is 62k to 72k;
- a soundness result: stage C and stage D are unproved protocol changes, and
  none of the changed kernels has a source-correspondence proof;
- a complete product path: the prover and client do not yet produce or carry
  the certificate (it would travel with the proof; here it sits in the
  account the checkpoint used), and the two-transaction programs deployed on
  devnet are unchanged.

The release target stays as it was: not yet established.

### Round 4: margin (predictions committed before measurement)

Baseline: the kept set W13 + G2 + G6, measured inside the adapter at 1,231,228
(transfer) and 1,231,240 (withdrawal) nested verifier CU in the replay.

| Candidate | Basis | Predicted saving |
|---|---|---:|
| H1 leaner dot accumulators | `fast_pairing.rs` is 125,090 instructions in the W13 trace for about 1,120 QM31 products: about 45 in the product formulas, 17 accumulating, 5 re-checking the scalar canonical, 4 on the term counter and about 36 unattributed (operand moves). The lean form reads the limbs once, drops the per-push scalar check and term counter, and accumulates in place | 25k |

H1 is exact for canonical scalars. It removes two defensive checks of the
pinned accumulator (scalar canonicality at every push, and the 4,096-term
limit), so adopting it needs the canonical-scalar fact and a static term bound
at each call site; every current call site pushes at most 174 terms of values
that are canonical by construction or by an earlier decode.

### Round 4: result

| Build | transfer-13 | transfer-255 | transfer-1023 | withdrawal-13 | withdrawal-255 | withdrawal-1023 | Saving on the previous build |
|---|---:|---:|---:|---:|---:|---:|---:|
| W13 | 1,226,151 | 1,229,212 | 1,227,553 | 1,226,317 | 1,227,376 | 1,227,416 | |
| W20 = W13 + G2 + G6 (the kept set) | 1,206,081 | 1,209,165 | 1,207,537 | 1,206,255 | 1,207,300 | 1,207,354 | 20,016 to 20,076 |
| W21 = W20 + H1 | 1,204,371 | 1,207,444 | 1,205,783 | 1,204,528 | 1,205,592 | 1,205,624 | 1,708 to 1,754 |

H1 was predicted at 25k and measured at 1.7k; dropped. In the replay the H1
adapter build gives 1,326,537 (transfer) and 1,335,953 (withdrawal), 1,750
below the kept build; the kept build's figures stand.

The kept set, as a plain build, is W20: 1,206,081 to 1,209,165 on the six
fixtures (ELF `3d5b5166…62db8e2`, source `b1189d085a1`).

**Reading.** Kernel-level changes have stopped paying: of the last seven
tried, two cleared the 3,000 rule. The predictions for them were wrong in the
same direction each time, because the compiler had already removed most of
what looked removable in the source. Further margin of a useful size would
have to come from the proof format, not from the arithmetic:

- one 22-query multiproof per tree in place of two batches: about 65 fewer
  parent hashes (about 11k) and 2,176 fewer proof bytes;
- a folded tree of depth 16 in place of the padded depth 18: about 40 fewer
  parents (about 7k) and about 1.2 KB.

Together with the 384-byte certificate that would leave the proof about 3 KB
smaller than today, which is one upload transaction fewer. Both need the
prover; neither has been built or measured.

## Round 5: proof format and prover (owner direction, 11 November)

The soundness rows for the changed verifier are written out in
`SOUNDNESS-ROWS.md` (committed with this section, before the code).

### The summed format (design and pre-registration)

**Dropped: the shallower folded tree.** The folded tree is padded from `2^16`
to `2^18` leaves at the top, where all 22 paths have already merged, so depth
16 would save two parent hashes and 64 bytes, not the forty hashes estimated
earlier. It is not worth a change to a commitment.

**Layout.** Identical to the pinned compact format up to the end of the 22
openings (offsets unchanged, so the pinned parsing, scan and preparation code
applies as it is), with a new magic. Then:

| Section | Bytes |
|---|---:|
| Header, semantic, `y1`, inactive, round 0, folded root, round 1, final message, 22 openings (as pinned) | 28,359 |
| C1 multiproof over the 22 queries, zero-padded to 296 nodes | 9,472 |
| C2 multiproof, the same indices, 296 nodes | 9,472 |
| Folded multiproof over the distinct `u / 4`, 254 nodes | 8,128 |
| Stage D certificate | 384 |
| Total | 55,815 |

The pinned format is 57,607 bytes. With the 688-byte candidate prefix the
proof account is 56,503 bytes: 58 bytes more than 15 uploads carry at today's
chunk size (3,763), and within 15 uploads if the client fills each upload
transaction to the 4,096-byte limit (it leaves 67 bytes unused today). The
upload count is therefore not claimed either way.

**Transcript.** Unchanged for rows 0 to 32. A pinned proof can be re-packed
into the summed format from public data alone: the merged multiproof's nodes
are a subset of the two batches' nodes, and the certificate is a function of
the proof. The prover's publish step is that re-packing of its own pinned
output; a native emission from the trees would produce the same bytes. Version
separation of the transcript is listed as an open decision in the soundness
note.

**Verifier.** `verify_summed_format`: shape check for the new length and
magic, the pinned scan and preparation, three merged multiproofs (C1 and C2
share one sorted index schedule), stage C, the relation round checks and
stage D with the certificate read from the proof.

**Pre-registration.**

- Baseline: the kept set W20 (1,206,081 to 1,209,165, certificate in a
  separate account) and the replay figures 1,328,287 and 1,337,700.
- Prediction: about 46 fewer parent hashes than the two-batch form on these
  fixtures, at about 172 CU each, less the cost of sorting 22 keys in place of
  10 and 12: a saving of about 6k. Proof bytes 55,815 (fixed by the layout).
- Tests required: the six fixtures re-packed and accepted; a pinned proof
  rejected by the summed verifier and a summed proof by the pinned one; every
  region mutated and rejected, including certificate bytes, multiproof nodes
  and slot padding; the merged node count equal to the pinned count function
  on the fixtures' index sets and within the slot bounds; the bit-reversed
  index sets attaining 296 and 254.
- Measurement: W22 = W20 with the summed-format path, plain build, six
  fixtures; and the replay of the two devnet settlements with the proof
  buffer re-packed into the summed format and the certificate inside it.

### Round 5: result

**The summed format, verifier alone** (W22 = the kept set with the
summed-format path, source `4d90eb5f43e`, ELF `413cd484…ed5f0ff`; proofs
re-packed from the six fixtures, 55,815 bytes each):

| | transfer-13 | transfer-255 | transfer-1023 | withdrawal-13 | withdrawal-255 | withdrawal-1023 |
|---|---:|---:|---:|---:|---:|---:|
| W20, certificate in a separate account, two batches per tree | 1,206,081 | 1,209,165 | 1,207,537 | 1,206,255 | 1,207,300 | 1,207,354 |
| W22, summed format | 1,188,076 | 1,191,300 | 1,190,853 | 1,189,844 | 1,193,943 | 1,195,051 |
| Saving | 18,005 | 17,865 | 16,684 | 16,411 | 13,357 | 12,303 |

Predicted about 6k; measured 12k to 18k; kept. All six complete inside a real
1,400,000 CU transaction. On chain, a summed proof with one certificate byte
changed is rejected and a pinned-format proof is rejected. Host tests (39
pass): the six re-packed fixtures accepted; the two formats reject each
other; a changed byte rejected in every region, including multiproof nodes,
slot padding and the certificate; node counts equal to the pinned count
function and within the slots; the bit-reversed index sets attain exactly 296
and 254 nodes.

**One transaction through the Pool, summed format** (adapter ELF
`b04bf96d…31060be`; source `58ff2daf4d7`; replay tool at
`b9dd44e9e76`). The recorded proof buffers are re-packed into the summed
format (56,503 bytes with the candidate prefix); the seventh account is left
as recorded and is not read. The first attempt (adapter ELF A3) failed at an
account-length check in the adapter wrapper that still expected the pinned
length; that is fixed in A4 and the failed records are retained.

| | Transfer | Withdrawal |
|---|---:|---:|
| Whole transaction | 1,314,472 | 1,320,977 |
| Pool program (inclusive) | 1,314,116 | 1,320,621 |
| Nested verifier | 1,217,420 | 1,214,524 |
| Margin to 1,400,000 | 85,528 | 79,023 |
| Marker address prefunded with one lamport (three System calls) | 1,318,569 | 1,325,074 |
| Marker address prefunded with full rent (two System calls) | 1,316,954 | 1,323,459 |

Checks the replay now makes, all passing for both payments:

- the control (deployed verifier, recorded accounts) reproduces the recorded
  compute units and ends in the recorded final state on every account, apart
  from the payer's fee (the replayed transaction is unsigned and built as a
  legacy message). The replay uses devnet's rent, 5,080 lamports per byte,
  read off the recorded accounts; with LiteSVM's default rent the created
  marker held a different balance, which the first version of this check
  caught;
- the one-transaction run ends in the same final state as the control on
  every account, the payer's balance included; the proof buffer is not
  written;
- the two rejected runs (one certificate byte changed; the recorded
  pinned-format buffer) change no account apart from the fee charged to the
  payer for a failed transaction;
- with the marker address prefunded, the settlement still ends in the same
  state apart from the payer's balance.

**Not measured.** Root-history page occupancy and rollover, and lane frontier
patterns other than the two recorded ones. The recorded payments are on a
young Pool; a rollover needs a different account list and a consistent Pool
state that the devnet receipts do not contain. The 79k to 86k margin is
therefore a margin on these two payments plus the two marker variants, not an
all-input bound.

**Prover and client.** The publish step for the summed format is
`to_summed_format`, a function of the pinned proof and the public statement;
it is what the measurement driver and the replay use. Not built: a client
that uploads the summed proof and sends the single settlement transaction to
a network, and the programs deployed for it (a new verifier address needs a
registry entry, and the devnet registry in use is frozen, so a network run
needs a fresh deployment decision).

## Round 6: client and devnet (owner go-ahead, 11 November)

Full record, predictions and receipts: `evidence/future-version-20261111/devnet/README.md`.
This section is the summary.

**Built.** The devnet client's planner takes `"one_tx": true`: it re-packs the prover's proof
with `to_summed_format`, checks the result with `verify_summed_format`, and writes the summed
proof for upload. The run script `FV_spend.py` pays in 18 transactions: an open that funds a
fresh session key and creates the proof account and the checkpoint account (carrying the last 58
proof bytes), 15 writes of 3,763 bytes, the one verification-and-settlement transaction, and a
close that returns everything the session key holds. The payer signs the open only. A variant of
the adapter without the stage 1 entry (`future-one-tx-lean`, ELF `85568738…6c02c`, 967,384 bytes)
is the deployed verifier; the replay of the recorded PIN2 settlements gives the same compute units
with it as with the earlier adapter ELF.

**Deployed.** Verifier `CmxQHrAx4qno6WRPMpWdRVp7MbyQiG7PhcfsVhuJaW92` on devnet, upgrade
authority revoked (the registry requires it), 4,915,189,560 lamports of rent locked. Pool,
registry and upload program are the deployed PIN2 ones, unchanged.

**Measured on devnet** (fixture measurements; predictions registered before each run):

| Run | Payment | Settlement, one transaction | Margin to 1,400,000 |
|---|---|---:|---:|
| registered | transfer | 1,308,068 | 91,932 |
| registered | withdrawal | 1,321,318 | 78,682 |
| timing | transfer | 1,312,109 | 87,891 |
| timing | withdrawal | 1,321,189 | 78,811 |

In the registered run a changed certificate byte and a changed Merkle node byte were each rejected
with no state change (after about 1.29M and 0.66M compute units), replays were rejected, and the
payer's balance change per payment equalled fees plus the nullifier marker rent. One prediction
missed: the transfer's compute band was centred too high, by 932.

In the timing run a payment was sent the way a wallet would send it (all 18 transactions signed
first, four phases, confirmation only, each transaction broadcast to two endpoints): the open
confirmed at 1.5 s, the 15 writes at 3.1 s (all in one slot), the settlement at 4.5 s and the close
at 6.0 s, for both payments.

**Proving.** 26.7 s and 26.8 s per proof natively on an Apple M3, one thread, 0.61 GB peak. No
phone or browser measurement exists.

**Still not established.** As before: an all-input compute bound (rollover and a long-history
Pool are unmeasured), the soundness rows of the changed verifier, the source correspondence of the
changed kernels. The release target is unchanged and not yet established. A separate agent is
working through the soundness argument; its note will be
`docs/research/future-version/SOUNDNESS-ARGUMENT.md`.

### Round 6, after the devnet runs: branch-head build (transcript continuation, Merkle check last)

Two changes were made to the verifier after the devnet deployment, both for the proof and both
recorded with their reasons in SOUNDNESS-ARGUMENT.md and RECORDED-EXPERIMENT-40.md: the final
sumcheck continues the opening transcript (one transcript start fewer), and the Merkle
authentication runs after the final sumcheck rows (the order the formal model has). Build A6 of
the branch head 4045ecbdda3 (`5dd5b2b16c00…a003b`, 967,120 bytes, the A5 feature set), replayed on
the recorded devnet settlements (`replays-v4/`):

| Payment | A5, deployed on devnet | A6, branch head | Difference |
|---|---:|---:|---:|
| Transfer, whole transaction | 1,314,472 | 1,314,308 | -164 |
| Withdrawal, whole transaction | 1,320,977 | 1,320,803 | -174 |

Final state equal to the control in both; a changed certificate byte is rejected with no state
change. Neither change raises compute units on these two payments. A6 is not deployed.


## Round 7: what the extraction rewrites cost (predictions committed before measurement)

The extraction probe (EXTRACTION-PROBE.md) found that nine functions of the one-transaction
verifier do not go through the translator as written, and produced a rewritten copy of seven of
them that does (`extraction-probe/rewrites-tested.patch`, 6 files, +343 −212 lines, applies to the
branch head). The owner's rule for Aspis is that a change passes only if it does not raise compute
units, lower soundness or put privacy at risk. The rewrites do not touch the proof format, the
transcript or the prover's output. Their compute cost is not known. This round measures it.

Baseline: build A6, replay of the two recorded devnet settlements: transfer 1,314,308 CU,
withdrawal 1,320,803 CU.

Builds, same recipe and feature set as A6, same replay tool and recorded transactions:
- **X1**: the branch head with the patch applied.
- **X2**: X1 with `SolanaDigest::digest_into` written as `*out = hashv(parts).to_bytes()` on
  chain too (the SDK call the translator can see), instead of the direct `sol_sha256` call.

Predictions, written before any build:

| Build | Predicted difference from A6, each payment | Point guess |
|---|---|---|
| X1 | 0 to +20,000 CU. The merged Merkle check runs about 850 node steps and the record decoder several hundred element steps; a rewrite that replaces an early exit by a carried flag costs a few units per step. | +8,000 |
| X2 | X1 plus 4 to 12 CU per in-place digest (up to 975 of them): +4,000 to +12,000 over X1. | X1 + 7,000 |

Acceptance, fixed now:
- Both replays must accept and end in the same state as the control, and the changed-certificate
  and redirect attempts must still be rejected with no state change. Otherwise the build is wrong
  and the number is void.
- A build passes the owner's rule only if neither payment costs more than A6. A build that costs
  more is not adopted on my authority. It goes to the owner with the measured cost, or the
  rewrite is redone function by function until it costs nothing.
- If X1 costs more, it is bisected by file (multiproof, wire, weights, the fold and final checks)
  so that each function's cost is known.

### Round 7: result

Builds (recipe and feature set of A6; each from its own copy of the source and its own target
directory):

| Build | Source | ELF sha256 | Bytes |
|---|---|---|---:|
| A6 | branch head 4045ecbdda3 | `5dd5b2b16c00922813dec692ee348dda2a73a58cbfaabe5a2f591b0b8c5a003b` | 967,120 |
| X1 | head + `rewrites-tested.patch` | `7a77273b1dc64689a0eed1cc267c6e81c9f6d0ad2e17fe0be316243d3ae9a3d5` | 972,024 |
| X2 | X1 + SDK `hashv` in `digest_into` | `dff6a4385d7ae6503e97a6672835aab3b0ad3937bfba0caa0a339e9508a2556c` | 972,544 |

Replay of the two recorded devnet settlements (`replays-v5/`), whole transaction:

| Payment | A6 | X1 | X1 − A6 | X2 | X2 − X1 | X2 − A6 |
|---|---:|---:|---:|---:|---:|---:|
| Transfer | 1,314,308 | 1,306,700 | −7,608 | 1,331,318 | +24,618 | +17,010 |
| Withdrawal | 1,320,803 | 1,313,188 | −7,615 | 1,337,466 | +24,278 | +16,663 |
| Withdrawal, marker pre-funded with one lamport (heaviest measured) | 1,324,900 | 1,317,285 | −7,615 | 1,341,563 | +24,278 | +16,663 |

Both predictions missed:
- X1: predicted 0 to +20,000 (point +8,000). Measured −7,608 and −7,615. Wrong direction: the
  rewritten functions are cheaper. Which function the saving comes from was not attributed; the
  bisection by file was conditional on X1 costing more and was not run.
- X2 over X1: predicted +4,000 to +12,000. Measured +24,618 and +24,278, twice the top of the
  band: about 25 CU for each in-place digest, not 4 to 12.

Acceptance conditions, both builds: the one-transaction run completes under 1,400,000 CU, its
final state equals the control's, a changed certificate byte is rejected, the pinned-format buffer
is rejected, rejected runs leave the state unchanged apart from the fee, and the four redirect
attempts are rejected with no token movement (`replays-redirect/X1-rewrites-withdrawal.json`,
`X2-rewrites-hashv-withdrawal.json`). All hold.

**Is the rewritten verifier the same function?** A cheaper build could be a build that lost a
check, so this was tested before anything else is said about X1.

- Mutation campaign (`tools/r1-cost-probe/src/bin/one_tx_mutants.rs`, host script
  `fv_mutants.sh`). The tool is built once from the original source and once from the rewritten
  source. Each binary runs the verifier on 156,704 corrupted copies of the two recorded proofs
  (every single-bit flip at every byte, 111,630 of them; a non-canonical limb at every 4-byte
  position; every Merkle node and certificate block zeroed; every adjacent pair of node blocks
  exchanged; four length changes) and writes the verdict and the number of observer marks
  reached. The two verdict files are byte-identical (sha256
  `e3659a53d3b4e308711668d82715cd981e8d3bdc7ba859c9ff3bdaa1e3c9e2b9`), with the deployed feature
  set switched on (`mutants/MUTANTS_dep2.done`) and with the default features
  (`MUTANTS_full.done`). The deployed-feature verdicts also equal the default-feature verdicts.
- In both, every single-bit flip is rejected. 174 mutants are accepted: each zeroes or exchanges
  blocks of the all-zero padding of a node slot, so the mutant is the original proof.
- The first two runs (`full`, `dep`) shared one cargo target directory between the two trees.
  A control run of the tests in that arrangement finished in 0.15 s, which showed that cargo can
  take one tree's artifacts for the other's. The campaign was therefore rerun with one target
  directory per tree (`dep2`). Each tree compiled its own crates, the two binaries have the same
  hashes as in `dep`, and the verdict files are the same. So the earlier runs had not mixed the
  trees, and `dep2` is the run relied on.
- On the rewritten source with the deployed feature set: the statement-binding test (69
  changed-statement cases rejected) and the weights, pairing, dots and validated-prefix
  equivalence tests pass (host receipt `SB-dep-src-xp1`). The control on the original source
  reused the rewritten tree's test binaries and is not a control.

What this does not show: equality on every input. The mutants are corruptions of two honest
proofs with their own statements. On-chain behaviour of the rewritten build is tested by the
replays above and by nothing else. Nothing here is proved.

**The prover.** `weights.rs`, `r1_wire.rs` and `fast_pairing.rs` are compiled into the prover as
well. The pinned prover (`prover.rs`, `host_*.rs`) names none of the changed functions. The
re-packing helper `to_summed_format` gives the same bytes from both trees on the two recorded
proofs (the proof hashes in the verdict files' header lines agree). A byte-identity run of the
prover on the frozen source is still owed at the freeze.

**Cost outside compute.** The ELF grows by 4,904 bytes (X1) or 5,424 bytes (X2). An immutable
verifier locks its rent: at 5,080 lamports per byte that is about 0.025 SOL or 0.028 SOL more,
once, at deployment.

**Status against the owner's rule.**
- X1 costs less than A6 on both payments, so the rewrites pass the compute test. Soundness is
  tested as above, not proved. Not yet adopted: adoption is part of the freeze proposal.
- X2 costs more than A6. Under the rule as given it is the owner's decision. On 2026-11-11 the
  owner first said the direct call is a fine trust assumption, then: "for what is really a proof
  of concept research thing, maybe there is more value in more clean proof". The lead recommended
  the SDK route (X2) and asked for a confirmation, with a proposed working rule: proof
  cleanliness wins while the heaviest measured payment stays at least 50,000 CU under the limit.
  X2's heaviest measured payment is 58,437 CU under the limit. The page-rollover path is not
  measured in any build. No decision is recorded until the owner confirms.
- Owner, same day: "ok i say take sdk, although if thre is a way that you could work out the
  worst case inputs before a final decision that would be great". Recorded as: the SDK hash route
  (X2) is the owner's choice, and the final decision waits for the worst-case compute figure. The
  owner did not answer the proposed working rule, so it is not in force: every other choice that
  raises compute units still goes to the owner one by one. The worst-case work is in
  WORST-CASE-COMPUTE.md.

### Round 7: decision, and the branch head

- Owner, 2026-11-11, after the worst case was measured (WORST-CASE-COMPUTE.md: 1,372,342 for A6,
  1,364,799 for X1, 1,390,527 for X2, against the limit of 1,400,000) and the lead recommended
  keeping the direct hash call: "recommendation". The build is X1: the rewrites applied, the
  direct `sol_sha256` call kept, and that call site named inside the hash trust assumption.
- The rewrites are applied to the branch at 7dffe3e2a93. The six changed files equal those of the
  measured source tree, hash for hash.
- Reproducibility of X1: a second copy of that source at another path, built with a fresh target
  directory (host attempt `B-X1-repro`), gives a byte-identical program,
  `7a77273b1dc64689a0eed1cc267c6e81c9f6d0ad2e17fe0be316243d3ae9a3d5` (`out/X1-repro/`). One host,
  one toolchain; a build on a second machine is still owed for a release.
- The owner then asked whether further optimisation is worth attempting before the freeze. A
  bounded effort is running: implementation only, each change still accepted by the translator,
  identical verdicts on the mutation campaign, measured at the rollover worst case, two rounds at
  most, nothing adopted without the owner. Its note is OPTIMISATION-ROUNDS.md. The freeze waits
  for it.

## Round 8: the sampler's digit function in index-loop form (owner: "ok rewrite it now")

`sampler::low_base_p_digits` turns a 32-byte hash output into the base-P digits that become the
verifier's challenges; the prover runs the same code. Its shipped form divided through
`quotient.iter_mut().rev()` inside a `from_fn` closure. The translator in use drops a write made
through a reversed mutable iterator and reports success (EXTRACTION-PROBE.md section 11), so the
function could not be carried into a proof of the Rust. R1's proof does not use an emission of it:
it models the samplers by an emission of a rewritten crate with indexed loops, and the link from
that crate to the shipped source is an open item there (soundness lead, 2026-11-11).

Two forms were gated against the head (build X1):
- S1: the eight division passes written in place with index loops.
- S2: the text of the rewritten crate that R1's model was emitted from (research evidence
  `prover-commit25-20261021`, `harness/lowdigits25.rs` and `addsmall25.rs`, module `reference`):
  `low_base_p_digits` through `qm31_div_pass`, and `add_small_base_p` as an index loop.

| Gate | S1 | S2 |
|---|---|---|
| Differential test against the shipped form kept as an oracle (boundary blocks, 200,000 pseudo-random blocks) | pass | pass, also for `add_small_base_p` |
| Integration tests with the deployed feature set | pass | pass |
| Program ELF | `be0ecb65032406107f6380e3e12f34359935ef3bd533dc30db6d4f24bc46dea3` | the same ELF, byte for byte |
| Mutation campaign, 156,704 corrupted proofs, verdict file against the head | identical | identical |
| Replay of the recorded payments, changed certificate, redirect attempts | as the head | as the head |
| Prover byte identity: fixture proofs from the tool built in the changed tree against the unchanged tree, six scenarios, pinned and re-packed hashes | identical | identical |
| Compute against X1, every payment and marker state measured | +137 | +137 |

The two forms compile to the same program. S2 is adopted because its text is the one R1's proof
already models. Cost: 137 CU on every payment (1,306,837 and 1,313,325 on the recorded payments;
1,354,239 at the heaviest measured case). Not predicted beforehand in writing: I told the owner I
expected it to be negligible. Evidence: `evidence/future-version-20261111/sampler-rewrite/`, host
script `fv_sampler_gate.sh`, verdict reader `fv_gate_compare.py`.

Tested, not proved. The prover check covers accepted fixture proofs only; the privacy lead runs
its own harness with failing attempts on the integrated candidate before the freeze.

## Round 9: bounded verifier optimisation, adopted (owner asked for "a couple of rounds")

Full account, with the profile, every candidate, the predictions and the rejected changes:
OPTIMISATION-ROUNDS.md. Summary of what is adopted.

Patch `optimisation/r2c.patch` (sha256
d5894a550a464b2a8879949e74cac2d750836e52ab8cb95ec8cbf27f431d2dbb), three changes, all in
functions that exist only in Aspis (`fused.rs`, `multiproof.rs`; nothing present at the R1 pin
c7593d23fdc is touched):
- `base_fold`: eight entries per loop step (8,659 CU at the heaviest measured case);
- `merged_level`: each index read once (2,246);
- `extension_lane` with a new `scanned_k`: the extension-lane values read without a second
  canonicality check, the canonical scan having already accepted the same bytes (15,086).

No change to the proof format, the transcript, the order or number of digest calls, the prover's
functions, the Pool, or the direct hash call.

| | X1 | X1 + patch | Saving |
|---|---:|---:|---:|
| Transfer (recorded) | 1,306,700 | 1,280,827 | 25,873 |
| Withdrawal (recorded) | 1,313,188 | 1,287,348 | 25,840 |
| Heaviest measured (withdrawal at rollover, seed 60, one-lamport marker) | 1,354,102 | 1,328,111 | 25,991 |

Predicted for the combination before it was built: 26,000 (band 22,000 to 28,000). Of the six
single-candidate predictions in the two rounds, three were in their band and three missed in the
wrong direction (two rejected, one rewritten); they are listed in the note.

Gates on the combined tree: mutation campaign verdict file identical to X1's (156,704 corrupted
proofs); statement-binding and equivalence tests 11 of 11, library tests 23 of 23 with two new
equivalence tests; replays, changed certificate, pinned-format buffer and redirect attempts as
before; the translator accepts the changed functions and their Lean elaborates (the same four
declarations fail as on X1, none of them changed here); a rebuild after a test-only fix gives
the same ELF (`639642a06c0aeef10e8a9bb60660757febbf8df768d103504ec9a7a35916ff78`).

Branch head after rounds 8 and 9 (this patch and the sampler rewrite): program ELF
`7540abe6c5f07827011b11d3313fe5594816a32fa05963195ee4a1f5cf7856b5`, 972,072 bytes (host build
`BASE2`); recorded payments 1,280,964 and 1,287,485, each 137 above the patch alone, as the
sampler rewrite predicts. Worst case of this head with the allowance of WORST-CASE-COMPUTE.md
(10,697): 1,328,248 + 10,697 = 1,338,945, by arithmetic from the two measured parts; the
heaviest scenario has not been rerun on this exact ELF yet.

Information recorded for the owner, not adopted: with this patch the SDK hash route would cost
about what X1 costs today (1,355,305 at the heaviest measured case).

Tested, not proved.
