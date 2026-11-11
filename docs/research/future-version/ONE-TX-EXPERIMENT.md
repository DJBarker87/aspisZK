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
