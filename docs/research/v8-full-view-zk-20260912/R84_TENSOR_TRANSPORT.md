# R84: tensor transport, a retained failure, and a measured two-swap candidate

2026-09-29. Research experiment, **not security promotion**. Source control:
R82 `d137f7316e0878bfb90780c13214a7586287deb2`; unchanged-profile R83 control
is committed as `14eb3740d`.

The new-profile complete verifier executes at **1,212,653 / 1,210,833 CU**.
Both honest runs still exhaust at the actual **1,000,000-CU** cap. The larger
fixture remains **212,653 CU** over target. These are fresh proofs for a new
encoding profile, not unchanged-proof measurements. Compared with the R83
control's 1,326,977 / 1,328,177 totals, the observed difference is 114,324 /
117,344 CU; it is a whole-profile comparison with different challenges.

**R83 remains the selected unchanged-profile implementation.** Neither the
new profile's privacy nor its end-to-end soundness has been established.

## Original supplied candidate: passes algebra, fails the retained H1 gate

The supplied base permutation is

```text
base(j) = (j & 1) | (((j >> 1) & 63) << 4) | (((j >> 7) ^ 7) << 1)
```

Swapping its images at code positions 127 and 1023 fixes the balancing pivot.
The first 89 images are 14,15,30,31,...,718. The actual source inventory
confirms all sixteen columns are legally maskable there, all are inactive
for H1, and neither the pivot nor reserved row 1014 is selected. The existing
balanced-pivot operation is retained.

Focused Rust checks pass all 1,024 permutation/inverse basis cases, all 89
balanced pad images, 65,536 full-QM31 tensor coefficient comparisons, and
64 arbitrary swap/dual/chord/image/final cases. The source-order constructor
is checked against the frozen SBF table.

But both genuine source-prefix attempts fail the **unchanged rank-540 gate**:
H1 rank is **539**, with zero affine residuals for these particular opposite
witnesses. This is a coverage warning, **not an exhibited privacy attack**.
No assertion was weakened to accept it, and no SBF result for this one-swap
profile is claimed.

A diagnostic elimination with retained row-operation coefficients isolates
the additional dependency. The active/balance/final submatrix has 471 rows
but rank 470. Its one left-kernel vector has support on:

```text
H1 active row 993, H1 active row 1008, inactive balance, Final256[255].
```

Both public coefficient certificates were rechecked against **all 1,022
original matrix columns**. Their products with the two actual affine targets
are zero. A universal source justification would still be needed to use
this smaller image; two zero targets do not supply it. The original failed
profile and its exit-101 receipts are preserved.

## Separate candidate: one additional tail swap

The second candidate adds a swap of code positions **126 and 1021**. Before
this swap those positions contain original rows 1022 (inactive) and 993
(active), respectively. It moves the problematic active row out of the tail.

This preserves the first 89 pad images, pivot 1023 and all 271 selected
sparse-G coordinates: neither 126 nor 1021 belongs to `128 + 3*i` for
`0 <= i < 271`. The compact correction now has **two rank-one swap terms**.
It is a separately versioned profile, not a silent change to the first map:

`AV8/R84/sparseG-bitperm-two-swaps/quadratic-channel-fold/research-v2`.

On **both actual source-generated prefixes**:

- C1 opposite-witness correction: rank 108 per selected column; original
  raw, point and OOD equations checked.
- H1 active/balance/final submatrix: rank 471; full 562-row system: rank 540,
  with every original affine equation and actual padding API checked.
- G: 626 equations, rank 602, with affine compatibility and every original
  equation checked—not just rank.
- Actual independent encode/decode reconstruction retains p0/p2, all seven
  first-relation coefficients and combined Final256, plus earlier semantic,
  raw, point, OOD and balance observations.

These are finite fixed-prefix witness corrections. They do not prove a
posterior-preserving causal simulator or the shared-oracle publication law.
The old R18 rank-517 bit-affine negative and all other earlier regressions
remain untouched. No old H1-only semantic schedule search was repeated.

## Actual compact implementation and complete measurements

The source evaluator transforms the tensor points, moves the fused XOR-12
block to high bits 8/9, and reuses the existing chord/block recurrence.
It evaluates the two swap contractions, retains the original balancing
pivot, and regenerates the exact inactive masks from the new order. Those
masks require 12 shared sums and 159 selected additions in this implementation.
The old T163 evaluator remains in the source as a retained, non-selected
implementation; it is not used to check this different profile.

R83's exact-output packed opening contraction is reused. The sparse-G scalar
still uses the same 271 code positions and the shared high/final adjoint.
Both roots, canonical parsing, paired authentication, image coefficients,
query powers, transcript ordering and all final acceptance checks remain.
The versioned profile/functional descriptors bind the changed map explicitly.

Compiled and executed:

- `r84-bitperm-check`: inventory, inverse and full-QM31 functional tests;
  the compact source is compared with the independent dense source function,
  including arbitrary final/image values and zero/one challenges.
- `r55-opening-check`: retained decoding/malformed/reference controls and
  R83's 4,096 arbitrary mixed-coefficient cases.
- Optimized actual host prover/verifier: both fresh complete proofs accepted.
- 3,282 wire controls: one acceptance and 3,281 checked rejections, including
  the old R19 profile. No resource failure is counted as a security rejection.
- SBF source-table export equality, stack gate, and complete LiteSVM runs.
  Both honest diagnostic executions accept; changed combined finals reject
  with Custom(6), including at the actual 1M cap.

SBF ELF SHA-256:
`f4256c5aea3fc28c6ccffd2ef2e3e0e4a3cf7922ba41e5b122eff9bebc876b6a`.

New proof SHA-256 values:

```text
world0 d0396cfbf2850540182bf7ed028a0739379cccb04439f5a61a3700989f8628cd
world1 581b08936f5aaaea7f69d0cb1b324499779f40f1a2bf67dedc4a701462bc428d
```

The same simulation driver and 262,144-byte heap are used. No transaction
was submitted to a network; accounts were unchanged in the simulations.

## Receipts and exact remaining boundary

`tools/check_r84_evidence.py` audits 100 public artifacts, the 212 source
pins per stage, allowed source differences, parent gate links, new map,
unchanged challenge chronology apart from versioned domains, and measured
runtime results. No keys, private fixtures or ELF binaries were collected
into the repository. Initial exploratory stage A lacked an explicit saved
overflow-check environment setting; the diagnostic/source gates in B and
the two-swap/compact stages explicitly enable and record overflow checks.
Some inherited preflight metadata still names the historical T163 ancestor;
the effective R84 profile/order is explicit. The compact stage corrects the
basis metadata to `signed-bit-permutation-two-swaps`.

All heavy work used the cached Tailscale NUC, zero swap, TasksMax=128 and
explicit high/max caps: 5/7 GiB host, 12/16 GiB SBF, 2/3 GiB simulation.
Selected representative receipts:

| Target | Exit | Wall | Peak process RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Two-swap affine world0 | 0 | 42.06 s | 261,480 | 0 |
| Two-swap affine world1 | 0 | 41.13 s | 261,264 | 0 |
| Compact source leaf compilation | 0 | 22.27 s | 523,380 | 0 |
| Compact source leaf execution | 0 | 0.18 s | 2,288 | 0 |
| Complete SBF build | 0 | 23.61 s | 602,428 | 0 |

**No Lean targets were added or compiled.** Formalization remains paused
for the CU campaign. The Solana skill's source, stack and complete-execution
gates were followed.

The first remaining security proposition is **universal actual-source
C1/H1/G joint affine-image compatibility for the two-swap map**, including
the channel messages, legal same-public witness changes and degenerate or
adaptive prefixes (or an explicit justified loss for exceptions). This must
precede a claim of posterior-preserving simulation. Coherent pre-beta
extraction, shared-oracle/seed/commitment correspondence, visible failures,
retries and publication obligations also remain separate and open.

The first performance obligation is a complete honest run under **1M**;
212,653 CU remains even for this unpromoted profile. The next native target
is broader canonical-kernel fusion. Word-aligned leaves, higher-arity trees
and inverse hints have **not** been implemented or benchmarked in this round.
No new hiding assumption, shortened challenge/hash, reduced query count,
resampling, deployment or wallet operation was introduced.
