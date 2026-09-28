# R24: source-exact native composition

2026-09-28. Parent `a0f2d200c295f3028a12e1142a39a026d19bf1a0`.
R21 remains retired. R19/R20 proof format, transcript, sparse G, T163,
authentication and acceptance checks are unchanged.

## Complete measured result

| Clean complete verifier | World 0 CU | World 1 CU |
|---|---:|---:|
| R20 control | 2,865,333 | 2,866,803 |
| R23 guarded width | 2,529,453 | 2,530,968 |
| R24 A: also scalar transpose | 2,500,981 | 2,502,249 |
| R24 B: also guarded QM31 product | 1,857,687 | 1,859,272 |
| **R24 C: also inactive-mask sharing** | **1,817,965** | **1,819,559** |

This is approximately 36.6% below R20 and 28.1% below R23. **Both actual
1,000,000-CU executions still exhaust.** About another 45% reduction is needed;
the target is not complete. No partial run or isolated terminal is counted as
a complete-verifier budget success.

Both unchanged genuine proofs pass at the diagnostic cap, with the same 256KiB
heap. Corrupted final-message controls give checked custom rejection at that
cap. At 1M, resource failure is not called rejection. Simulated accounts remain
unchanged; no deployment, live transaction, wallet operation or key cleanup ran.

## Changes and exact boundary

1. Compose R22's source-tested scalar transpose into the actual full relation
   caller. The ordinary contribution is contracted against the final vector
   directly; the sparse contribution and every image term remain.
2. Guard all eight input limbs before a canonical schoolbook QM31 product.
   It uses the existing tower and full-width reducer. Six reductions reconstruct
   the output from bounded integer accumulators. Explicit wrapping additions
   and subtractions occur only inside these locally bounded expressions.
   Noncanonical constructors execute the original multiplication path; global
   overflow checking stays enabled. Outlining the product and three scalar
   routines is necessary for SBF code-size/stack safety.
3. Derive the actual inactive masks from the frozen source table. Sixteen
   normal masks contain 809 set bits but only ten distinct masks. Choosing each
   mask or its complement leaves 87 selected rows, plus shared totals. The
   exact source transport rechecks all masks in host gates. No mask, basis
   permutation, pivot or protocol parameter changes.

The full candidate has 176 checked source pins; the isolated candidate has
183. The repository's production paths are not patched: reproducible research
stagers create the exact assembled source, which is retained with manifests.

## Checks and formal leaves

For each accepted native candidate: 256 arbitrary source comparisons, 4,096
coordinate-basis adjoint checks, two genuine public input sets, unchanged
captured outputs, and all runtime negative controls. The guarded field gate
compares 200,000 random pairs and 1,296 boundary pairs against untouched R20
field multiplication/square (402,592 results), retains 64 raw-product tests
including 15 overflow panics, and checks 24 invalid-constructor cases.

All three complete compositions pass both host proofs and all 3,281 wire
controls (3,280 checked rejections), clean SBF compilation and the complete
diagnostic-cap SVM gate. Before each full SBF build, all 1,024 source permutation
and inactive entries match the frozen SBF table.

`R24NativeBounds.lean` compiled in the existing cached Lean 4.31 workspace:
exit 0, **1.53s**, peak RSS **1,683,148KiB**, **0 swaps**. Four small leaves prove
the 32-bit product bound, canonical product bound, concrete accumulator upper
bounds, and commutative-ring tower identity. `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound` (subsets by theorem), no `sorryAx`.
The receipt pins the exact source hash and R23 base revision.

These leaves are **not** a complete Rust/machine-code refinement, a theorem
about every intermediate expression, or a privacy/soundness theorem. The local
source argument also checks subtraction nonnegativity using P² offsets and
canonical operands. Existing protocol security obligations remain open.

## Rejected experiments retained

- Fully inline canonical product: LLVM branch-target range failure.
- Outlined product without splitting scalar routines: SBF frame 4,672 exceeds
  4,096. A mistakenly launched simulation then failed on the scalar path.
  **Neither its reference result nor its failing scalar run is accepted evidence.**
  Native and full runtime runners now require the successful stack-safe build
  gate before execution; compiler exit zero alone is insufficient.
- Three widened M31 add/sub variants: frame diagnostics in the statement
  trace builder (6,336 bytes); earlier variants also hit LLVM branch range.
  Host equalities do not override these failures.
- Packed QM31 add/sub: passed 805,184 canonical field comparisons, 512 raw
  boundary outcome checks, source checks, stack gate and runtime controls, but
  was slower. Scalar native CU rose from 284,643/284,684 to 296,217/296,255.
  It is not installed in the complete candidate.

## Diagnostic profile, not a budget claim

An instrumented copy of B costs 1,860,552/1,862,137 CU. World-0 checkpoint
differences: semantic rounds 187,859; semantic terminal 409,681; preparation
116,607; opening points 68,431; records 285,893; Merkle 139,513; query/tail
115,882; ordinary 338,764; G/final 140,748. Remaining markers/framing account
for the rest. These are instrumented B intervals, **not isolated costs or a
breakdown of clean C**. The next target is source-exact semantic arithmetic,
with native field/kernel experiments measured against C.

## Reproduction and retention

Use `stage_r24_qm.py --outlined --split-scalar`, then
`stage_r24_inactive.py`, then `stage_r24_compose.py` from the frozen R23 stages.
Existing native/full runners perform host → SBF → capped SVM gates. The Solana
testing skill informed that cadence. All heavy jobs ran on the NUC over
Tailscale with MemorySwapMax=0: builds 5G/7G, runtime 2G/3G, analysis 1G/2G,
focused Lean 2G/3G. Logs retain commands, exit, time, RSS and swaps.

`collect_r24_native.py` retains successes **and failures**, exact changed
sources, manifests and logs under `evidence/r24-native/`. `check_r24_evidence.py`
audits those compact artifacts without repeating unchanged expensive tests.
Large binaries and generated build keys remain securely on the build host;
no account keys are copied into evidence or deleted.
