# Reuse the line coordinate already checked and computed

Research continuation of `992288fd577f647c810a506fc83b4811fb90f0e6`,
2026-09-09. This is a small retained arithmetic saving, not a new protocol.
Production/main, proof bytes, transcript, challenges and all acceptance checks
are unchanged. [Exact results](line-norm-results.json) pin every source/ELF and
the 50 executed maximum/ordinary/rollback cases.

## Measured complete transactions

| Shape | Previous maximum | New maximum | Same-pool V7 excess |
|---|---:|---:|---:|
| Transfer, current page | 1,061,150 | **1,060,912** | 20,089 |
| Transfer, rollover | 1,073,971 | **1,073,708** | 39,307 |
| Withdrawal, current page | 1,079,437 | **1,079,180** | 42,815 |
| Withdrawal, rollover | 1,092,468 | **1,092,232** | 43,348 |

The same twelve maximum-body proofs save **236–264 CU each**. Worst-observed
headroom is **107,768 CU** below the actual 1,200,000 TxV1 cap. These are
fixture maxima, not a universal bound or a V7 no-regression result.

The selected ELF is **1,009,440 bytes**, 200 more than split-prefix:

```text
cc8ca133f9a3ba6042cab39a53cc4264ed98fc7eead2915d257cc835d1a5418e
```

All 24 maximum-body cases, 24 ordinary-body cases and two failing-Token-CPI
rollback controls retain their outcomes, proof identity and protected-account
checks. Successful matrices use the same pinned Token3.5 SBF, Pool, Registry,
driver and runtime as the previous measurement. Rollback uses the intentionally
failing Token double *after actual V8 verification*, not that successful Token
control. Unsupported rollover stale/replay scenarios remain uncounted.

## Exact change and caller obligation

The query loop already computes `t=2*x*x-1` from each selected circle point
for final-domain evaluation. The preceding circle-norm kernel recomputed
`x*x` to form its even coefficient `A+B*x*x`. The new kernel uses

```text
(A+B/2) + (B/2)*t = A+B*x*x.
```

It borrows the existing ordered `xs` vector, leaving the other three
butterfly terms and all four slot signs unchanged. This saves **22 M31
squares**, charging one CM31 half and one CM31 addition at setup, one borrowed
slice and one additional length guard. Those operation counts are not a
substitute for the complete-transaction measurement.

The private helper requires that the borrowed vector is the one built from
the SAME immutable `Selected` points used for the chord denominators. The
actual callback provides it directly. It is not a public hint, and a length
check alone would not prove its values correct: a retained mismatched-line
counterexample makes that distinction explicit.

Zero chord/denominator and zero base-product guards remain. Parsing, auth,
gamma combination, quotient numerator, image/shifted-row relations, rho
injection, compact responses and terminal comparison are unchanged. The
previous table/unit-circle proof and split-prefix inversion proof are reused,
not replayed unchanged.

## Formal and executable evidence

[`LineNorm.lean`](experiments/LineNorm.lean) proves:

- The literal M31 half operation `(x>>1)|((x&1)<<30)` equals
  `x/2+(x%2)*2^30`, is canonical, and doubles to `x` modulo p.
- Both shifted intermediates and the result fit a 32-bit word. The proof
  does not rely solely on a field identity to justify machine operations.
- Applying the operation to each canonical CM31 limb gives the required
  CM31 half. Thus the affine rewrite has its actual source halving premise.
- The affine even part and all four norm outputs equal the previous ones.
- The source-shaped push-only loop produces exactly the ordered map of line
  coordinates and preserves its length.

This is kernel-checked field/bit-range and loop algebra plus source inspection;
it is **not** a translated Rust U32/Vec/LLVM/SBF refinement. Canonical source
arithmetic and immutable callback provenance remain explicit interfaces.

The optimized Rust gate compares 1,024 chord profiles at query lengths1–22,
including zero cases, plus 512 arbitrary-point affine comparisons, half-word
boundaries, private shape errors and mismatched-line rejection of equivalence.
The arbitrary-point tests compare the two expressions; they do not assert
that the earlier circle-specific norm is valid off-circle.

Final focused Lean: exit0, **4.09s**, **2,884,337,664-byte peak RSS**, zero swaps.
All ten audits use only standard propext/Classical.choice/Quot.sound; no
retained `sorry` or new axiom. The first preflight failed only because
`List.length_map` needed an explicit function argument. The corrected leaf
adds the actual CM31 half bridge and passes; the failed log is retained as
failure evidence, not counted as a proof. No whole-package replay was run.
Lean4.32.0, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, cached
Tactic olean hash and final source/olean hashes are recorded by the runner/log.

| NUC focused job | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Optimized test/build | 0 | 35.21 | 560,608 | 0 |
| SBF build | 0 | 33.93 | 591,444 | 0 |

Compilation dominates. Build scopes use High5/Max7GiB/jobs2; SVM scopes use
High3/Max4GiB, all SwapMax0. HostRust1.94.1, SBF tools1.54/Rust1.89-dev,
overflow checks, LiteSVM0.16.0/runtime4.2.1 remain pinned. Direct-r10 accesses
are ≤4,096 with no new stack warning; that is not a whole-machine stack proof.

The five CM31 coefficients still occupy40 payload bytes; the norm vector704;
the selected split-inverse requested M31 payload inventory1,408. No line
buffer is allocated by the new helper. Actual allocator/peak-memory delta
was not measured and is not inferred to be zero from equal payload sums.

## Reproduction and decision

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_line_norm.py
bash docs/research/v8-no-work-100-20260907/experiments/run_line_norm_lean.sh NEW_LOG
```

In the previously authorised, pinned NUC task COPY, install the three
`line-norm-*.patch` files against992288fd plus `line_norm.rs`, the updated
runners, and the unchanged preceding overlays. The auditor reconstructs those
source hashes. Run the focused `run_line_norm_nuc.sh NEW_LOG`, then
`run_complete_build_nuc.sh line-norm NEW_LOG`. The final logs record exact
commands. The ordinary/maximum matrix commands use `ASPIS_POOL_ZERO_FAST=1`,
`ASPIS_COMPLETE_TX_LIMIT=1200000`, pinned Token3.5 variables, and
`run_complete_matrix_nuc.sh line-norm NEW_OUTPUT`; add
`ASPIS_COMPLETE_MAX_FIXTURES=1` only for the maximum matrix. The two rollback
controls use only `ASPIS_V8_LINE_NORM=1` with
`run_pool_zero_cases_nuc.sh rollback NEW_OUTPUT`. No real witnesses or binary
proof data are published in this evidence.

Keep the change: it is byte/transcript-neutral and improves every measured
maximum-body transaction. The body census remains
`697*16+52+24+22*621+2*296*26 = 40,282`; no prover-time measurement or new
security error term is inferred. Global recovery, adaptive full-view ZK and
resource-bounded FS retain their prior open status.

The next useful experiment is a **fresh selected-build stage profile**. Several
later arithmetic/authentication changes have invalidated the old profile as
a guide to current bottlenecks. Instrumented counts must remain diagnostic,
separate from the quiet selected ELF and its complete measured CU.
