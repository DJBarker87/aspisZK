# Expanded quotient fold: a correct but small retained saving

Research continuation of `074daa2fd0636a577f87bb84075e9ad6fd4f5662`,
2026-09-09. The fresh [selected-source profile](line-profile-review.md)
identified37,619 instrumented CU in quotient products/folds. This continuation
tests a different reduction layout for the latter, proves its algebra and
retains the measured small win. It does not claim to remove the entire bucket.

## Complete result

| Shape | Previous maximum | New maximum | Same-pool selected V7 excess |
|---|---:|---:|---:|
| Transfer, current page | 1,060,912 | **1,060,825** | 20,002 |
| Transfer, rollover | 1,073,708 | **1,073,615** | 39,214 |
| Withdrawal, current page | 1,079,180 | **1,079,103** | 42,738 |
| Withdrawal, rollover | 1,092,232 | **1,092,138** | 43,254 |

The same twelve maximum-body proofs improve by **55–102 CU each**. All24
maximum-body cases,24 ordinary-body cases and two failing-Token-CPI rollback
controls retain outcomes and protected-account checks. These execute the real
research V8 verifier and Pool settlement/rollback, not an accepting-verifier
double. Successful matrices use the pinned Token3.5 SBF; the two intentional
post-verifier failure controls use the separately specified Token double.

The actual TxV1 cap is1,200,000. Worst-observed headroom is107,862 CU; the
body remains40,282 bytes. These are fixture maxima, not universal CU or V7
no-regression results. Same proofs, Pool, Registry, Token, driver and runtime
are checked by [the auditor](experiments/audit_quotient_fold.py) and pinned in
[machine-readable results](quotient-fold-results.json).

The selected quiet ELF is1,010,904 bytes, **1,464 bytes larger** than the
previous control:

```text
cdcc870db14a20cc30424b0193ba3c057c9784386391fd58286c7a9566fa1b13
```

## What is fused

Let `A=v0+v1`, `B=v2+v3`, `C=v0-v1`, `D=v2-v3`,
`ix=1/(2x)`, `iy=1/(2y)`. The existing normalized sequential fold is

```text
pos = A/2 + alpha*C*iy
neg = B/2 - alpha*D*iy
fold = (pos+neg)/2 + alpha^2*(pos-neg)*ix.
```

The new implementation computes

```text
(A+B)/4 + sum_products3_prepared(
  [alpha, alpha^2, alpha^3],
  [(C-D)*(iy/2), (A-B)*(ix/2), (C+D)*(ix*iy)]).
```

The three challenge powers are prepared once outside the q22 loop. The
existing checked three-product kernel accumulates product channels before
reducing, instead of separately reducing three prepared QM31 products.
The point order stays `(x,y),(x,-y),(-x,-y),(-x,y)`, including the negative
second-pair alpha term. Numerator-times-chord-inverse products are unchanged.

This is not the previously rejected four-channel gamma fusion: it changes a
different downstream normalized butterfly, uses three different alpha powers,
and makes no assumption about gamma powers, decoded columns or honest zeros.

Costs charged in the source operation model:

- One extra QM31 product to prepare alpha^3 globally, and one extra prepared
  multiplier (36 payload bytes in the existing nine-limb representation).
- One extra M31 product and two M31 halves per query.
- Two rather than three QM31 halves per query; nine QM31 add/sub operations
  in either expression, excluding arithmetic internal to multiplication.
- Three mixed-width value scalings remain. The old three prepared QM31
  products become one existing three-product sum; no new unchecked accumulator
  or expanded machine-word range is introduced.

The new layout adds no heap allocations. Temporary arrays/register lifetimes
change; the actual peak allocator/RSS delta is not inferred from operation
counts. The emitted direct-r10 frame audit stays≤4,096 with no new warning.
It is not a whole-machine stack proof. The small measured net gain is the
decision criterion; the algebra alone did not promise a large saving.

## Proof and source boundary

[`QuotientFold.lean`](experiments/QuotientFold.lean) proves the equality of
the literal sequential and expanded expressions symbolically over a
commutative ring. It even holds for an arbitrary shared half scalar h: no
honest-proof, nonzero-coordinate or actual-inverse hypothesis is used in the
identity. It also proves prepared-power equality, handles alpha0, and preserves
a wrong-slot-sign counterexample.

The earlier `LineNorm` bit/range-to-field half bridge supplies the meaning of
the unchanged M31/CM31 halves. The QM31 half is componentwise. The existing
`M31RangeKernels` fixed-channel bounds and previously retained field overlays
remain unchanged. Three canonical products per channel fit the existing
bounded accumulator. Both input differences/sums and mixed-scaled values are
canonical outputs of the already selected field operations, not unreduced
integers passed into the kernel.

This is **kernel-checked source-shaped algebra plus audited source mapping and
differential tests**, not a translated complete Rust/LLVM/SBF equivalence
theorem. It does not assert whole-protocol soundness or omit the existing
source/refinement boundary. Malformed parsing/authentication paths and all
zero-denominator checks are unchanged; the new helper receives only values
after those same checks.

Optimized actual-QM31 tests compare4,096 arbitrary value/challenge/coordinate
profiles and16 single-slot basis cases to the retained sequential source.
They include zero challenges, zero inverse inputs as algebraic controls,
maximal canonical limbs and each slot. A second focused test build changes
the cfg environment to the selected range/hybrid/lazy/channel/prepared kernels
and repeats that changed-code coverage. It is not an unchanged regression.

The one focused Lean leaf passed with four axiom audits, only standard
propext/Quot.sound, no `sorry` or new axiom: exit0,5.79s,
2,874,490,880-byte peak RSS,zero swaps. Source/olean and cached Mathlib
Tactic hashes are in the log. Lean4.32.0 and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` are unchanged. No broad proof replay.

| Focused NUC job | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Standard arithmetic optimized test/build | 0 | 35.09 | 560,712 | 0 |
| Selected arithmetic optimized test/build | 0 | 21.82 | 514,668 | 0 |
| Quiet SBF build | 0 | 34.36 | 592,360 | 0 |

Compilation dominates. Builds use High5/Max7GiB/jobs2; SVM uses High3/Max4GiB,
all SwapMax0. Checked optimized SBF tools1.54/Rust1.89-dev, hostRust1.94.1 and
LiteSVM0.16.0/runtime4.2.1 remain pinned. A first outer launch had a typed
`20260908` research-directory path instead of `20260907` for its *next* SBF
command: shell exit127 after the successful test. Correcting that path launched
only the SBF build; it did not repeat the completed test or change any source.

## Reproduction and next decision

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_quotient_fold.py
bash docs/research/v8-no-work-100-20260907/experiments/run_quotient_fold_lean.sh NEW_LOG
```

On the authorised pinned NUC task COPY, apply `quotient-fused-callback.patch`
to074daa2f and add `quotient_fold.rs` plus updated runners. The source guard
checks all five relevant hashes. Run `run_quotient_fold_nuc.sh NEW_LOG`, and
with `ASPIS_QUOTIENT_SELECTED_KERNELS=1` for the selected-field configuration.
Build with `run_complete_build_nuc.sh quotient-fused NEW_LOG`.
The maximum/ordinary commands and pinned programs follow line-norm with mode
`quotient-fused`; rollback uses `ASPIS_V8_QUOTIENT_FUSED=1`. Evidence logs record
the complete commands. Do not silently rebuild the old line-norm profile with
the changed callback; that named control's source guard intentionally refuses it.

Retain the small win: same bytes/transcript/checks, lower CU on all measured
maximum proofs. No new message, challenge, hint, nonce, proof padding or
prover search is introduced. Body census remains
`697*16+52+24+22*621+2*296*26=40,282`. There is no new prover-time measurement
or security probability; global recovery, adaptive full-view privacy and the
resource-bounded FS theorem keep their existing status.

**Next bounded experiment:** the final256 coefficient fold still evaluates
`c0 + sum_products3_prepared(...)`. The source already has an affine
three-product kernel that can include c0 in the reduction channels. Prove its
concrete constant-channel mapping/range from the selected input path, then
compare all four quiet complete shapes. It must preserve compact boundaries
and final equality. Reject it if the integrated CU regresses or its source
range obligation cannot be discharged; do not book its possible savings now.
This is not a claim that every safe optimisation has been exhausted.
