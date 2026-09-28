# R33: admissible G core and a low-support residual minor

Parent `ff6056e5596470c7b473d316e599a37f5fa837aa` (R32).
Branch `research/v8-r33-admissible-g-residual-20260928`.

**Result:** R32's core theorem is composed with the real rational-circle
chord normalization. On both retained genuine prefixes, the fixed core
minor is invertible and all 276 compatible targets are recovered through
the 17-by-428 Schur residual system. Its selected rank-13 minor uses the
same first 13 free columns in both prefixes. Those columns have zero G
core, so the minor itself contains no core inverse.

This is not universal residual coverage or full privacy. No verifier,
protocol profile, proof format, transcript, source sampler or negative
regression changed. Selected CU remains 1,620,236 / 1,621,719; both actual
1M runs remain exhausted. No unchanged SBF test or proof generation ran.

## Admissible source parameters

`SparseGAdmissible.lean` imports the retained `NormalizedChord.lean` and
R32's current-layout polynomial minor. It proves chord homogeneity,
homogeneity of the selected matrix and its vector multiplication, and
core surjectivity for rational-circle points under the explicit conditions:

```
2 != 0;  1+u^2 != 0;  1+v^2 != 0;  v != u;
eval(alpha,u,v, currentMinorPolynomial) != 0.
```

The actual chord is the normalized chord multiplied by the nonzero scale
`2*(v-u)/((1+u²)*(1+v²))`. The result no longer treats the normalized
chord as though it were the source's unscaled chord. It still makes no
claim about the probability of the final determinant condition.

The checker derives u and v from each genuine prefix's point coordinates,
checks their denominators/distinctness, reconstructs both original circle
points, and checks all three actual chord coefficients. For all 699
kernel columns it checks every sparse G coin against the scaled normalized
direct-source column: **189,429 comparisons per prefix**. No sampled
parameter, query, commitment, beta or proof field is replaced.

## Exact residual equation

Split the 699 kernel columns into R31's 271 selected columns and their
428-column complement. Write the core equation and remaining observations as

```
A*u + F*v = a
B*u + D*v = b.
```

Since A is invertible, the remaining equation is exactly

```
(D - B*A^-1*F)*v = b - B*A^-1*a,
u = A^-1*(a-F*v).
```

`GResidualSchur.lean` reuses R11's posterior-elimination identity to prove
this coverage equivalence in both directions. The theorem explicitly
requires a linear equivalence for A; it does not assume the residual
map is surjective or claim a distribution/simulator theorem.

The source checker performs this elimination on the actual matrix and
targets. **4,320 residual RHS entries change in each prefix.** Its negative
control requires this change: omitting the `B*A^-1*a` term is not valid.
The original 17 residual rows all remain in the solve and recheck.

## Four retained source dependencies

The residual rows are `(point0,point1,point2,ordinaryPolynomial[0..6],
structuredPolynomial[0..6])`. On each of the 699 source kernel columns the
checker confirms:

1. point0 is the actual structured functional of the 271 core coins;
2. the ordinary polynomial evaluates to zero at alpha;
3. the structured polynomial evaluates to zero at alpha;
4. the structured polynomial's source `boundary_sum` equals
   `kappa*point0 + kappa²*point1 + kappa³*point2`.

These explain the candidate 13-dimensional compatible residual image.
Here they are exact source checks on two prefixes, not yet a universal
source proof of those four dependencies or of residual coverage.

The target basis is unchanged from R29: 270 semantic directions in the
kernel of the actual structured coin functional, and six ordinary
polynomial directions `X^i-alpha^i`. All retained point/raw/OOD/final/
balance observations and the structured polynomial target are zero.

For **every** target, the checker solves the residual system, reconstructs
the 699 kernel coefficients, checks all 288 original core/residual equations,
constructs the actual 1024-entry quotient, applies the pinned chord and
T163 inverse, then rechecks actual coins, raw88, points, both OOD values,
Final256, balance, image tails and both full seven-coefficient polynomials.
Perturbing a selected core coefficient is detected for all 276 targets.

## The useful low-support structure

Both prefixes choose these residual rows:

```
[1,2,3,4,5,6,7,8,10,11,12,13,15]
```

and the first 13 free columns, which are original kernel columns 0..12.
They are the three channels at degrees 22,23,24,25, followed by channel B
at degree 26. Their quotient support is below 106. The raw-kernel remainder
has degree below 22 and does not increase this upper support.

The checker explicitly verifies the support of those 13 constructed columns,
all 271 core zeros for each, and equality of their Schur entries to the
unadjusted residual entries. Thus this **13-by-13 minor** does not require
the 271-by-271 inverse in its entries. The residual **RHS still does**.

`LowGResidualSupport.lean` proves the general support bound: quotient
support below `2*n` gives chord support below `2*n+3`, assuming each scatter
edge increases the index by at most one. For n=53, all encoded coordinates
from 109 upward are zero, including every G read at `128+3*i`.

`SourceEdgeGrowth.lean` discharges that edge premise for the concrete R17
source-shaped 512/513 schedules. It checks only bounded pure integer index
schedules (at most 513 inputs, ten-bit fuel), then transfers the result to
arbitrary field weights using `weighted_targets`. There is no dense field
recurrence or determinant normalization. `sourceChord_low_g_zero` composes
the finite zero-extension/chord model with this support result for arbitrary
half, alpha-independent input values and chord coefficients.

This is a symbolic source-shaped support result, not an extracted Rust
field proof. The current Rust kernel construction is additionally checked
at both prefixes. General natural-basis/source correspondence and the
remaining residual determinant still require their own bridges.

## Receipts

Source stage `/home/dombarker/project-offloads/aspis-r33-residual-20260928-c`:
188 pins, only the new host checker and host Cargo target differ from R31.
All inherited non-Cargo pins remain exact. The first host compile needed
an explicit `Vec<usize>` pivot annotation; its exit-101 receipt is retained.
The source was then extended with the low-support assertions, giving a
specific reason for the final source rerun.

| Final focused target | Exit | Wall | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Host release/offline/locked compile | 0 | 19.19s | 518,640 | 0 |
| World0 residual/source reconstruction | 0 | 1.46s | 29,920 | 0 |
| World1 residual/source reconstruction | 0 | 1.45s | 29,920 | 0 |
| `SparseGAdmissible.lean`, 4 declarations | 0 | 1.05s | 2,265,252 | 0 |
| `GResidualSchur.lean`, 2 declarations | 0 | 0.83s | 1,559,468 | 0 |
| `LowGResidualSupport.lean`, 4 declarations | 0 | 0.80s | 1,602,820 | 0 |
| `SourceEdgeGrowth.lean`, 5 declarations | 0 | 1.64s | 1,798,784 | 0 |

All **15 new declarations** have `#print axioms` audits containing only
standard propext/Classical.choice/Quot.sound; no sorryAx or added axiom.
Three missing small prerequisite objects were compiled once; R32's nine
objects and subsequent dependent objects were reused by source hash.
The dependency-free Lean 4.32 runner avoids resolving exported caches.
Rust scope 5G/7G, Lean scope 3G/5G, MemorySwapMax0, TasksMax128; Rust release
overflow checks enabled. The Solana testing skill kept host/source results
separate from CU/production execution claims.

Each prefix has **79,488 original equation checks**, 276 full source
reconstructions and 276 corruption controls. The two 2704-byte public
residual minors are committed with checksums. Complete 3,086,784-byte public
right-inverse tables remain on the NUC; repository receipts bind their hash
and length. They are not claimed as kernel-checked certificates.

Evidence gate:

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r33_evidence.py
```

## First remaining proposition

Source-bind the fixed **low 13-by-13 residual minor** as a polynomial/rational
function of the real prefix, retaining its query-root factor and all point/
polynomial observations. Prove sufficient compatible-image coverage for
admissible contexts, or a source-justified exception bound. Two nonzero
evaluations are not a universal rank theorem. Treating query roots or
earlier semantic challenges as independent uniform variables without the
shared-oracle/first-hit proof is not allowed.

The H1 current-layout core/residual theorem, full Rust/source refinements,
posterior-preserving adaptive simulator, coherent pre-beta extraction,
commitment and seed-expansion hops, visible failures/retries/publication,
explicit losses and the 1M execution target remain separate release gates.
No merge, deployment or wallet operation occurred.
