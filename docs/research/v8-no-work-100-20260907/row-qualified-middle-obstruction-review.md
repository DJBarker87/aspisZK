# Row-qualified middle-gamma obstruction and linear-map reduction

Status: the optimized exact finite-field control passed. The corrected
`FixedLinearMapCurveReductionV2.lean` is **kernel-checked**, with nine
standard-only axiom audits. This is not a counterexample to the actual retained
higher-Y event or to its proposed 34,810,510-gamma bound.

## Result and remaining target

Three nonzero, source-related ordinary MLE rows and the two actual OOD
evaluation constraints do not, by their rank alone, force adaptive
row-correct candidates to lie on one pre-gamma degree-28 curve. An exact
small circle-code example preserves all 37 gamma values, each with 29/37
complete-fibre support, while its fixed received curves have gamma degree
at most 28. The candidate curve has degree 29 and lies in the common row
kernel. The ordinary rows have rank three on the six-dimensional quotient
image subspace; no zero ordinary weights are used.

The actual target remains the union, outside `Good` and the common-row
singular set, of gammas admitting the **same** image-valid quotient with
200808..252847 fibres, correct source rows, actual final identity and a root
of a retained prime factor of the literal interpolation parent with Y-degree
at least three. Neither this control nor the generic linear-map reduction
establishes that last factor/parent condition. In particular, 37 examples
cannot numerically refute a bound of 34,810,510.

The existing `no-early-middle-moment-obstruction-review.md` quantifies the
gap: extending the unqualified layer cake through 252847 gives about
97.1879 bits. Its sufficient 34,810,510 middle-union cap is a target, not a
consequence of five linear equations. No new probability, independence,
sampler law or extra suffix repair charge is asserted here.

## Literal source boundary and reusable checked bridges

All paths in this section are relative to this research directory unless
otherwise stated. The investigation began at research `5d65daeb`; the new
generic draft was frozen with current HEAD
`2f012db3288c902f43659afb2e3137d15008597b`.

| Boundary / fact | Exact source or theorem | What must not be inferred |
| --- | --- | --- |
| C1 root, then lambda/chi; C2 root, then semantic challenges and ten semantic rounds | `experiments/inactive_row_binding.rs`, `semantic` | The later semantic point is not available when choosing C1. |
| Three related points are z, binary successor, and XOR 12 | `crates/aspis-core/src/v6_transcript.rs`, `v6_statement_points` | They are neither three independently sampled points nor arbitrary covectors. |
| 87 point claims; OOD point 0/answer 0; distinct point 1/answer 1; nonce; gamma | `inactive_row_binding.rs`, `points_absorb`, `to_gamma` | The second point draw follows the first answer; the complete prefix is fixed before gamma. |
| Inactive claim after gamma; then kappa with ordinary powers kappa, kappa², kappa³ | `inactive_row_binding.rs`, corrected `prepare`; `ClaimTransport.corrected_prepare_discrepancy` | Inactive is not an additional fixed pre-gamma degree-28 RHS constraint. |
| Chord/interpolant correction, image gate, tau, first relation response, alpha, adaptive final256 | `prepare`, `relation`; `OODInterpolantRows.Data.source_prior` | The quotient witnessing the final is not fixed before alpha. |
| Row discrepancy for an arbitrary image-valid Q | `ComponentRows.point_error` | The discrepancy need not be a nonzero degree-28 polynomial in gamma. |
| Degree-28 error polynomial for one fixed component tuple p | `ClaimTransport.component_error_eval`, `component_error_degree`; `ComponentRows.recovered_point_error` | The representation `original Q = batch gamma p` is a prerequisite, not a conclusion. |
| Exact image reconstruction and OOD equations | `InterleavedChordRows.message_circle_eval`; `SelectedHigherYBranch.qualified_points` | These give linear constraints on each actual original message, not candidate coherence across gammas. |
| Actual supported candidate and retained higher factor | `SelectedHigherYBranch.Qualified`, `higher_prefix_branch`; `SelectedHigherYHighSupport.Witness` | A generic row-kernel example is not automatically in this event. |

The complete research verifier also checks the selected payment semantic
terminal (`verify` and `terminal`). Passing the row/image equations alone is
not passing this verifier. Authentication and the actual query schedule are
also outside the control.

## Exact optimized control

Files: `experiments/RowQualifiedMiddleControl.rs`, immutable matching
`row-qualified-middle-control-local-v1-source.txt`, and
`row-qualified-middle-control-local-v1.log`. The optimized executable is
retained locally in the ignored `experiments/target/RowQualifiedMiddleControl`.

The field is F65537. Natural-eight circle messages use the line basis
`1, x, 2*x²-1, x*(2*x²-1)` with y in the low bit. The OOD points are `(1,0)`
and `(0,1)`, the chord is `D=1-x-y`, both answers and their interpolant are
zero, and the inverse guard is one. The quotient image constraints are
`q[7]=0` and `q[6]=q[5]`; exact multiplication by D reconstructs a natural-eight
original message.

The ten-coordinate seed is `[2,3,5,7,11,13,17,19,23,29]`. The control applies
the literal successor carry and XOR-12 formulas, then the exact ten-bit MLE
weight formula to the first eight entries (the message is zero-padded).
Every tested ordinary-row weight is nonzero. Optimized elimination of the
three-by-six image/row matrix gives rank three and the nonzero kernel pair

```
Q = [58142,18991,4309,1,0,0,0,0]
V = [46492,59154,44472,42238,7341,32768,32769,0] = D*Q.
```

Take gamma nodes 1..37 and their 37 cyclic 29-element subsets J. Set
`H_J(Z)=product(g in J)(Z-g)` and `R_J(Z)=Z^29-H_J(Z)`, so each R_J has degree
at most 28. Choose 3700 complete four-sign circle fibres on which both D and
V are nonzero, with 100 fibres in each group J. On this group the fixed
received curve is `R_J(Z)*V(x,y)`. Its first 26 coefficients are fixed C1;
its last three are fixed C2, hence the residual helper after the gamma^26
shift has degree **two**, not 28. All these arrays are fixed before gamma.

For node g choose original `U_g=g^29*V` and quotient `Q_g=g^29*Q`.
It agrees on exactly 2900/3700 complete fibres. This ratio is strictly within
the selected middle-band ratios. All three ordinary rows and both OOD rows
are zero at every g. A post-gamma inactive claim can equal the actual
inactive functional on U_g, without assuming its covector is zero.

The executable checks 547,600 original/quotient symbol cases, the image
identities, rank, nonzero weights, OOD values, and support counts. Its printed
`helper_GRS_degree=2` refers to the degree-two rational-coordinate chord
denominator; it is distinct from the residual C2 gamma-degree-two fact just
explained. Claims/error polynomials have degree at most 28; the adaptive
candidate U_g deliberately has gamma degree 29.

There is also a small-code own-support argument. A nonzero natural-eight
circle function has at most eight zeros on the rational chart. If an
arbitrary 26-component natural-eight tuple owns at least nine symbols in one
group, each of its components equals that group's coefficient multiple of
V. The control checks that all first-26 R_J coefficient vectors are distinct,
so that tuple owns exactly the 400 symbols of that group. Otherwise it owns
at most `37*8=296` symbols. Thus own support is at most 400, below the scaled
selected early threshold (`400*1048576 < 38228*14800`). This argument is
mathematical; the program checks its finite inputs and arithmetic, not an
exhaustive enumeration of all codewords or a new Lean theorem.

Similarly U_g is not within the scaled Good radius: it has 800 bad fibres,
where the scaled radius is less than 132. Any other natural-eight codeword
meeting that radius would share more than eight symbols with U_g and hence
equal it. These are scaled small-code statements, not the actual QM31
`earlyC1 = none` or `Good` theorems.

The construction guesses/fixes z before building its C1 arrays. In the
actual transcript C1 precedes z. Thus it can falsify a universal claim about
every fixed completed prefix but does **not** establish a positive acceptance
probability against fresh semantic challenges. It also does not construct
the selected canonical interpolation parent or a retained Y≥3 factor.

## Checked generic fixed-map theorem

`experiments/FixedLinearMapCurveReductionV2.lean` has nine audit declarations.
The original filename is retained as the exact failed v1 source, not as a
second successful target. Both use namespace `AspisV8.FixedLinearMapCurveReduction`.
For a fixed K-linear map `L : V -> W` and fixed `b : Fin(d+1) -> W`, put
`B(g)=sum_i g^i * b_i` and `Feasible={g in Gamma | B(g) in range(L)}`.

* If one coefficient is outside range(L), a derived separating functional
  annihilates range(L) but gives a nonzero scalar polynomial on B. Its degree
  is at most d, so **Feasible has at most d elements**. It is not the set of
  infeasible gammas that is small.
* If every coefficient is in the range, choose one fixed tuple p of lifts.
  For every later gamma and every candidate U, including an arbitrarily
  adaptive post-alpha choice,
  `L(U)=B(gamma) iff U-batch(gamma,p) in ker(L)`.
* Consequently more than d feasible values gives a fixed particular curve,
  but not `U=batch(gamma,p)` and not coherence of all accepted candidates.

The separation is derived with
`Submodule.exists_dual_map_eq_bot_of_notMem`; no supplied certificate is
assumed. The selected d=28 instance would package the three fixed semantic
rows and two fixed OOD evaluations as one five-output linear map on original
messages, with the five claim/answer coefficient vectors as b. That exact
packaging/transport is not implemented in this generic leaf. Its p is fixed
after the completed OOD prefix, not before C1 or before the semantic rounds.

Even that adapter would leave the decisive missing theorem: bound the
support-qualified, retained-higher-factor candidates among the allowed
kernel offsets (or derive enough coefficientwise support to enter the fixed
early C1 family). Linear feasibility alone supplies neither condition.
The checked `SelectedRegularTailSum.tail_sum_bound` remains available, but
its degree budget is not divided by the row rank. A codimension-five kernel
can still contain messages of maximum allowed spatial degree.

## Reproducibility and provenance

Local focused command, with no NUC or Lean invocation:

```
/usr/bin/time -l sh -c 'rustc --edition=2021 -O -C overflow-checks=yes docs/research/v8-no-work-100-20260907/experiments/RowQualifiedMiddleControl.rs -o /tmp/aspis-row-qualified-control.3zem9M/control && /tmp/aspis-row-qualified-control.3zem9M/control'
```

Output was retained through tee. The observed shell command exited zero
and the log contains all PASS records. Combined compilation plus execution:
1.71 s wall, 133,169,152 **bytes** peak RSS (macOS time), zero swaps.
Compiler: rustc 1.93.0, commit `254b59607d4417e9dffbc307138ae5c86280fe4c`,
target `aarch64-apple-darwin`, LLVM 21.1.8. This is a tiny optimized control,
not a large release gate or a selected protocol execution.

SHA256 values:

* Rust source and immutable source snapshot:
  `16dca3b5e78ab1262d869beeedf459f29fe4f48dad08d86116c5b252b3c845b5`.
* Execution log:
  `f6a6aa55f9e0ad229a2c32126a015584a2fc9e3ea6ee649d5c049b3c7a77d5a1`.
* Retained optimized binary:
  `c83c287d3ec1dde1c2d72700e73f5171b632396e9cb9c526b3ead499fbb8ec6b`.
  This digest was taken **after** execution and artifact copy; it is not an
  execution-time binary checksum.
* Failed v1 Lean source and immutable snapshot:
  `09c064dedc3282541870a0dd50e49dc3fa9d21042a8f96ba7a7d48cd75d73d4b`.

## Focused Lean evidence

After the unrelated V7 job ended, the coordinator ran only the new targets
on the Tailscale NUC. No package replay or source-map instantiation was run.
Both attempt triplets are retained as `experiments/fixed-linear-map-v1` and
`fixed-linear-map-v2` with suffixes `.log`, `-manifest.json`, `-source.txt`.

| Attempt | Exact target | Exit | Wall | Peak RSS (KiB) | Swap | Result |
| --- | --- | --- | --- | --- | --- | --- |
| v1 | FixedLinearMapCurveReduction | 1 | 1.42 s | 2,239,124 | 0 | Missing explicit polynomial sum-evaluation rewrite and failed bottom-membership projection; cascading sorryAx rejected. |
| v2 | FixedLinearMapCurveReductionV2 | 0 | 1.41 s | 2,250,756 | 0 | Nine audits, all only propext, Classical.choice, Quot.sound; no errors, warnings or sorryAx. |

V2 changes only those two elaboration steps: `eval_finsetSum` / `eval_monomial`
and termwise commutativity, then `simpa using member`. No theorem statement,
import, heartbeat, recursion-depth or resource cap changed. The nine audited
declarations are `scalar_coeff`, `scalar_degree`, `scalar_eval`, `curve_map`,
`feasible_card_of_separator`, `feasible_card_of_coefficient_outside`,
`solution_iff_kernel_offset`, `range_kernel_dichotomy`, and
`dense_feasible_particular_curve`.

The inherited task is `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`;
actual network endpoint is `dombarker@100.108.41.90` with key alias `nuc.local`
(not a network hostname). Runner creation/source baseline remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, separate from this continuation's
source parent. Borrowed V7 pin remains
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. Lean 4.32.0 commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`; Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`.

Each run used `lean -j1 -M9500` in its own scope, MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%. V2 records 1005 registered
provenance entries unchanged before/after. This is the registered overlay
check, not a replay of native package compilation. The new theorem imports
only native `Mathlib.LinearAlgebra.Dual.Lemmas` and
`Mathlib.Algebra.Polynomial.Roots`.

Exact SHA256 evidence:

* v1 log `a583ab2bd09c9887191ff09cf747d7f55c37a752be02b48a91408db3756989d7`.
* v1 manifest `4697ddc0fdcfb0ed8f4dec478e3827e57eca8e6d90288ab454e59827215053c1`.
* v2 source/snapshot `ee2383eef76a418362630018f1b82b27a99160a6ff5d80170dc62dadf446535f`.
* v2 log `8c6685b7d4c2d3be8cbaa243e797cb4766f54c8cb2655384e2e3ca00c79cd9f5`.
* v2 manifest `8b7e3e3057c6059f1e0226baa58eec46db7c77c64e4703474b57fb45769497a1`.
* v2 output, as hashed by the NUC run:
  `115c8110a6ae9a63f39fcc5f4c2e71622d2cb3a2a0dfd945c45ba9b6825e7f3e`.
* runner `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

Conclusion: the fixed-map dichotomy is now proved; the actual row-map
instantiation, coefficientwise support of its particular lift, and a
retained-factor bound on the adaptive kernel offsets remain separate
obligations. This result does not close the Y≥3 middle band.
