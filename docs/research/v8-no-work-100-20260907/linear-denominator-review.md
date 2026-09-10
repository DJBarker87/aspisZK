# Retained linear factors: a pre-OOD denominator obstruction

Parent revision: `2f6d82fef294410367aa1781fb924af7c38deab9`.
The three main leaves and the separate symbolic degree-drop regression
are all kernel-checked and frozen.

## Proved classification

Write a fixed prime linear-Y factor as `F=A(X,Z)Y+B(X,Z)`. For positive
Z-degree `A`, define the fixed X-polynomial

`E_F(X) = leadingCoeff_Z(A)(X) * resultant_Z(A,B)(X)`.

[LinearDenominatorPrimitive](experiments/LinearDenominatorPrimitive.lean)
derives the resultant's nonvanishing from primitivity of `AY+B` and
`A != 0`. It does not assume coprimality over `K(X)`. A hypothetical common
divisor over `K(X)[Z]` is cleared to its primitive integer normalization;
Gauss descent makes that primitive polynomial divide both A and B over
`K[X][Z]`, contradicting Y-primitivity unless it is a unit. This carefully
avoids claiming that the multivariate coefficient ring is Bezout.

[LinearDenominatorOOD](experiments/LinearDenominatorOOD.lean) proves that
any literal polynomial OOD identity

`A(t,Z)*answer(Z)+B(t,Z)=0`

forces `E_F(t)=0`. If the leading coefficient vanishes, the first factor
handles the degree drop. Otherwise A retains its original positive degree
and the polynomial identity makes the original-degree Sylvester resultant
vanish. B may lose degree, and A and B may have unequal degrees. No
separability, common-root extension, fixed answer, or answer degree bound
is needed for this denominator case.

The coefficient bound `degree_X(A_j),degree_X(B_j)≤H` gives

`degree_X(E_F) ≤ (degree_Z A + degree_Z B + 1)*H`.

[LinearDenominatorFactors](experiments/LinearDenominatorFactors.lean)
derives primitivity and nonzero A from actual prime-factor membership and
linear Y-degree. Its second branch reuses the root agent's
`GammaConstantLinear.excess_numerator_obstruction`: if A is Z-constant but
B has degree above the answer degree, one nonzero X coefficient of B
must vanish at every retained OOD point.

Multiplying these certificates over the fixed parent factor multiset gives
one polynomial E, chosen from P before either OOD point, with

`E != 0`,

`degree_X E ≤ (2*trivariateYZWeight(c,P)+1)*degree_X P`.

Every retained linear factor is then either `degree_Z A=0` and
`degree_Z B≤c`, or both actual OOD points are roots of this same E. The
proof keeps the same factor throughout and permits answers to depend
arbitrarily and sequentially on the OOD points. It sums the individual
factor X-degrees using the exact V7 factor product; it does not charge the
parent's X-degree separately for each factor.

For the selected parent ceilings, the numerical degree cap is
`(2*117077+1)*114687 = 26,854,534,485` (billions, not millions). This is a
polynomial degree, not a verifier soundness bound. Two sampled points can
be interpreted via a squared root count only under an independently
established suitable sequential sampling law. No actual sampler, Fiat–Shamir,
hash budget, proof acceptance, or extraction probability is proved here.

## Degeneracy checks

The exact symbolic degree-drop regression is `A=XZ+1`, `B=1`:
`F=(XZ+1)Y+1` is primitive and prime; the original resultant is 1, but
at `X=0` the answer `-1` is a polynomial OOD identity. Thus a resultant-only
obstruction is false even for a valid prime linear factor. The added leading
coefficient is X and correctly vanishes. The checked
[LinearDenominatorRegression](experiments/LinearDenominatorRegression.lean)
proves its prime/primitive factor status and each of these exact identities.

Additional mathematical checks, not additional executed source fixtures:

- `A=Z,B=0` would have zero resultant, but `F=ZY` is not prime and violates
  the primitive-content premise.
- `A=0` is inconsistent with linear Y-degree.
- `A=Z,B=1` has X-constant nonzero certificate; no polynomial OOD answer
  exists at any X.
- `A=Z,B=Z²+X` has unequal Z-degrees and resultant X; at X=0 the answer
  `-Z` is a valid identity caught by that root.

The resulting small-linear class is consumed by the root's actual-message
classification. Higher-Y factors, shared own support, base-field/canonical
descent, early-C1 timing, semantic/payment validity, and efficient extraction
remain separate obligations. A fixed factor's sparse hit set is not the
same as saying that the factor's sparse property is itself unlikely.

## Reuse and exact evidence

V7Smooth's determinant-level resultant degree proof is reused unchanged,
source SHA-256 `af4f75fd298825dc5d14f8315136bfd9d7bd550831dad834aa00e422b7a35c8a`.
V7FactorBudgets source SHA-256 is
`ced62421bc10c37b03bbe780b0c7b94183ced4ddb1f42128aeb12637acab7866`.
The exact all-factor X-degree sum is reused from `MonicFactorOOD`, and
the YZ-weight sum from `FactorIdentityCover`, both frozen prior leaves.
No speculative mutable main source is imported.

NUC scope: `/home/dombarker/project-offloads/aspis-denominator.QNcd5G`.
Runner [run_denominator_nuc.sh](experiments/run_denominator_nuc.sh), SHA-256
`4a9ee5f24b89642c6a323db95dde0cded2097769c141ed6eb4dcdd16ef8d8935`.
MemoryHigh8GiB, MemoryMax10GiB, SwapMax0, CPU200%, `lean -j1 -M9500`.
Borrowed source pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`;
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. Full source/olean
closure preflight and unchanged postflight are recorded per run. Native
package caches are reused, not replayed from source in this turn.

| Target / attempt | Exit | Wall | Peak RSS (KiB) | Swap | Audits/status |
| --- | ---: | ---: | ---: | ---: | --- |
| LinearDenominatorPrimitive v1 | 1 | 10.48s | 2,412,292 | 0 | Diagnostic |
| LinearDenominatorPrimitive v2 | 0 | 1.21s | 2,423,796 | 0 | 3 standard-only |
| LinearDenominatorOOD v1 | 1 | 2.90s | 6,800,996 | 0 | Diagnostic |
| LinearDenominatorOOD v2 | 0 | 3.07s | 6,835,712 | 0 | 4 standard-only |
| LinearDenominatorFactors v1 | 1 | 9.33s | 6,805,596 | 0 | Diagnostic |
| LinearDenominatorFactors v2 | 0 | 3.34s | 6,842,148 | 0 | 5 standard-only |
| LinearDenominatorRegression v1 | 1 | 2.92s | 6,802,748 | 0 | Diagnostic |
| LinearDenominatorRegression v2 | 0 | 3.18s | 6,837,504 | 0 | 6 standard-only |

The primitive v1 wrapper omitted the fraction-field type from its theorem
context; v2 explicitly includes it. OOD v1 needed the noncomputable
normalized-GCD instance chosen from its existing nonempty instance. Factors
v1 needed explicit types for two dependent-if proofs and symbolic exposure
of the product abbreviation before rewriting. None of these repairs raised
limits, changed the mathematical statements, or expanded a concrete field.
Failed snapshots/logs remain diagnostics, never green evidence.
Regression v1 needed three local interface repairs: applying `one_ne_zero`
to a simplified equality, explicitly proving relative primality with one,
and supplying the constant-divisor coefficient theorem through `rw`.
Its polynomial degree/resultant/OOD identities were already established in
that first attempt; v2 closes all six audits.

| Green target | Source SHA-256 | Olean SHA-256 |
| --- | --- | --- |
| LinearDenominatorPrimitive | `0725b51796024ed398bd3ef1fa8a9ee4111e70ae4de65138ee5c9b94e6c3ce9c` | `3228e18c27d16b05b06eb7ad5fada178d437a30ddaa3ea6248ab624889c985da` |
| LinearDenominatorOOD | `c9fcc51ae89588b0c394006f2ff387c5e63c38502bb8e41887b7f9b40f2c2c0d` | `9f4e9d89cd69c9887942f9948a2b907f3c1c844be4455d5571f74663160e50a4` |
| LinearDenominatorFactors | `b3b298ead4bc7d28482b614dced6ca77c768d66f4d4511862a47d1612ae4c69d` | `1fc2769537328391e9db90b4978a5a8ae4f18d825e4c767aa5add64e0971af63` |
| LinearDenominatorRegression | `afbf62a058b78d519660975592f44b90f94a3f09253f41b8f97602fe109f9ebb` | `756eaf4a94ad7af48f377f30ffa587d634c586d910950a38cbd3965f9ddcd0a7` |

All successful audits list only `propext`, `Classical.choice`, `Quot.sound`.
Attempt artifacts use the corresponding lower-case hyphenated target name
and `-nuc-vN` prefix in `experiments`, each with exact `-source.txt`, `.log`,
and `-manifest.json`. No laptop compilation or uncapped job was launched.
