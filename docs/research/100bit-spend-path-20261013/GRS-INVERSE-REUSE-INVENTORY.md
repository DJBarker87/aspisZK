# GRS image and fractional-lift inverse inventory

This is a read-only reuse inventory, not an algorithmic decoder implementation. It combines the natural-basis inverse inspection at base `209663b6e8bd07a5067eb5dce3cf11e02e438a0d`, the circle/image inspection at base `e21211727fc6ad53a2ef014d3fa3dda72037cef0`, and the fractional-lift declaration inspection at base `209663b6e8bd07a5067eb5dce3cf11e02e438a0d`. No Lean target was run for these inspections.

## Released message image

The released initial message is `Fin 1024 → K` ([`AlgorithmicCircleDecoderV7.lean`](../../../AspisFormal/AspisFormal/Pool/AlgorithmicCircleDecoderV7.lean:23), SHA-256 `2faaf875cf3237c9409a19bf2bbb2dd3d302288ed24b059aabb90fac5ddd6471`). The encoder uses two degree-`<512` coefficient polynomials obtained from even and odd message coordinates ([`InitialEncoder.lean`](../v8-wide-reference-20261005/lean/Wide/InitialEncoder.lean:29), SHA-256 `518bf5e70161f11981f3c0b97f95f88efe08e0d3065d54848079e507138552b2`; [`V5FriInitialCircleEncoderIdentity.lean`](../../../AspisFormal/AspisFormal/V5FriInitialCircleEncoderIdentity.lean:47)). The existing `evenOddCoefficients_injective` and `initialPolynomialPair_injective` are injectivity statements; they do not themselves provide an inverse. Separately, `AspisR0.PolynomialPair.pair_complete` gives existential completeness for any pair of polynomials of degree at most 511, as detailed below.

The numerator construction is `circleNumerator p0 p1 = mobiusLift 512 p0 + (C 2 * X) * mobiusLift 511 p1` ([`V5FriCircleEncoderDistance.lean`](../../../AspisFormal/AspisFormal/V5FriCircleEncoderDistance.lean:170), SHA-256 at that base `909dc85e736ceb7997a6f7d7d31c600531712c34015a3ab6d33beb2e66b46525`). Existing parity coefficient formulas split its even coefficients into the `fractionalLift 512 p0` coefficients and odd coefficients into twice the `fractionalLift 511 p1` coefficients. This describes the image of an already supplied pair; it does not test or invert an arbitrary ambient polynomial.

## Existing fractional-lift facts

In [`V5FriCircleEncoderDistance.lean`](../../../AspisFormal/AspisFormal/V5FriCircleEncoderDistance.lean:106), `fractionalLift d p` is

```text
Σ i ∈ range (d + 1), C (p.coeff i) * (1-X)^i * (1+X)^(d-i)
```

and `mobiusLift d p` is `Polynomial.expand K 2 (fractionalLift d p)`. The module proves degree bounds, evaluation and denominator-clearing identities, and coefficient parity facts. `evenOddExpanded_injective` separates a polynomial from `X` times a polynomial after `expand K 2`, assuming `[NeZero (2 : K)]`.

The scalar theorem `fractional_involution` proves that `x ↦ (1-x)/(1+x)` is involutive when `x ≠ -1` (and `2` is nonzero). It concerns field elements, not composition of the polynomial lift. The lift theorem `fractionalLift_eq_of_eq` proves injectivity on inputs with degree at most `d`, under finite-field/decidable-equality assumptions and `d+1 < Fintype.card K`. No polynomial identity was found asserting `fractionalLift d (fractionalLift d p) = 2^d • p`; no scaled inverse theorem or image characterization by an even-part degree condition was found in the searched project Lean sources or saved Mathlib API excerpts.

The existing `circleNumerator_pair_eq` theorem proves uniqueness of two bounded-degree input polynomials from equality of their circle numerators. Together with the released message split, this gives uniqueness for released messages. It does not establish that every polynomial in the ambient degree-`≤1024` space has a released-message preimage.

## Natural-basis inverse for bounded polynomial pairs

The maintained natural line basis has degree-ordered basis polynomials and an invertible triangular coefficient matrix ([`CircleNaturalBasis.lean`](../../../AspisFormal/AspisFormal/CircleNaturalBasis.lean:37), SHA-256 `c9705066fdda76adbccae72d1e5ddcf3b17e4d0d9de5330ab36f228ea5819d78`). `naturalCoeffMatrix_det_ne_zero`, `monomialToNatural`, and `naturalCoeff_mul_monomialToNatural` establish the matrix inverse interface (`:53-76`). In [`V5FriConcreteEncoderApplicability.lean`](../../../AspisFormal/AspisFormal/V5FriConcreteEncoderApplicability.lean:276) (SHA-256 `91d8d7a2d8e1ea832459a439482aa858e970cba1608ab7652bdfce3eede632d3`), `naturalToMonomialCoefficients_bijective` proves the coefficient conversion bijective, and `naturalCoefficientPolynomial_complete` (`:308-317`) states that for `0<n` and `p.natDegree ≤ n-1`, some natural-basis coefficient vector represents `p`. At `n=512`, this supplies existential representation for every polynomial of degree at most 511.

The paired API [`PolynomialPair.lean`](../v8-wide-reference-20261005/lean/R0/PolynomialPair.lean:18), SHA-256 `0c1772aadc2902ac392c9d086161deaf131565c611619ae538c4bdcf5e51099f`, has `AspisR0.PolynomialPair.pair_complete`: for `p0,p1` each of degree at most 511, it returns an `InitialMessage K` whose `initialP0` and `initialP1` are exactly those polynomials. The proof applies the 512-wide natural-basis completeness theorem to each polynomial and interleaves the resulting coefficient vectors. The paired `lift` at lines 45-49 uses `Classical.choose` on this existence theorem; it is explicitly noncomputable.

This is an exact existential inverse for the bounded pair-to-message representation. It does not provide an algorithmic decoder, prove that arbitrary ambient degree-`≤1024` polynomials are circle numerators, or establish that data produced by another decoder meets the component degree bounds. The supporting `CircleNaturalBasisEval.lean` source has SHA-256 `127ea451736936d8fb077e065efb7d49719af776b3782dc82af4b97076be3a9a`.

## Existing GRS and GS declarations

`exactInitialGRSConversion` is the checked forward conversion ([`GRSConversion.lean`](../v8-wide-reference-20261005/lean/Wide/GRSConversion.lean:183), SHA-256 `df621ca75572edf4e5291d1c64b802a158303e404a5b7f0ec3e63630acd39255`). Its structure records the message-coordinate equivalence, evaluation points and multipliers, polynomial map, injectivity, degree bound, and forward coordinate identity. It has no inverse or image-membership field.

The existing exact GS specification is a finite mathematical filter over all `InitialMessage` values. `exactInitialInterpolationCoefficients` uses `Classical.choose` from an existence theorem, and `exactInitialRootCandidates` filters `Finset.univ : Finset (InitialMessage E)` by the interpolation equation ([`MultiplicityThreeGS.lean`](../v8-wide-reference-20261005/lean/Wide/MultiplicityThreeGS.lean:1006), SHA-256 `73252b85be6db2b7a0180d9f942e1872a75a57e6257dfb36124139bb27f277b5`). Subsequent definitions add the direct agreement threshold and prove exact candidate membership/completeness and the list-size bound. These are noncomputable finite specifications, not an executable inverse of an arbitrary ambient polynomial coefficient vector.

Nearby results such as `exactInitialEncoder_injective`, the linearity of constructed message combinations, and curve/challenge extraction theorems establish injectivity or existence under their stated premises. They do not characterize arbitrary ambient degree-`≤1024` polynomials as circle numerators. The natural-basis pair theorem above does establish existence for any pair satisfying the two degree-`≤511` bounds. The earlier route note [`GS-DECODER-REUSE-PATH.md`](./GS-DECODER-REUSE-PATH.md) describes the remaining ambient image boundary; it was created after the circle inspection base and is linked for context, not claimed as a file present at that historical base.

## Search scope and hash correction

The fractional-lift inspection searched project Lean sources and the saved API excerpt [`API_EXCERPTS.md`](../v8-full-view-zk-20260912/evidence/r374-single-coordinate-degree/api-cache-inventory/API_EXCERPTS.md:1). General polynomial composition/evaluation facts (`Polynomial.comp_assoc` and `Polynomial.eval_comp`) were present in the saved Mathlib source snapshot; no specialized linear-fractional polynomial action theorem appeared there. The local worktree had no full `.lake/packages/mathlib` source checkout, so this does not claim an exhaustive search of every Mathlib release or remote cache.

The circle inspection's source hashes were checked against base `e21211727fc6ad53a2ef014d3fa3dda72037cef0`. Its temporary report contained a transcription error for `InitialCurve.lean`: the correct SHA-256 at that base is `dce9f637cd7b50d4962e7e09432dd43ed8966c2b2750b7720a2320e745d4415e`. The declaration is not relied on for the inverse boundary described above. Other independently checked circle-inspection hashes include the message type, `InitialEncoder`, `V5FriCircleEncoderDistance`, `GRSConversion`, `MultiplicityThreeGS`, `InitialRoot`, `InitialSelection`, and `InitialCurveBranch` listed above or in the temporary report. The current-base hash of `V5FriCircleEncoderDistance.lean` was rechecked as `909dc85e736ceb7997a6f7d7d31c600531712c34015a3ab6d33beb2e66b46525`.
