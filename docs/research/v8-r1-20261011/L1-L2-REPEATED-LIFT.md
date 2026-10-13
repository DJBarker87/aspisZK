# L1 / L2 — repeated lift for the second fold: fixed statements (lead, 2026-10-13)

Rows α₁ and q22 of `R1_SOUNDNESS.md`. These statements were written after
reading the sources below; a worker who cannot write one as stated STOPS and
reports the exact mismatch (the fixed-statement rule). No row closes here;
L1/L2 supply the matched-response property for the second fold, which the
later rows (round comparisons, binding, FS) consume.

## Sources the statements are built on

- `Wide/FinalEncoder.lean` (`v8-wide-reference-20261005`): `exactFinalLinear :
  FinalCoefficients K →ₗ[K] FinalWord K` with
  `exactFinalLinear c i = (naturalCoefficientPolynomial c).eval (algebraMap (storedFirstLineX18 i))`
  (:23, :66); `exactFinalEncoder_overlap_cap` (:89): distinct messages agree
  on ≤ 255 coordinates; `exactFinalEncoder_injective` (:101).
  `FinalCoefficients K = Fin 256 → K`, `FinalWord K = Fin 262144 → K`.
- `AspisFormal/V7ExactOneFoldDomains.lean`: `line18Point n = g ^ (2048 + 8192 n)`
  (:330), `line18X n = X (line18Point n)`, `storedFirstLineX18 i = line18X (reverseFin 18 i)`
  (:348), `storedFirstLineX18_injective` (:351).
- `AspisFormal/V5FriReleasedLineGeometry.lean`: `line16Point m = g ^ (8192 + 32768 m)`
  (:33), `storedLine16Point v = line16Point (reverseFin 16 v)` (:45),
  `storedLine16X v = X (storedLine16Point v)` (:64).
- `AspisFormal/V5ComponentCConcreteFoldLinearity.lean`: `childIndex i s = 4 i + s` (:207).
- `AspisFormal/V5FriBitReverse.lean`: `reverseFin` (:79);
  `reverseBits_radix4_fibre : reverseBits (w+2) (4p+s) = reverseBits w p + 2^w · reverseBits 2 s` (:92).
- `AspisFormal/CircleNaturalBasisEval.lean`: `naturalLinePoly K k = ∏_{bit ∈ k.bitIndices} T K (2^bit)`
  (:39); `doubledFactor x 0 = x`, `doubledFactor x (b+1) = 2 (doubledFactor x b)^2 − 1` (:20);
  `doubledFactor_eq_chebyshev : doubledFactor x b = (T K (2^b)).eval x`.
- `AspisFormal/V5FriConcreteEncoderApplicability.lean`:
  `naturalCoefficientPolynomial c = monomialPolynomial (naturalCoeffMatrix K n *ᵥ c)` (:294),
  `naturalCoefficientPolynomial_eval_eq_sum` (the natural-basis expansion at a point).
- `AspisFormal/V5FriExactLineDomains.lean`: `X_sq : X (p^2) = 2 X p ^ 2 − 1` (:94).
- Mathlib `Polynomial.Chebyshev.T_mul (m n : ℤ) : T R (m*n) = (T R m).comp (T R n)`.
- `Wide/DegreeThreeMatched.lean`, `AspisFormal/V5FriDegreeThreeCorrelatedAgreement.lean`:
  `ProximateStrategy` (candidate, support), `ValidResponse enc θ lanes σ z :=
  θ < |σ.support z| ∧ ∀ x ∈ σ.support z, curveValue lanes z x = enc (σ.candidate z) x`,
  `goodChallenges`, `jointAgreementSet`, `HasMatchingDecomposition`, `BadResponse`,
  `badStrategy`; `Wide/MatchedInstances.lean:35`
  `exactFinal_bad_response_challenges_card_le lanes σ :
  (goodChallenges exactFinalEncoder 9557 lanes (badStrategy exactFinalEncoder 9557 lanes σ)).card ≤ foldChallengeCap`
  with `foldChallengeCap = 9396508281246` (`V6PublishedTheoremInterfaces.lean:41`).
- The checkpoint's abstract lemmas (`docs/research/100bit-spend-path-20261013/lean/RepeatedLift.lean`:
  `repeated_support_card`, `repeated_projection_agrees_on_support`,
  `repeated_lift_projection_descent`) may be reused as the abstract step with
  their hypotheses discharged by L1.4–L1.5; they are not a substitute for them.

Geometry behind the statements (not itself a lemma): with `r := reverseBits`,
the stored children `4v+s` of parent `v` have natural indices
`r 16 v + 65536 · r 2 s` (`reverseBits_radix4_fibre` at width 16). Hence
`line18Point` of child `s` is `p · ζ^{r 2 s}` with `p = line18Point (r 16 v)`
and `ζ = g^(2^29)` of order 4 (`g` has order `2^31`), so the four `x`-values
are `x, −x, −y, y` in stored slot order (`r 2` sends `0,1,2,3` to `0,2,1,3`),
`T 2` of them are `z, z, −z, −z` with `z = 2x²−1 = −(2y²−1)`, and the fourth
power of every child point is `g^(8192 + 32768 · r 16 v) = line16Point (r 16 v)`,
the parent's `2^16` node. Every basis element `naturalLinePoly K k` with
`k ≡ 1, 2, 3 (mod 4)` therefore sums to zero over a quartet
(`Σ x_s = 0`, `Σ T2(x_s) = 0`, `Σ x_s T2(x_s) = 0`), and every element with
`4 ∣ k` is a function of the parent node.

## L1 — module `R1/RepeatedLift.lean` (new tree `docs/research/v8-r1-20261011/lean/R1/`;
imports `Wide.FinalEncoder`, `Wide.MatchedInstances`, the AspisFormal line-geometry modules)

Definitions (exactly these):

```
abbrev SecondCoefficients (K) := Fin 64 → K
abbrev SecondWord (K) := Fin 65536 → K
def liftCoefficients : SecondCoefficients K →ₗ[K] FinalCoefficients K      -- (lift m) k = if 4 ∣ k then m (k/4) else 0
def projectCoefficients : FinalCoefficients K →ₗ[K] FinalCoefficients K    -- keep slots 4 ∣ k, zero elsewhere
def secondLinear : SecondCoefficients K →ₗ[K] SecondWord K
  -- secondLinear m v = (naturalCoefficientPolynomial m).eval (algebraMap (ZMod P) K (storedLine16X v))
def repeatWord : SecondWord K → FinalWord K                                 -- repeatWord g (childIndex v s) = g v
def quartetAverage : FinalWord K → SecondWord K                             -- v ↦ (∑ s : Fin 4, w (childIndex v s)) / 4
```

Lemmas (statements fixed; routes indicative):

```
L1.1 naturalLinePoly_four_mul (d : ℕ) :
       naturalLinePoly K (4 * d) = (naturalLinePoly K d).comp (T K 4)
     -- bitIndices (4d) = (bitIndices d).map (· + 2); T K (2^(b+2)) = (T K (2^b)).comp (T K 4) by T_mul.
L1.2 naturalCoefficientPolynomial_lift (m : SecondCoefficients K) :
       naturalCoefficientPolynomial (liftCoefficients m) = (naturalCoefficientPolynomial m).comp (T K 4)
     -- natural-basis expansion (prove the polynomial-level form of naturalCoefficientPolynomial_eval_eq_sum
     --   if only the pointwise one exists) + L1.1; comp distributes over the sum.
L1.3 line18Point_child_pow_four (v : Fin 65536) (s : Fin 4) :
       line18Point (reverseFin 18 (childIndex v s)) ^ 4 = line16Point (reverseFin 16 v)
     -- reverseBits_radix4_fibre at width 16; exponent arithmetic; g ^ (2^31) = 1.
     storedFirstLineX18_child_T4 (v : Fin 65536) (s : Fin 4) :
       doubledFactor (algebraMap (ZMod P) K (storedFirstLineX18 (childIndex v s))) 2
         = algebraMap (ZMod P) K (storedLine16X v)
     -- X_sq twice on L1.3 (X (p^4) = 2(2 X p^2 − 1)^2 − 1), then map through algebraMap.
L1.4 exactFinalLinear_lift (m : SecondCoefficients K) (v : Fin 65536) (s : Fin 4) :
       exactFinalLinear (liftCoefficients m) (childIndex v s) = secondLinear m v
     -- eval_comp with L1.2, doubledFactor_eq_chebyshev (b = 2), L1.3.  This is E256(L m)(4v+s) = E64(m)(v).
L1.5 exactFinalLinear_project (a : FinalCoefficients K) (v : Fin 65536) (s : Fin 4) :
       exactFinalLinear (projectCoefficients a) (childIndex v s) = quartetAverage (exactFinalLinear a) v
     -- split k = 4d + t; for t ∈ {1,2,3}: naturalLinePoly (4d+t) = naturalLinePoly (4d) * naturalLinePoly t
     --   (disjoint bitIndices), the 4d-part is constant on the quartet (L1.1 + L1.3), and
     --   Σ_s x_s = Σ_s T2(x_s) = Σ_s x_s·T2(x_s) = 0 over the quartet from the ζ-rotation structure of the
     --   four child points (lemmas on g^(2^29), g^(2^30) in the circle group; locate or prove them).
L1.6 exactFinalLinear_descent (a : FinalCoefficients K) (S : Finset (Fin 65536))
       (hconst : ∀ v ∈ S, ∀ s t : Fin 4, exactFinalLinear a (childIndex v s) = exactFinalLinear a (childIndex v t))
       (hS : 64 ≤ S.card) :
       a = projectCoefficients a
     -- L1.5 gives agreement of E a and E (P a) on the 4|S| ≥ 256 > 255 quartet coordinates;
     --   exactFinalEncoder_overlap_cap forces equality (childIndex injective ⇒ card of the quartet set = 4|S|).
     exactFinalLinear_descent_lift … : ∃ m, a = liftCoefficients m         -- m d := a (4d); P a = L m by definition.
```

`#print axioms` for L1.4, L1.5, L1.6: exactly `[propext, Classical.choice, Quot.sound]`.

## L2 — module `R1/SecondFoldMatched.lean` (imports `R1.RepeatedLift`)

Definitions:

```
def liftLanes (g : Fin 4 → SecondWord K) : Fin 4 → FinalWord K := fun i => repeatWord (g i)
def liftStrategy (σ : ProximateStrategy K (Fin 65536) (SecondCoefficients K)) :
    ProximateStrategy K (Fin 262144) (FinalCoefficients K) where
  candidate z := liftCoefficients (σ.candidate z)
  support z := (σ.support z).biUnion (fun v => Finset.univ.image (childIndex v))
```

Lemmas:

```
L2.1 liftStrategy_support_card (σ) (z) : ((liftStrategy σ).support z).card = 4 * (σ.support z).card
L2.2 validResponse_lift (g) (σ) (z) :
       ValidResponse secondLinear 2389 g σ z → ValidResponse exactFinalEncoder 9557 (liftLanes g) (liftStrategy σ) z
     -- 2389 < |S| ⇒ 9557 < 4|S| (4·2390 = 9560); curveValue (liftLanes g) z (childIndex v s) = curveValue g z v
     --   (batchedDiscrepancy is pointwise); E256 (L cand)(childIndex v s) = E64 cand v by L1.4.
L2.3 matchingDecomposition_descend (g) (σ) (z) :
       HasMatchingDecomposition exactFinalEncoder (liftLanes g) (liftStrategy σ) z →
       HasMatchingDecomposition secondLinear g σ z
     -- components a_i agree with repeatWord (g i) on all children of S ⇒ constant on each quartet ⇒ (L1.6)
     --   a_i = L b_i; L (σ.candidate z) = Σ z^i L b_i ⇒ σ.candidate z = Σ z^i b_i (liftCoefficients injective);
     --   E64 b_i agrees with g i on S by L1.4.  (|S| ≥ 2390 ≥ 64 for the descent.)
L2.4 secondFold_bad_response_challenges_card_le (g : Fin 4 → SecondWord K)
       (σ : ProximateStrategy K (Fin 65536) (SecondCoefficients K)) :
       (goodChallenges secondLinear 2389 g (badStrategy secondLinear 2389 g σ)).card ≤ foldChallengeCap
     -- goodChallenges (badStrategy … σ) ⊆ goodChallenges exactFinalEncoder 9557 (liftLanes g) (badStrategy … (liftStrategy σ))
     --   by L2.2 and the contrapositive of L2.3; then exactFinal_bad_response_challenges_card_le.
```

`#print axioms` for L2.4: exactly `[propext, Classical.choice, Quot.sound]`.

## What L1/L2 deliver and do not deliver

Delivered: the second fold's matched-response property with the existing cap
`foldChallengeCap` (≈ 2^43.1), on the `2^16` stored line domain with the
`64`-coefficient natural-basis code, with no new decoder instance, no
list-size or Johnson premise, and no new large certificate. Not delivered: the
runtime fold identities (`LineFold.lean` has the field recovery; the
domain-commutation statement that the verifier's channel recovery equals
`secondLinear` of the folded coefficients is row Src/L7), the round-polynomial
comparisons (L3), the support argument `|M| ≥ 9558 ⇒ ≥ 2390 parents` and its
use in the q22 row (a small counting lemma to be stated with L3), and any FS
instantiation.

## Setup note for the host

The new `R1/` tree must be added to the pinned workspace's lakefile with
`Wide`, `R0` and `AspisFormal` as dependencies before the first attempt; one
Lean job at a time, attempts continue from the current counter; caps and
evidence format as T2b-1. Statements above are fixed; `Nat.bitIndices` lemma
names, the circle-group order lemma and the exact form of the natural-basis
expansion are the places a stop is most likely.
