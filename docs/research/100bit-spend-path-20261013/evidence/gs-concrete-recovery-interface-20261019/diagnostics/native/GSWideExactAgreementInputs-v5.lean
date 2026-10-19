import WideExactGRSInstantiationV5
import GSArrayMatchingCount
import GSNormalizedPointAgreement
import CompPoly.Univariate.ToPoly.Impl
import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness

open CompPoly
open CompPoly.GuruswamiSudan
open AspisPool.AlgorithmicCircleDecoderV7

namespace AspisWide.GSWideExactAgreementInputs

open AspisWide.WideExactGRSInstantiation
open AspisWideTower

noncomputable def initialNormalizedPoints (received : InitialWord WideExact) :
    Array (WideExact × WideExact) :=
  Array.ofFn (initialWideNormalizedPair received)

noncomputable def finalNormalizedPoints (received : FinalWord WideExact) :
    Array (WideExact × WideExact) :=
  Array.ofFn (finalWideNormalizedPair received)

theorem initial_matches_eq_agreement
    (received : InitialWord WideExact) (message : InitialMessage WideExact)
    (p : CPolynomial WideExact)
    (hp : p.toPoly = initialConversion.messagePolynomial message) :
    matchingPointCount (initialNormalizedPoints received) p =
      agreementCount received
        (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) message) := by
  let polyEval : Fin 1048576 → WideExact := fun i =>
    (initialConversion.messagePolynomial message).eval (initialConversion.points i)
  have heval : ∀ i, CPolynomial.eval (initialConversion.points i) p = polyEval i := by
    intro i
    simp [polyEval, CPolynomial.eval_toPoly, hp]
  have hmatch : ∀ i,
      polyEval i = (initialConversion.multipliers i)⁻¹ * received i ↔
        AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) message i = received i := by
    intro i
    exact initialWide_multiplier_normalization received message i
  simpa [initialNormalizedPoints, AspisWide.GSNormalizedPointAgreement.normalizedPoints,
    agreementCount] using
    (AspisWide.GSNormalizedPointAgreement.matching_count_eq_agreement
      initialConversion.points initialConversion.multipliers received
      (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) message)
      p polyEval heval hmatch)

theorem final_matches_eq_agreement
    (received : FinalWord WideExact) (message : FinalMessage WideExact)
    (p : CPolynomial WideExact)
    (hp : p.toPoly = finalConversion.messagePolynomial message) :
    matchingPointCount (finalNormalizedPoints received) p =
      agreementCount received
        (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) message) := by
  let polyEval : Fin 262144 → WideExact := fun i =>
    (finalConversion.messagePolynomial message).eval (finalConversion.points i)
  have heval : ∀ i, CPolynomial.eval (finalConversion.points i) p = polyEval i := by
    intro i
    simp [polyEval, CPolynomial.eval_toPoly, hp]
  have hmatch : ∀ i,
      polyEval i = (finalConversion.multipliers i)⁻¹ * received i ↔
        AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) message i = received i := by
    intro i
    exact finalWide_multiplier_normalization received message i
  simpa [finalNormalizedPoints, AspisWide.GSNormalizedPointAgreement.normalizedPoints,
    agreementCount] using
    (AspisWide.GSNormalizedPointAgreement.matching_count_eq_agreement
      finalConversion.points finalConversion.multipliers received
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) message)
      p polyEval heval hmatch)

theorem initial_points_distinct (received : InitialWord WideExact) :
    DistinctXCoordinates (initialNormalizedPoints received) := by
  simpa [initialNormalizedPoints, AspisWide.GSNormalizedPointAgreement.normalizedPoints,
    DistinctXCoordinates] using
    (AspisWide.GSNormalizedPointAgreement.normalized_points_distinct
      initialConversion.points initialConversion.multipliers received
      initialConversion.points_injective)

theorem final_points_distinct (received : FinalWord WideExact) :
    DistinctXCoordinates (finalNormalizedPoints received) := by
  simpa [finalNormalizedPoints, AspisWide.GSNormalizedPointAgreement.normalizedPoints,
    DistinctXCoordinates] using
    (AspisWide.GSNormalizedPointAgreement.normalized_points_distinct
      finalConversion.points finalConversion.multipliers received
      finalConversion.points_injective)

theorem initial_close_gives_strict_match_bound
    (received : InitialWord WideExact) (message : InitialMessage WideExact)
    (p : CPolynomial WideExact)
    (hp : p.toPoly = initialConversion.messagePolynomial message)
    (hclose : closeAtLeast 38230
      (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact))
      received message) :
    114689 < 3 * matchingPointCount (initialNormalizedPoints received)
      p := by
  have hcount := initial_matches_eq_agreement received message p hp
  change 38230 ≤ agreementCount received
    (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) message) at hclose
  rw [← hcount] at hclose
  omega

theorem final_close_gives_strict_match_bound
    (received : FinalWord WideExact) (message : FinalMessage WideExact)
    (p : CPolynomial WideExact)
    (hp : p.toPoly = finalConversion.messagePolynomial message)
    (hclose : closeAtLeast 9558
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact))
      received message) :
    28673 < 3 * matchingPointCount (finalNormalizedPoints received)
      p := by
  have hcount := final_matches_eq_agreement received message p hp
  change 9558 ≤ agreementCount received
    (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) message) at hclose
  rw [← hcount] at hclose
  omega

#print axioms initial_matches_eq_agreement
#print axioms final_matches_eq_agreement
#print axioms initial_points_distinct
#print axioms final_points_distinct
#print axioms initial_close_gives_strict_match_bound
#print axioms final_close_gives_strict_match_bound

end AspisWide.GSWideExactAgreementInputs
