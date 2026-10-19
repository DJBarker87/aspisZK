import WideExactGRSInstantiationV5
import GSArrayMatchingCount
import CompPoly.Univariate.ToPoly.Impl
import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness

open CompPoly
open CompPoly.GuruswamiSudan
open AspisPool.AlgorithmicCircleDecoderV7

namespace AspisWide.GSWideExactAgreementInputs

open AspisWide.WideExactGRSInstantiation
open AspisWideTower

def initialNormalizedPoints (received : InitialWord WideExact) :
    Array (WideExact × WideExact) :=
  Array.ofFn (initialWideNormalizedPair received)

def finalNormalizedPoints (received : FinalWord WideExact) :
    Array (WideExact × WideExact) :=
  Array.ofFn (finalWideNormalizedPair received)

theorem initial_matches_eq_agreement
    (received : InitialWord WideExact) (message : InitialMessage WideExact)
    (p : CPolynomial WideExact)
    (hp : p.toPoly = initialConversion.messagePolynomial message) :
    matchingPointCount (initialNormalizedPoints received) p =
      agreementCount received
        (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) message) := by
  rw [initialNormalizedPoints, AspisWide.GSArrayMatchingCount.matching_count_ofFn]
  unfold agreementCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change CPolynomial.eval (initialConversion.points i) p =
      (initialConversion.multipliers i)⁻¹ * received i ↔
    received i = AspisWide.InitialEncoder.exactInitialEncoder
      (K := WideExact) message i
  rw [CPolynomial.eval_toPoly, hp]
  constructor
  · intro h
    exact (initialWide_multiplier_normalization received message i).mp h |>.symm
  · intro h
    exact (initialWide_multiplier_normalization received message i).mpr h.symm

theorem final_matches_eq_agreement
    (received : FinalWord WideExact) (message : FinalMessage WideExact)
    (p : CPolynomial WideExact)
    (hp : p.toPoly = finalConversion.messagePolynomial message) :
    matchingPointCount (finalNormalizedPoints received) p =
      agreementCount received
        (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) message) := by
  rw [finalNormalizedPoints, AspisWide.GSArrayMatchingCount.matching_count_ofFn]
  unfold agreementCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change CPolynomial.eval (finalConversion.points i) p =
      (finalConversion.multipliers i)⁻¹ * received i ↔
    received i = AspisWide.FinalEncoder.exactFinalEncoder
      (K := WideExact) message i
  rw [CPolynomial.eval_toPoly, hp]
  constructor
  · intro h
    exact (finalWide_multiplier_normalization received message i).mp h |>.symm
  · intro h
    exact (finalWide_multiplier_normalization received message i).mpr h.symm

theorem initial_points_distinct (received : InitialWord WideExact) :
    DistinctXCoordinates (initialNormalizedPoints received) := by
  unfold DistinctXCoordinates initialNormalizedPoints
  simpa [initialWideNormalizedPair] using initialWide_points_nodup

theorem final_points_distinct (received : FinalWord WideExact) :
    DistinctXCoordinates (finalNormalizedPoints received) := by
  unfold DistinctXCoordinates finalNormalizedPoints
  simpa [finalWideNormalizedPair] using finalWide_points_nodup

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
  unfold closeAtLeast agreementCount at hclose
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
  unfold closeAtLeast agreementCount at hclose
  rw [← hcount] at hclose
  omega

#print axioms initial_matches_eq_agreement
#print axioms final_matches_eq_agreement
#print axioms initial_points_distinct
#print axioms final_points_distinct
#print axioms initial_close_gives_strict_match_bound
#print axioms final_close_gives_strict_match_bound

end AspisWide.GSWideExactAgreementInputs
