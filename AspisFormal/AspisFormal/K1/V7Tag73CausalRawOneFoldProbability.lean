import AspisFormal.K1.V7Tag73CausalRawOneFoldProductProbability
import AspisFormal.K1.V7Tag73VariablePrefixGammaFactorization

/-!
# Causal one-fold probability from four raw alpha blocks

This is the small output-only probability kernel used by the fold-armed
source adapter.  Duplex advance answers remain in the causal residual; the
four routed output blocks alone are the exact ordinary raw sampler.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CausalRawOneFoldProbability

open MeasureTheory
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldProductProbability
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7ExactCorrelatedAgreementTerminal
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

noncomputable def successfulRawOneFoldUniformLaw :
    PMF SuccessfulTag73RawStream :=
  PMF.uniformOfFintype SuccessfulTag73RawStream

def successfulRawOneFoldEvent
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext) :
    Set SuccessfulTag73RawStream :=
  successfulOrdinaryExactFactorization ⁻¹'
    rawOneFoldProductEvent context

theorem uniform_successful_raw_onefold_probability_le
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext) :
    (PMF.uniformOfFintype SuccessfulTag73RawStream).toOuterMeasure
        (successfulRawOneFoldEvent context) ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  calc
    (PMF.uniformOfFintype SuccessfulTag73RawStream).toOuterMeasure
        (successfulRawOneFoldEvent context) =
      ((PMF.uniformOfFintype SuccessfulTag73RawStream).map
        successfulOrdinaryExactFactorization).toOuterMeasure
          (rawOneFoldProductEvent context) := by
            rw [PMF.toOuterMeasure_map_apply]
            rfl
    _ = (PMF.uniformOfFintype
          (Tag73OrdinarySamplerSkeleton × QM31Exact)).toOuterMeasure
            (rawOneFoldProductEvent context) := by
      rw [AspisV5RankOneOpeningHiding.uniform_map_equiv
        successfulOrdinaryExactFactorization]
    _ ≤ _ := uniform_raw_onefold_product_probability_le context

theorem successful_raw_onefold_uniform_law_probability_le
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext) :
    successfulRawOneFoldUniformLaw.toOuterMeasure
        (successfulRawOneFoldEvent context) ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  unfold successfulRawOneFoldUniformLaw
  exact uniform_successful_raw_onefold_probability_le context

theorem uniform_conditional_successful_raw_onefold_probability_le
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (accepted : Prop) [Decidable accepted] :
    (PMF.uniformOfFintype SuccessfulTag73RawStream).toOuterMeasure
        (if accepted then successfulRawOneFoldEvent context else ∅) ≤
      if accepted then
        (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)
      else 0 := by
  by_cases h : accepted
  · rw [if_pos h, if_pos h]
    exact uniform_successful_raw_onefold_probability_le context
  · simp [h]

theorem uniform_successful_raw_onefold_probability_le_family
    {Index : Type}
    (context : Index → Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (index : Index) :
    (PMF.uniformOfFintype SuccessfulTag73RawStream).toOuterMeasure
        (successfulRawOneFoldEvent (context index)) ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) :=
  uniform_successful_raw_onefold_probability_le (context index)

end


#print axioms uniform_successful_raw_onefold_probability_le
#print axioms successful_raw_onefold_uniform_law_probability_le
#print axioms uniform_conditional_successful_raw_onefold_probability_le
#print axioms uniform_successful_raw_onefold_probability_le_family

end AspisK1.V7Tag73CausalRawOneFoldProbability
