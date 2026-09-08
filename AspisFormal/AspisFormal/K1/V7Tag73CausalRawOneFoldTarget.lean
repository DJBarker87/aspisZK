import AspisFormal.K1.V7Tag73ExactInternalCurveProbability

/-!
# Exact causal one-fold bad target

This file isolates the algebraic target and its degree-three cardinality bound
from the later successful-sampler probability argument.  Keeping the two
kernel checks separate materially lowers peak elaboration memory.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CausalRawOneFoldTarget

open MeasureTheory
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7ExactCorrelatedAgreementTerminal
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

noncomputable def exactRawOneFoldTarget
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (skeleton : Tag73OrdinarySamplerSkeleton) : Finset QM31Exact :=
  let current := context skeleton
  causalOneFoldFailureTarget current.schedule current.encoders
    (exactOneFoldAlgebraBinding current.schedule current.encoders
      current.initialEncoderExact current.finalEncoderExact
      current.inverseTablesExact)
    current.base current.strategy

theorem exact_raw_onefold_target_card_le
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (skeleton : Tag73OrdinarySamplerSkeleton) :
    (exactRawOneFoldTarget context skeleton).card ≤ foldChallengeCap := by
  let current := context skeleton
  exact causalOneFoldFailureTarget_card_le current.schedule current.encoders
    (exactOneFoldAlgebraBinding current.schedule current.encoders
      current.initialEncoderExact current.finalEncoderExact
      current.inverseTablesExact)
    current.base current.strategy
    exactV7FinalPublishedOneFoldCurveDecodability

theorem exact_raw_onefold_target_probability_le
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (skeleton : Tag73OrdinarySamplerSkeleton) :
    (PMF.uniformOfFintype QM31Exact).toOuterMeasure
        {value | value ∈ exactRawOneFoldTarget context skeleton} ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  rw [uniform_ordinary_target_probability_exact]
  gcongr
  exact_mod_cast exact_raw_onefold_target_card_le context skeleton

end

#print axioms exact_raw_onefold_target_card_le
#print axioms exact_raw_onefold_target_probability_le

end AspisK1.V7Tag73CausalRawOneFoldTarget
