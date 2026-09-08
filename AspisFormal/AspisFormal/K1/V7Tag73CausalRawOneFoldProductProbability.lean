import AspisFormal.K1.V7Tag73CausalRawOneFoldTarget
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge

/-!
# Product-law probability for the exact causal one-fold bad target

This module checks the finite product/slice argument independently of the
later raw-stream equivalence transport.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CausalRawOneFoldProductProbability

open MeasureTheory
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

def dependentProductEvent {Residual Total : Type}
    (target : Residual → Set Total) : Set (Residual × Total) :=
  {pair | pair.2 ∈ target pair.1}

@[simp] theorem productEventFstSlice_dependentProductEvent
    {Residual Total : Type} (target : Residual → Set Total)
    (residual : Residual) :
    productEventFstSlice (dependentProductEvent target) residual =
      target residual := by
  rfl

def rawOneFoldProductEvent
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext) :
    Set (Tag73OrdinarySamplerSkeleton × QM31Exact) :=
  dependentProductEvent
    (fun skeleton => {value | value ∈ exactRawOneFoldTarget context skeleton})

theorem uniform_raw_onefold_product_probability_le
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext) :
    (PMF.uniformOfFintype
      (Tag73OrdinarySamplerSkeleton × QM31Exact)).toOuterMeasure
        (rawOneFoldProductEvent context) ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply uniform_product_event_probability_le_of_every_slice_le
  intro skeleton
  rw [rawOneFoldProductEvent,
    productEventFstSlice_dependentProductEvent]
  exact exact_raw_onefold_target_probability_le context skeleton

end


#print axioms uniform_raw_onefold_product_probability_le

end AspisK1.V7Tag73CausalRawOneFoldProductProbability
