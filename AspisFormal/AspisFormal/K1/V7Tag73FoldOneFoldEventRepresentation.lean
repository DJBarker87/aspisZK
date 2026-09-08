import AspisFormal.K1.V7Tag73FoldOneFoldProductMembership

/-! # Named representation boundary for the nested fold/alpha event -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73FoldOneFoldEventRepresentation

open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CausalFoldRawOneFoldProduct
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldProductProbability
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73FoldOneFoldProductMembership
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A coordinate's membership in the nested fold event, parameterized only by
the successful raw-alpha event. -/
def dependentFoldRawEventMember
    {Residual : Type}
    (coordinate : Residual × (Digest256 × FourGammaBlocks))
    (rawEvent : Set SuccessfulTag73RawStream) : Prop :=
  coordinate ∈
    dependentSuccessfulSubtypeEvent foldAlphaTotalSucceeds
      (fun _residual => successfulFoldAlphaTotalEquiv ⁻¹'
        foldSuccessfulRawOneFoldEvent (fun _fold => rawEvent))

/-- The public successful-raw event is exactly the factorized family of exact
one-fold target slices. -/
theorem successfulRawOneFoldEvent_eq_factorizedTarget
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext) :
    successfulRawOneFoldEvent context =
      successfulOrdinaryExactFactorization ⁻¹'
        dependentProductEvent
          (fun skeleton => {value |
            value ∈ exactRawOneFoldTarget context skeleton}) := by
  rw [successfulRawOneFoldEvent, rawOneFoldProductEvent]

/-- The existing named factorized predicate is the raw-event predicate at the
factorized target set. -/
theorem dependentFoldFactorizedOneFoldEventMember_eq
    {Residual : Type}
    (coordinate : Residual × (Digest256 × FourGammaBlocks))
    (target : Tag73OrdinarySamplerSkeleton → Set QM31Exact) :
    dependentFoldFactorizedOneFoldEventMember coordinate target =
      dependentFoldRawEventMember coordinate
        (successfulOrdinaryExactFactorization ⁻¹'
          dependentProductEvent target) := by
  rfl

/-- Transport factorized target membership to the public successful-raw event
without unfolding the surrounding nested event. -/
theorem dependentFoldFactorized_to_successfulRaw
    {Residual : Type}
    (coordinate : Residual × (Digest256 × FourGammaBlocks))
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (member : dependentFoldFactorizedOneFoldEventMember coordinate
      (fun skeleton => {value |
        value ∈ exactRawOneFoldTarget context skeleton})) :
    dependentFoldRawEventMember coordinate
      (successfulRawOneFoldEvent context) := by
  have factorized := dependentFoldFactorizedOneFoldEventMember_eq coordinate
    (fun skeleton => {value |
      value ∈ exactRawOneFoldTarget context skeleton})
  have memberRaw : dependentFoldRawEventMember coordinate
      (successfulOrdinaryExactFactorization ⁻¹'
        dependentProductEvent
          (fun skeleton => {value |
            value ∈ exactRawOneFoldTarget context skeleton})) :=
    Eq.mp factorized member
  have rawEventExact := successfulRawOneFoldEvent_eq_factorizedTarget context
  exact Eq.mpr
    (congrArg (dependentFoldRawEventMember coordinate) rawEventExact) memberRaw

#print axioms successfulRawOneFoldEvent_eq_factorizedTarget
#print axioms dependentFoldFactorizedOneFoldEventMember_eq
#print axioms dependentFoldFactorized_to_successfulRaw

end


end AspisK1.V7Tag73FoldOneFoldEventRepresentation
