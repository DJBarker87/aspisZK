import AspisFormal.K1.V7Tag73FoldOneFoldEventRepresentation

/-! # Component-wise membership in the public fold/alpha event -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73FoldOneFoldComponentMembership

open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CausalFoldRawOneFoldProduct
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldProductProbability
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73FoldOneFoldEventRepresentation
open AspisK1.V7Tag73FoldOneFoldProductMembership
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The three component facts package into exactly the public nested event. -/
theorem mem_dependent_fold_successfulRawOneFoldEvent_of_components
    {Residual : Type}
    (coordinate : Residual × (Digest256 × FourGammaBlocks))
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (succeeds : foldAlphaTotalSucceeds coordinate.2)
    (foldAccepted : FoldWork31Accepted coordinate.2.1)
    (targetMember : successfulOrdinaryExactValue
          (⟨fourGammaBlocksRawEquiv coordinate.2.2, succeeds⟩ :
            SuccessfulTag73RawStream) ∈
        exactRawOneFoldTarget context
          (successfulOrdinaryExactFactorization
            (⟨fourGammaBlocksRawEquiv coordinate.2.2, succeeds⟩ :
              SuccessfulTag73RawStream)).1) :
    dependentFoldRawEventMember coordinate
      (successfulRawOneFoldEvent context) := by
  apply dependentFoldFactorized_to_successfulRaw coordinate context
  apply mem_dependent_fold_predicate_of_components coordinate
    (fun skeleton value =>
      value ∈ exactRawOneFoldTarget context skeleton)
    succeeds foldAccepted
  assumption

#print axioms mem_dependent_fold_successfulRawOneFoldEvent_of_components

end


end AspisK1.V7Tag73FoldOneFoldComponentMembership
