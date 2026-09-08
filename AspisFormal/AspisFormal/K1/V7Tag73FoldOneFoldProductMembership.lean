import AspisFormal.K1.V7Tag73CausalFoldOneFoldTapeBridge
import AspisFormal.K1.V7Tag73SuccessfulRawOneFoldProductMembership

/-! # Generic fold/alpha product-event membership -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73FoldOneFoldProductMembership

open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CausalFoldRawOneFoldProduct
open AspisK1.V7Tag73CausalRawOneFoldProductProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulRawOneFoldProductMembership
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Named form of the nested fold/alpha factorized target event. -/
def dependentFoldFactorizedOneFoldEventMember
    {Residual : Type}
    (coordinates : Residual × (Digest256 × FourGammaBlocks))
    (target : Tag73OrdinarySamplerSkeleton → Set QM31Exact) : Prop :=
  coordinates ∈
    dependentSuccessfulSubtypeEvent foldAlphaTotalSucceeds
      (fun _residual => successfulFoldAlphaTotalEquiv ⁻¹'
        foldSuccessfulRawOneFoldEvent
          (fun _fold => successfulOrdinaryExactFactorization ⁻¹'
            dependentProductEvent target))

/-- Package an abstract accepted fold, successful alpha raw stream, and exact
slice membership into the nested dependent event used by the probability
theorem.  No production verifier term appears in this lemma. -/
theorem mem_dependent_fold_factorized_oneFoldEvent
    {Residual : Type}
    (coordinates : Residual × (Digest256 × FourGammaBlocks))
    (target : Tag73OrdinarySamplerSkeleton → Set QM31Exact)
    (succeeds : foldAlphaTotalSucceeds coordinates.2)
    (foldAccepted : FoldWork31Accepted coordinates.2.1)
    (raw : SuccessfulTag73RawStream)
    (rawExact :
      (⟨fourGammaBlocksRawEquiv coordinates.2.2, succeeds⟩ :
        SuccessfulTag73RawStream) = raw)
    (member : successfulOrdinaryExactValue raw ∈
      target (successfulOrdinaryExactFactorization raw).1) :
    dependentFoldFactorizedOneFoldEventMember coordinates target := by
  unfold dependentFoldFactorizedOneFoldEventMember
  change ∃ h : foldAlphaTotalSucceeds coordinates.2,
    successfulFoldAlphaTotalEquiv ⟨coordinates.2, h⟩ ∈
      foldSuccessfulRawOneFoldEvent
        (fun _fold => successfulOrdinaryExactFactorization ⁻¹'
          dependentProductEvent target)
  refine ⟨succeeds, ?_⟩
  change
    (⟨fourGammaBlocksRawEquiv coordinates.2.2, succeeds⟩ :
        SuccessfulTag73RawStream) ∈
      if FoldWork31Accepted coordinates.2.1 then
        successfulOrdinaryExactFactorization ⁻¹'
          dependentProductEvent target
      else ∅
  rw [if_pos foldAccepted, rawExact]
  exact mem_factorized_dependentProductEvent_of_value target raw member

#print axioms mem_dependent_fold_factorized_oneFoldEvent

end


end AspisK1.V7Tag73FoldOneFoldProductMembership
