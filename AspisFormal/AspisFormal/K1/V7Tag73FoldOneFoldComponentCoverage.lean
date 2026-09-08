import AspisFormal.K1.V7Tag73FoldOneFoldComponentMembership

/-!
# Component-wise coverage of the public fold/alpha event

This leaf separates deterministic coverage from the probability theorem.  A
caller supplies only the three named component facts for each event member.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73FoldOneFoldComponentCoverage

open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CausalFoldRawOneFoldProduct
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73FoldOneFoldComponentMembership
open AspisK1.V7Tag73FoldOneFoldEventRepresentation
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Per-coordinate component facts cover exactly the nested public event used
by the work-times-degree-three probability theorem. -/
theorem foldOneFoldComponentFacts_cover_public_event
    {Tape Residual : Type}
    (coordinates : Tape ≃ Residual × (Digest256 × FourGammaBlocks))
    (context : Residual → Digest256 → Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (event : Set Tape)
    (componentCovered : ∀ tape, tape ∈ event →
      FoldOneFoldComponentFacts (coordinates tape)
        (context (coordinates tape).1 (coordinates tape).2.1)) :
    event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent foldAlphaTotalSucceeds
        (fun residual => successfulFoldAlphaTotalEquiv ⁻¹'
          foldSuccessfulRawOneFoldEvent
            (fun fold => successfulRawOneFoldEvent
              (context residual fold))) := by
  intro tape eventMember
  apply dependentFoldRawEventMember_to_family (coordinates tape)
    (fun residual fold => successfulRawOneFoldEvent
      (context residual fold))
  exact foldOneFoldComponentFacts_mem (coordinates tape)
    (context (coordinates tape).1 (coordinates tape).2.1)
    (componentCovered tape eventMember)

#print axioms foldOneFoldComponentFacts_cover_public_event

end

end AspisK1.V7Tag73FoldOneFoldComponentCoverage
