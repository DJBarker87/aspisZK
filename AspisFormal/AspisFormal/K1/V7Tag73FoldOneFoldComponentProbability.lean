import AspisFormal.K1.V7Tag73FoldOneFoldComponentCoverage

/-!
# Probability bound from component-wise fold/alpha coverage

This leaf feeds deterministic component coverage into the existing exact
work-times-degree-three uniform-tape theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73FoldOneFoldComponentProbability

open MeasureTheory
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73FoldOneFoldComponentCoverage
open AspisK1.V7Tag73FoldOneFoldComponentMembership
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Exact uniform probability bound obtained from the three deterministic
component facts at every member of the event. -/
theorem uniform_tape_fold_onefold_probability_le_of_components
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    (coordinates : Tape ≃ Residual × (Digest256 × FourGammaBlocks))
    (context : Residual → Digest256 → Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (event : Set Tape)
    (componentCovered : ∀ tape, tape ∈ event →
      FoldOneFoldComponentFacts (coordinates tape)
        (context (coordinates tape).1 (coordinates tape).2.1)) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) := by
  apply uniform_tape_dependent_fold_onefold_probability_le coordinates context
    event
  exact foldOneFoldComponentFacts_cover_public_event coordinates context event
    componentCovered

#print axioms uniform_tape_fold_onefold_probability_le_of_components

end

end AspisK1.V7Tag73FoldOneFoldComponentProbability
