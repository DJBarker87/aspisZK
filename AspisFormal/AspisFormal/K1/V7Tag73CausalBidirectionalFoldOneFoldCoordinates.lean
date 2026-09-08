import AspisFormal.K1.V7Tag73BidirectionalFoldOneFoldCoordinates
import AspisFormal.K1.V7Tag73CausalFoldOneFoldTapeBridge
import AspisFormal.K1.V7Tag73HiddenTapeAveraging

/-!
# Compiler probability over bidirectional fold/alpha coordinates

The five-slot router isolates exactly the accepted 31-bit fold-work answer and
the four alpha output blocks, irrespective of which of the two source inputs
was exposed first.  Every other oracle answer, including alpha advance blocks,
final work and the q16 forest, remains in the residual.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CausalBidirectionalFoldOneFoldCoordinates

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CausalFoldRawOneFoldProduct
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- One fixed bidirectional router has the exact work-times-degree-three
probability bound.  This theorem contains no source or acceptance premise;
the caller supplies only deterministic event coverage. -/
theorem exact_compiler_causal_bidirectional_fold_onefold_event_probability_le
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (router : HiddenTape →
      ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters)
    (context : HiddenTape →
      ExactCompilerBidirectionalFoldOneFoldResidual parameters →
        Digest256 → Tag73OrdinarySamplerSkeleton →
          ExactCausalOneFoldSamplerContext)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
          (router hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent foldAlphaTotalSucceeds
          (fun residual => successfulFoldAlphaTotalEquiv ⁻¹'
            foldSuccessfulRawOneFoldEvent
              (fun fold => successfulRawOneFoldEvent
                (context hidden residual fold)))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_fold_onefold_probability_le
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
      (router hidden))
    (context hidden) (jointEventSlice event hidden) (covered hidden)

end

#print axioms
  exact_compiler_causal_bidirectional_fold_onefold_event_probability_le

end AspisK1.V7Tag73CausalBidirectionalFoldOneFoldCoordinates
