import AspisFormal.K1.V7Tag73CausalFoldOneFoldTapeBridge
import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates

/-!
# Compiler coordinates for one fold-positioned one-fold trial

The existing 518-slot causal router already isolates the fold-work answer,
four alpha-zero output blocks, final-work answer, and q16 forest.  For the
one-fold event only the fold answer and alpha blocks carry probability; final
work, q16, and every unused answer are reassociated into the residual.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CausalFoldOneFoldCoordinates

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CausalFoldRawOneFoldProduct
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

abbrev ExactCompilerFoldOneFoldResidual
    (parameters : ExactCompilerResourceParameters) :=
  ExactCompilerFoldAlphaFinalWorkQ16Residual parameters ×
    (Digest256 × Q16CandidateDigestForest)

def foldOneFoldCoordinateRegroup
    (Residual : Type) :
    ((Residual × AlphaZeroDigestBlocks) ×
        (Digest256 × (Digest256 × Q16CandidateDigestForest))) ≃
      ((Residual × (Digest256 × Q16CandidateDigestForest)) ×
        (Digest256 × FourGammaBlocks)) where
  toFun coordinates :=
    ((coordinates.1.1, coordinates.2.2),
      (coordinates.2.1, coordinates.1.2))
  invFun coordinates :=
    ((coordinates.1.1, coordinates.2.2),
      (coordinates.2.1, coordinates.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def exactCompilerCausalFoldOneFoldCoordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerFoldOneFoldResidual parameters ×
        (Digest256 × FourGammaBlocks) :=
  (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router).trans
    (foldOneFoldCoordinateRegroup
      (ExactCompilerFoldAlphaFinalWorkQ16Residual parameters))

theorem exact_compiler_causal_fold_onefold_event_probability_le
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (router : HiddenTape →
      ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (context : HiddenTape → ExactCompilerFoldOneFoldResidual parameters →
      Digest256 → Tag73OrdinarySamplerSkeleton →
        ExactCausalOneFoldSamplerContext)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      exactCompilerCausalFoldOneFoldCoordinates parameters (router hidden) ⁻¹'
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
    (exactCompilerCausalFoldOneFoldCoordinates parameters (router hidden))
    (context hidden) (jointEventSlice event hidden) (covered hidden)

end


#print axioms foldOneFoldCoordinateRegroup
#print axioms exactCompilerCausalFoldOneFoldCoordinates
#print axioms exact_compiler_causal_fold_onefold_event_probability_le

end AspisK1.V7Tag73CausalFoldOneFoldCoordinates
