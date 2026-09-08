import AspisFormal.K1.V7Tag73CausalFoldRawOneFoldProduct
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge
import AspisFormal.K1.V7Tag73VariablePrefixGammaFactorization

/-!
# Compiler-tape bridge for one fold-positioned one-fold trial
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CausalFoldOneFoldTapeBridge

open MeasureTheory
open AspisK1.V7Tag73CausalFoldRawOneFoldProduct
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

def foldAlphaTotalSucceeds
    (coordinates : Digest256 × FourGammaBlocks) : Prop :=
  Tag73RawSucceeds (fourGammaBlocksRawEquiv coordinates.2)

instance foldAlphaTotalSucceedsDecidable
    (coordinates : Digest256 × FourGammaBlocks) :
    Decidable (foldAlphaTotalSucceeds coordinates) := by
  unfold foldAlphaTotalSucceeds
  infer_instance

def successfulFoldAlphaTotalEquiv :
    {coordinates : Digest256 × FourGammaBlocks //
      foldAlphaTotalSucceeds coordinates} ≃
      Digest256 × SuccessfulTag73RawStream where
  toFun coordinates :=
    (coordinates.1.1,
      ⟨fourGammaBlocksRawEquiv coordinates.1.2, coordinates.2⟩)
  invFun coordinates :=
    ⟨(coordinates.1, fourGammaBlocksRawEquiv.symm coordinates.2.1), by
      simpa [foldAlphaTotalSucceeds] using coordinates.2.2⟩
  left_inv coordinates := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact fourGammaBlocksRawEquiv.symm_apply_apply coordinates.1.2
  right_inv coordinates := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact fourGammaBlocksRawEquiv.apply_symm_apply coordinates.2.1

theorem uniform_tape_dependent_fold_onefold_probability_le
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    (coordinates : Tape ≃ Residual × (Digest256 × FourGammaBlocks))
    (context : Residual → Digest256 → Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent foldAlphaTotalSucceeds
        (fun residual => successfulFoldAlphaTotalEquiv ⁻¹'
          foldSuccessfulRawOneFoldEvent
            (fun fold => successfulRawOneFoldEvent
              (context residual fold)))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) := by
  letI : Nonempty
      {coordinates : Digest256 × FourGammaBlocks //
        foldAlphaTotalSucceeds coordinates} := by
    exact ⟨⟨(Classical.choice inferInstance,
      fourGammaBlocksRawEquiv.symm successfulTag73RawStreamExample.1),
      successfulTag73RawStreamExample.2⟩⟩
  apply uniform_tape_dependent_successful_event_probability_le
    foldAlphaTotalSucceeds coordinates successfulFoldAlphaTotalEquiv
    (fun residual => foldSuccessfulRawOneFoldEvent
      (fun fold => successfulRawOneFoldEvent (context residual fold)))
    (((1 : ENNReal) / (2 : ENNReal) ^ 31) *
      ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)))
  · intro residual
    apply uniform_fold_successful_raw_onefold_probability_le
      (fun fold => successfulRawOneFoldEvent (context residual fold))
    intro fold
    let current : Tag73OrdinarySamplerSkeleton →
        ExactCausalOneFoldSamplerContext := context residual fold
    change (PMF.uniformOfFintype SuccessfulTag73RawStream).toOuterMeasure
        (successfulRawOneFoldEvent current) ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)
    have lawExact :
        PMF.uniformOfFintype SuccessfulTag73RawStream =
          successfulRawOneFoldUniformLaw := by
      unfold successfulRawOneFoldUniformLaw
      exact congrArg
        (fun fintype : Fintype SuccessfulTag73RawStream =>
          @PMF.uniformOfFintype SuccessfulTag73RawStream fintype
            instNonemptySuccessfulTag73RawStream)
        (Subsingleton.elim _ _)
    rw [lawExact]
    exact successful_raw_onefold_uniform_law_probability_le current
  · exact covered

end


#print axioms successfulFoldAlphaTotalEquiv
#print axioms uniform_tape_dependent_fold_onefold_probability_le

end AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
