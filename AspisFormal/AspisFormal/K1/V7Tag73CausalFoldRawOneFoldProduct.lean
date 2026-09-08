import AspisFormal.K1.V7Tag73CausalRawOneFoldProbability
import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability

/-!
# Positioned fold-work times causal one-fold probability

For one fixed pre-answer fold trial, the work predicate contributes `2^-31`
and the ordinary alpha response contributes the unchanged degree-three bound.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CausalFoldRawOneFoldProduct

open MeasureTheory
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldProductProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

def foldSuccessfulRawOneFoldEvent
    (bad : Digest256 → Set SuccessfulTag73RawStream) :
    Set (Digest256 × SuccessfulTag73RawStream) :=
  dependentProductEvent fun fold =>
    if FoldWork31Accepted fold then bad fold else ∅

theorem uniform_fold_successful_raw_onefold_probability_le
    (bad : Digest256 → Set SuccessfulTag73RawStream)
    (badProbability : ∀ fold,
      (PMF.uniformOfFintype SuccessfulTag73RawStream).toOuterMeasure
          (bad fold) ≤
        (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) :
    (PMF.uniformOfFintype
      (Digest256 × SuccessfulTag73RawStream)).toOuterMeasure
        (foldSuccessfulRawOneFoldEvent bad) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) := by
  classical
  rw [uniform_product_event_probability_eq_weighted_slices]
  calc
    (∑' fold : Digest256,
        (PMF.uniformOfFintype Digest256) fold *
          (PMF.uniformOfFintype SuccessfulTag73RawStream).toOuterMeasure
            (productEventFstSlice
              (foldSuccessfulRawOneFoldEvent bad) fold)) ≤
      ∑' fold : Digest256,
        (PMF.uniformOfFintype Digest256) fold *
          (if FoldWork31Accepted fold then
            (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)
          else 0) := by
      exact ENNReal.tsum_le_tsum fun fold => by
        apply mul_le_mul_left'
        rw [foldSuccessfulRawOneFoldEvent,
          productEventFstSlice_dependentProductEvent]
        by_cases accepted : FoldWork31Accepted fold
        · rw [if_pos accepted, if_pos accepted]
          exact badProbability fold
        · simp [accepted]
    _ = (∑' fold : Digest256,
          foldWork31AcceptedEvent.indicator
            (fun fold => (PMF.uniformOfFintype Digest256) fold) fold) *
        ((foldChallengeCap : ENNReal) /
          ((P ^ 4 : Nat) : ENNReal)) := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro fold
      by_cases accepted : FoldWork31Accepted fold <;>
        simp [foldWork31AcceptedEvent, accepted]
    _ = (PMF.uniformOfFintype Digest256).toOuterMeasure
          foldWork31AcceptedEvent *
            ((foldChallengeCap : ENNReal) /
              ((P ^ 4 : Nat) : ENNReal)) := by
      rw [PMF.toOuterMeasure_apply]
    _ = ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) := by
      rw [uniform_fold_work_31_probability_exact]

end


#print axioms uniform_fold_successful_raw_onefold_probability_le

end AspisK1.V7Tag73CausalFoldRawOneFoldProduct
