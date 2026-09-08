import AspisFormal.K1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
import AspisFormal.K1.V7Tag73CausalBidirectionalFoldOneFoldCoordinates
import AspisFormal.K1.V7Tag73K13IdealErrorLedger

/-!
# Exposure-trial accounting for bidirectional causal one-fold failure

Each fixed first-creation exposure pays the literal 31-bit work factor.  The
union over at most `2^31` possible exposures cancels that factor exactly and
leaves the degree-three one-fold error.  No grinding normalization or
independence assumption is introduced.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73AdaptiveBidirectionalFoldOneFoldTrialAccounting

open MeasureTheory
open AspisK1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalBidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CausalFoldRawOneFoldProduct
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

structure ExactCompilerCausalBidirectionalFoldOneFoldTrials
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    (parameters : ExactCompilerResourceParameters) where
  event : Trial → Set (ExactCompilerSample HiddenTape parameters)
  router : Trial → HiddenTape →
    ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters
  context : Trial → HiddenTape →
    ExactCompilerBidirectionalFoldOneFoldResidual parameters → Digest256 →
      Tag73OrdinarySamplerSkeleton → ExactCausalOneFoldSamplerContext
  covered : ∀ trial hidden,
    jointEventSlice (event trial) hidden ⊆
      exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
          (router trial hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent foldAlphaTotalSucceeds
          (fun residual => successfulFoldAlphaTotalEquiv ⁻¹'
            foldSuccessfulRawOneFoldEvent
              (fun fold => successfulRawOneFoldEvent
                (context trial hidden residual fold)))

theorem ExactCompilerCausalBidirectionalFoldOneFoldTrials.event_probability_le_work
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalBidirectionalFoldOneFoldTrials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trial : Trial) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      exactOneFoldIdealRawError / (2 : ENNReal) ^ 31 := by
  have bound :=
    exact_compiler_causal_bidirectional_fold_onefold_event_probability_le
      hiddenLaw parameters (trials.router trial) (trials.context trial)
      (trials.event trial) (trials.covered trial)
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) at bound
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) /
        (2 : ENNReal) ^ 31
  calc
    _ ≤ ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) := bound
    _ = _ := by
      simp only [div_eq_mul_inv, one_mul]
      ac_rfl

theorem ExactCompilerCausalBidirectionalFoldOneFoldTrials.failure_union_probability_le
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalBidirectionalFoldOneFoldTrials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trialCap : Fintype.card Trial ≤ 2 ^ 31) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) ≤ exactOneFoldIdealRawError := by
  exact finite_work_trial_union_probability_le_base
    (exactCompilerJointLaw hiddenLaw parameters) 31 exactOneFoldIdealRawError
    trials.event trials.event_probability_le_work trialCap

abbrev ExactCompilerExposureIndexedBidirectionalFoldOneFoldTrials
    {HiddenTape : Type} [Fintype HiddenTape]
    (parameters : ExactCompilerResourceParameters) :=
  ExactCompilerCausalBidirectionalFoldOneFoldTrials
    (HiddenTape := HiddenTape)
    (Trial := ExactCompilerExposureTrial parameters) parameters

theorem ExactCompilerExposureIndexedBidirectionalFoldOneFoldTrials.failure_union_probability_le
    {HiddenTape : Type} [Fintype HiddenTape]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerExposureIndexedBidirectionalFoldOneFoldTrials
      (HiddenTape := HiddenTape) parameters)
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) ≤ exactOneFoldIdealRawError := by
  apply ExactCompilerCausalBidirectionalFoldOneFoldTrials.failure_union_probability_le
    trials
  simpa [ExactCompilerExposureTrial] using foldExposureCap

end

#print axioms ExactCompilerCausalBidirectionalFoldOneFoldTrials
#print axioms
  ExactCompilerCausalBidirectionalFoldOneFoldTrials.event_probability_le_work
#print axioms
  ExactCompilerCausalBidirectionalFoldOneFoldTrials.failure_union_probability_le
#print axioms
  ExactCompilerExposureIndexedBidirectionalFoldOneFoldTrials.failure_union_probability_le

end AspisK1.V7Tag73AdaptiveBidirectionalFoldOneFoldTrialAccounting
