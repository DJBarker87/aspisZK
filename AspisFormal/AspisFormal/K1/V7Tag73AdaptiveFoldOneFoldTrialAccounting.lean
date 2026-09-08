import AspisFormal.K1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
import AspisFormal.K1.V7Tag73CausalFoldOneFoldCoordinates
import AspisFormal.K1.V7Tag73K13IdealErrorLedger

/-!
# Finite exposure-trial accounting for causal one-fold failure

Each fixed fold exposure pays the literal 31-bit work factor.  Unioning over
at most `2^31` compiler exposures restores exactly the original degree-three
one-fold error; no grinding normalization is introduced.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73AdaptiveFoldOneFoldTrialAccounting

open MeasureTheory
open AspisK1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldOneFoldCoordinates
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

structure ExactCompilerCausalFoldOneFoldTrials
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    (parameters : ExactCompilerResourceParameters) where
  event : Trial → Set (ExactCompilerSample HiddenTape parameters)
  router : Trial → HiddenTape →
    ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters
  context : Trial → HiddenTape →
    ExactCompilerFoldOneFoldResidual parameters → Digest256 →
      Tag73OrdinarySamplerSkeleton → ExactCausalOneFoldSamplerContext
  covered : ∀ trial hidden,
    jointEventSlice (event trial) hidden ⊆
      exactCompilerCausalFoldOneFoldCoordinates parameters
          (router trial hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent foldAlphaTotalSucceeds
          (fun residual => successfulFoldAlphaTotalEquiv ⁻¹'
            foldSuccessfulRawOneFoldEvent
              (fun fold => successfulRawOneFoldEvent
                (context trial hidden residual fold)))

theorem ExactCompilerCausalFoldOneFoldTrials.event_probability_le_work
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFoldOneFoldTrials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trial : Trial) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      exactOneFoldIdealRawError / (2 : ENNReal) ^ 31 := by
  have bound := exact_compiler_causal_fold_onefold_event_probability_le
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

theorem ExactCompilerCausalFoldOneFoldTrials.failure_union_probability_le
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFoldOneFoldTrials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trialCap : Fintype.card Trial ≤ 2 ^ 31) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) ≤ exactOneFoldIdealRawError := by
  exact finite_work_trial_union_probability_le_base
    (exactCompilerJointLaw hiddenLaw parameters) 31 exactOneFoldIdealRawError
    trials.event trials.event_probability_le_work trialCap

abbrev ExactCompilerExposureIndexedFoldOneFoldTrials
    {HiddenTape : Type} [Fintype HiddenTape]
    (parameters : ExactCompilerResourceParameters) :=
  ExactCompilerCausalFoldOneFoldTrials
    (HiddenTape := HiddenTape)
    (Trial := ExactCompilerExposureTrial parameters) parameters

theorem ExactCompilerExposureIndexedFoldOneFoldTrials.failure_union_probability_le
    {HiddenTape : Type} [Fintype HiddenTape]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerExposureIndexedFoldOneFoldTrials
      (HiddenTape := HiddenTape) parameters)
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) ≤ exactOneFoldIdealRawError := by
  apply ExactCompilerCausalFoldOneFoldTrials.failure_union_probability_le
    trials
  simpa [ExactCompilerExposureTrial] using foldExposureCap

end


#print axioms ExactCompilerCausalFoldOneFoldTrials
#print axioms ExactCompilerCausalFoldOneFoldTrials.event_probability_le_work
#print axioms ExactCompilerCausalFoldOneFoldTrials.failure_union_probability_le
#print axioms
  ExactCompilerExposureIndexedFoldOneFoldTrials.failure_union_probability_le

end AspisK1.V7Tag73AdaptiveFoldOneFoldTrialAccounting
