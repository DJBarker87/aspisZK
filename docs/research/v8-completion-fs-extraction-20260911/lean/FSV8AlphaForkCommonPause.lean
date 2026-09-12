import FSV8AlphaChallengeInputBridge
import AspisFormal.K1.V7FsStateRestorationCoupling

/-!
# Common pre-alpha pause for fork-output variations

The alpha replay configurations below vary only the value programmed at the
actual first alpha-candidate input.  Successful uses of the operational replay
constructor therefore have one canonical first driving split and one exact
prefix execution.  This is stronger than equality of parsed response values:
it identifies the chronological oracle/program pause before either fork output
is installed.

This pairwise theorem does not yet prove that a collected matrix used these
configurations.  That is a separate producer obligation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8AlphaForkCommonPause

open FSBoundedTranscript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open FSV8AlphaChallengeInputBridge

noncomputable section

abbrev Bytes := List UInt8

/-- Two successful replays which differ only in the programmed alpha output
share the exact canonical pause before that programming. -/
theorem alpha_fork_outputs_share_exact_pause
    {TapeIdentity Observation Statement Proof : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Bytes)
    (afterAlphaNonce : Transcript)
    (firstRunUse : ResourceUse) (leftOutput rightOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (leftReplay :
      {run : CoupledReplay TapeIdentity Statement Proof Bytes //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (alphaBoundaryConfiguration afterAlphaNonce firstRunUse leftOutput
              postForkController oracleLimits budget replayFuel)) run})
    (rightReplay :
      {run : CoupledReplay TapeIdentity Statement Proof Bytes //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (alphaBoundaryConfiguration afterAlphaNonce firstRunUse rightOutput
              postForkController oracleLimits budget replayFuel)) run})
    (leftSuccess :
      constructLegalReplay origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (alphaBoundaryConfiguration afterAlphaNonce firstRunUse leftOutput
              postForkController oracleLimits budget replayFuel)) =
        .ok leftReplay)
    (rightSuccess :
      constructLegalReplay origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (alphaBoundaryConfiguration afterAlphaNonce firstRunUse rightOutput
              postForkController oracleLimits budget replayFuel)) =
        .ok rightReplay) :
    leftReplay.val.replayPrefix = rightReplay.val.replayPrefix ∧
      leftReplay.val.driving = rightReplay.val.driving ∧
      leftReplay.val.suffix = rightReplay.val.suffix ∧
      leftReplay.val.prefixRun = rightReplay.val.prefixRun ∧
      leftReplay.val.derivedPauseOracle = rightReplay.val.derivedPauseOracle ∧
      leftReplay.val.residualProgram = rightReplay.val.residualProgram := by
  obtain ⟨leftSplit, leftSplitEq, leftPrefix, leftDriving, leftSuffix,
      leftRun⟩ :=
    map_success_exposes_driving_split_and_exact_prefix_run origin.capability
      (fixedFirstRunRecordFromOrigin origin
        (alphaBoundaryConfiguration afterAlphaNonce firstRunUse leftOutput
          postForkController oracleLimits budget replayFuel)) leftReplay
      leftSuccess
  obtain ⟨rightSplit, rightSplitEq, rightPrefix, rightDriving, rightSuffix,
      rightRun⟩ :=
    map_success_exposes_driving_split_and_exact_prefix_run origin.capability
      (fixedFirstRunRecordFromOrigin origin
        (alphaBoundaryConfiguration afterAlphaNonce firstRunUse rightOutput
          postForkController oracleLimits budget replayFuel)) rightReplay
      rightSuccess
  have splitEq : leftSplit = rightSplit := by
    apply Option.some.inj
    exact leftSplitEq.symm.trans rightSplitEq
  subst rightSplit
  have prefixEq : leftReplay.val.replayPrefix = rightReplay.val.replayPrefix :=
    leftPrefix.trans rightPrefix.symm
  have drivingEq : leftReplay.val.driving = rightReplay.val.driving :=
    leftDriving.trans rightDriving.symm
  have suffixEq : leftReplay.val.suffix = rightReplay.val.suffix :=
    leftSuffix.trans rightSuffix.symm
  have runEq : leftReplay.val.prefixRun = rightReplay.val.prefixRun := by
    exact leftRun.trans rightRun.symm
  rcases leftReplay.property with
    ⟨_, _, _, _, _, _, _, leftPause, leftResidual, _, _, _, _, _, _, _, _, _⟩
  rcases rightReplay.property with
    ⟨_, _, _, _, _, _, _, rightPause, rightResidual, _, _, _, _, _, _, _, _, _⟩
  have pauseEq : leftReplay.val.derivedPauseOracle =
      rightReplay.val.derivedPauseOracle :=
    leftPause.trans ((congrArg PrefixRun.oracle runEq).trans rightPause.symm)
  have residualEq : leftReplay.val.residualProgram =
      rightReplay.val.residualProgram := by
    have halted : PrefixHalt.paused leftReplay.val.residualProgram =
        .paused rightReplay.val.residualProgram :=
      leftResidual.symm.trans
        ((congrArg PrefixRun.halt runEq).trans rightResidual)
    exact PrefixHalt.paused.inj halted
  exact ⟨prefixEq, drivingEq, suffixEq, runEq, pauseEq, residualEq⟩

#print axioms alpha_fork_outputs_share_exact_pause

end
end AspisV8Completion.FSV8AlphaForkCommonPause
