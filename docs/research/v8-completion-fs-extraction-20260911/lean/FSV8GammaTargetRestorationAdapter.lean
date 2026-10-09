import FSV8GammaTargetDisposition
import ExtractionCollectorSource

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8GammaTargetRestorationAdapter

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisV8Completion.FSV8GammaChallengeInputBridge
open AspisV8Completion.FSV8GammaTargetDisposition

noncomputable section

/-! This is the source-facing boundary consumer.  A prior adversary query is
fed to the existing start-only K1.6 replay constructor; a table hit and an
absent target remain explicit data, rather than being treated as a fresh
successful programming opportunity. -/

inductive GammaDispositionResult
    (Record RejectReason ResourceReason : Type*) where
  | priorAdversary
      (attempt : ExtractionCollectorSource.AttemptOutcome
        Record RejectReason ResourceReason)
  | priorTarget (entry : TableEntry)
  | absent

def gammaDispositionResult
    {TapeIdentity Observation Statement Proof Result Record RejectReason ResourceReason : Type*}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (afterNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (checker : ExtractionCollectorSource.ActualResultChecker
      Result Record RejectReason ResourceReason) :
    GammaDispositionResult Record RejectReason ResourceReason :=
  match gamma_target_disposition origin.firstRun.stateAtAdversaryHalt afterNonce with
  | .priorAdversaryQ1 _ _ _ =>
      .priorAdversary (ExtractionCollectorSource.sourceAttempt origin
        (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
          postForkController oracleLimits budget replayFuel) checker)
  | .priorTarget entry _ => .priorTarget entry
  | .absent _ => .absent

theorem prior_q1_supplies_fixed_record
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (afterNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (record : QueryRecord)
    (member : record ∈ freezeAdversaryQ1 origin.firstRun.stateAtAdversaryHalt)
    (inputEq : record.input = gammaCandidateInput afterNonce) :
    record ∈ (fixedFirstRunRecordFromOrigin origin
      (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).firstRun.q1 ∧
    (fixedFirstRunRecordFromOrigin origin
      (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).transcriptDrivingInput =
      record.input := by
  constructor
  · simpa [FixedFirstRunRecord.firstRun, FirstRun.q1] using member
  · rw [fixedFirstRunRecordFromOrigin_transcriptDrivingInput,
      gammaBoundaryConfiguration_input]
    exact inputEq.symm

theorem prior_q1_checked_replay
    {TapeIdentity Observation Statement Proof Result Record RejectReason ResourceReason : Type*}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (afterNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (checker : ExtractionCollectorSource.ActualResultChecker
      Result Record RejectReason ResourceReason)
    (record : QueryRecord)
    (member : record ∈ freezeAdversaryQ1 origin.firstRun.stateAtAdversaryHalt)
    (inputEq : record.input = gammaCandidateInput afterNonce)
    (found : Record)
    (success : ExtractionCollectorSource.sourceAttempt origin
      (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel) checker =
      .checked found) :
    record ∈ (fixedFirstRunRecordFromOrigin origin
      (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).firstRun.q1 ∧
    ∃ output : {run : CoupledReplay TapeIdentity Statement Proof Result //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
              postForkController oracleLimits budget replayFuel)) run},
      constructLegalReplay origin.capability
        (fixedFirstRunRecordFromOrigin origin
          (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
            postForkController oracleLimits budget replayFuel)) = .ok output ∧
      checker.check output.val.returned = .accepted found := by
  have q1 := (prior_q1_supplies_fixed_record origin afterNonce firstRunUse
    forkOutput postForkController oracleLimits budget replayFuel record member inputEq).1
  have replay := ExtractionCollectorSource.sourceAttempt_checked origin
    (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel) checker found success
  exact ⟨q1, replay⟩

#print axioms prior_q1_supplies_fixed_record
#print axioms prior_q1_checked_replay
end
end AspisV8Completion.FSV8GammaTargetRestorationAdapter
