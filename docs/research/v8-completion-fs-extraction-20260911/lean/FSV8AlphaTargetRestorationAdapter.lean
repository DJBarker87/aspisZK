import FSV8AlphaTargetDisposition
import ExtractionCollectorSource

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8AlphaTargetRestorationAdapter

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisV8Completion.FSV8AlphaChallengeInputBridge
open AspisV8Completion.FSV8AlphaTargetDisposition

noncomputable section

inductive AlphaDispositionResult
    (Record RejectReason ResourceReason : Type*) where
  | priorAdversary
      (attempt : ExtractionCollectorSource.AttemptOutcome
        Record RejectReason ResourceReason)
  | priorTarget (entry : TableEntry)
  | absent

def alphaDispositionResult
    {TapeIdentity Observation Statement Proof Result Record RejectReason ResourceReason : Type*}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (checker : ExtractionCollectorSource.ActualResultChecker
      Result Record RejectReason ResourceReason) :
    AlphaDispositionResult Record RejectReason ResourceReason :=
  match alpha_target_disposition origin.firstRun.stateAtAdversaryHalt afterAlphaNonce with
  | .priorAdversaryQ1 _ _ _ =>
      .priorAdversary (ExtractionCollectorSource.sourceAttempt origin
        (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
          postForkController oracleLimits budget replayFuel) checker)
  | .priorTarget entry _ => .priorTarget entry
  | .absent _ => .absent

theorem prior_q1_supplies_fixed_record
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (record : QueryRecord)
    (member : record ∈ freezeAdversaryQ1 origin.firstRun.stateAtAdversaryHalt)
    (inputEq : record.input = alphaCandidateInput afterAlphaNonce) :
    record ∈ (fixedFirstRunRecordFromOrigin origin
      (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).firstRun.q1 ∧
    (fixedFirstRunRecordFromOrigin origin
      (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).transcriptDrivingInput =
      record.input := by
  constructor
  · simpa [FixedFirstRunRecord.firstRun, FirstRun.q1] using member
  · rw [fixedFirstRunRecordFromOrigin_transcriptDrivingInput,
      alphaBoundaryConfiguration_input]
    exact inputEq.symm

theorem prior_q1_checked_replay
    {TapeIdentity Observation Statement Proof Result Record RejectReason ResourceReason : Type*}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (checker : ExtractionCollectorSource.ActualResultChecker
      Result Record RejectReason ResourceReason)
    (record : QueryRecord)
    (member : record ∈ freezeAdversaryQ1 origin.firstRun.stateAtAdversaryHalt)
    (inputEq : record.input = alphaCandidateInput afterAlphaNonce)
    (found : Record)
    (success : ExtractionCollectorSource.sourceAttempt origin
      (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel) checker =
      .checked found) :
    record ∈ (fixedFirstRunRecordFromOrigin origin
      (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).firstRun.q1 ∧
    ∃ output : {run : CoupledReplay TapeIdentity Statement Proof Result //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
              postForkController oracleLimits budget replayFuel)) run},
      constructLegalReplay origin.capability
        (fixedFirstRunRecordFromOrigin origin
          (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
            postForkController oracleLimits budget replayFuel)) = .ok output ∧
      checker.check output.val.returned = .accepted found := by
  have q1 := (prior_q1_supplies_fixed_record origin afterAlphaNonce firstRunUse
    forkOutput postForkController oracleLimits budget replayFuel record member inputEq).1
  have replay := ExtractionCollectorSource.sourceAttempt_checked origin
    (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel) checker found success
  exact ⟨q1, replay⟩

#print axioms prior_q1_supplies_fixed_record
#print axioms prior_q1_checked_replay
end
end AspisV8Completion.FSV8AlphaTargetRestorationAdapter
