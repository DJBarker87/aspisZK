import FSV8GammaChallengeInputBridge
import FSV8V7StateAlignment
import FSV8V7OracleMachineBridge

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8GammaOriginHistoryAdapter
open FSOracleExecution FSBoundedTranscript
open AspisK1.V7FsAokExperiment AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open FSV8V7OracleMachineBridge FSV8V7StateAlignment
open FSV8GammaChallengeInputBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block

/-! `projectRecord` retains input/answer/freshness but erases the V7 actor.
This is the maximal history lift available from StateAligned without
inventing adversary/verifier provenance. -/
theorem projected_event_lifts_to_v7_record
    {steps : Nat} {tape : FSBoundedTranscript.Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs)
    (event : Event Bytes Block)
    (eventMem : event ∈ fs.log) :
    ∃ record, record ∈ v7.history ∧ projectRecord record = event := by
  have mapped : event ∈ v7.history.map projectRecord := by
    rw [← aligned.history]
    exact eventMem
  obtain ⟨record, recordMem, recordEq⟩ := List.mem_map.mp mapped
  exact ⟨record, recordMem, recordEq⟩

/-! Once the lifted record is known to be the origin's adversary query, the
prior fixed-record theorem supplies q1 membership.  The actor and origin-cut
hypotheses remain explicit because StateAligned/projectRecord do not provide
either fact. -/
theorem origin_q1_membership_from_lifted_record
    {TapeIdentity Statement Proof : Type*}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Returned)
    (afterNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (record : QueryRecord)
    (recordMem : record ∈ origin.firstRun.stateAtAdversaryHalt.history)
    (recordActor : record.actor = .adversary)
    (recordInput : record.input = gammaCandidateInput afterNonce) :
    record ∈ (fixedFirstRunRecordFromOrigin origin
      (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).firstRun.q1 := by
  exact (fixedRecord_q1_contains_gamma origin afterNonce firstRunUse forkOutput
    postForkController oracleLimits budget replayFuel record recordMem recordActor
    recordInput).1

#print axioms projected_event_lifts_to_v7_record
#print axioms origin_q1_membership_from_lifted_record
end AspisV8Completion.FSV8GammaOriginHistoryAdapter
