import V7CallerCurrentReleaseR30ChallengeCanonical
import V7ProductionSnapshotObserverR28AcceptedTail

/-!
# Canonical transcript challenges in an accepted production execution

The three accepted relation rounds retain their literal successful
`Transcript::challenge_qm31` equations.  This module applies the symbolic
sampler theorem to those exact calls.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7ProductionSnapshotObserverR30ChallengesCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR30ChallengeCanonical
open AspisV7ProductionSnapshotObserverR28AcceptedTail

theorem accepted_production_tail_challenges_canonical
    {hash : AspisV7ProductionSnapshotObserverR28SourceBridge.HashFn}
    {wire : AspisV7ProductionSnapshotObserverR28SourceBridge.Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext :
      AspisV7ProductionSnapshotObserverR28SourceBridge.HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : AspisV7ProductionSnapshotObserverR28SourceBridge.Statement}
    {queryFold :
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.QueryFold}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : V7CallerCurrentReleaseR26AcceptedInnerDispatch.AcceptedInnerDispatch
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.terminalInst
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.queryFoldInst
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement queryFold () true transcript (some snapshot)}
    {chain :
      V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge.AcceptedInnerPrechallengeChain
        inner}
    (acceptedTail : AcceptedProductionTail inner chain) :
    GeneratedCanonicalQM31 acceptedTail.source.roundOne.alphaOne ∧
    GeneratedCanonicalQM31 acceptedTail.source.roundTwo.alphaTwo ∧
    GeneratedCanonicalQM31 acceptedTail.source.roundThree.alphaThree := by
  exact ⟨
    successful_challenge_qm31_canonical
      acceptedTail.source.roundOne.transcriptAbsorb
      acceptedTail.source.roundOne.transcriptChallenge
      acceptedTail.source.roundOne.alphaOne
      acceptedTail.source.roundOne.challengeSuccess,
    successful_challenge_qm31_canonical
      acceptedTail.source.roundTwo.transcriptAbsorb
      acceptedTail.source.roundTwo.transcriptChallenge
      acceptedTail.source.roundTwo.alphaTwo
      acceptedTail.source.roundTwo.challengeSuccess,
    successful_challenge_qm31_canonical
      acceptedTail.source.roundThree.transcriptAbsorb
      acceptedTail.source.roundThree.transcriptChallenge
      acceptedTail.source.roundThree.alphaThree
      acceptedTail.source.roundThree.challengeSuccess⟩

#print axioms accepted_production_tail_challenges_canonical

end V7ProductionSnapshotObserverR30ChallengesCanonical
