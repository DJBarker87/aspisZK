import V7CallerCurrentReleaseR30PointClaimsCanonical
import V7CallerCurrentReleaseR30SumProducts3Canonical
import V7ProductionSnapshotObserverR28AcceptedTail

/-!
# Canonical point claims and initial running claim in production

This module applies the decoder and arithmetic canonicality theorems to the
literal calls retained by one accepted production execution.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7ProductionSnapshotObserverR30InitialClaimCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR30FixedFieldCanonical
open V7CallerCurrentReleaseR30PointClaimsCanonical
open V7CallerCurrentReleaseR30SumProducts3Canonical
open AspisV7ProductionSnapshotObserverR28AcceptedTail

theorem accepted_production_point_claims_canonical
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
    (inner : V7CallerCurrentReleaseR26AcceptedInnerDispatch.AcceptedInnerDispatch
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.terminalInst
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.queryFoldInst
      AspisV7ProductionSnapshotObserverR28ToR26Prechallenge.prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement queryFold () true transcript (some snapshot)) :
    CanonicalClaims inner.pointClaims := by
  exact fixed_reader_point_claims_canonical inner.transcript1 inner.transcript2
    inner.fields1 inner.fields2 inner.pointClaims inner.pointClaimsRun

theorem accepted_production_initial_running_claim_canonical
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
    (chain :
      V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge.AcceptedInnerPrechallengeChain
        inner) :
    GeneratedCanonicalQM31 chain.outer.runningClaim := by
  let outer := chain.outer
  have inactiveCanonical : GeneratedCanonicalQM31 outer.inactiveClaim :=
    fixed_reader_next_qm31_canonical inner.fields2 outer.fieldsAfterPrefix
      outer.inactiveClaim outer.inactiveClaimRun
  have contributionCanonical :
      GeneratedCanonicalQM31 outer.claimContribution :=
    successful_qm31_sum_products3_canonical outer.pointScales
      outer.combinedClaims outer.claimContribution outer.claimContributionRun
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_add_corresponds outer.inactiveClaim
      outer.claimContribution inactiveCanonical contributionCanonical
  have runningExact : outer.runningClaim = expected :=
    Result.ok.inj (outer.runningClaimRun.symm.trans expectedRun)
  change GeneratedCanonicalQM31 outer.runningClaim
  rw [runningExact]
  exact expectedCanonical

#print axioms accepted_production_point_claims_canonical
#print axioms accepted_production_initial_running_claim_canonical

end V7ProductionSnapshotObserverR30InitialClaimCanonical
