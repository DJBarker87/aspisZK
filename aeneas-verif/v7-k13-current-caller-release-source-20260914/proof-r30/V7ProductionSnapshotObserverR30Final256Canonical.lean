import V7CallerCurrentReleaseR30Final256Canonical
import V7ProductionSnapshotObserverR30RelationRowsCanonical

/-!
# Canonical final-256 values in an accepted production execution
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7ProductionSnapshotObserverR30Final256Canonical

open V7CallerCurrentReleaseR30FixedFieldCanonical
open V7CallerCurrentReleaseR30Final256Canonical
open V7CallerCurrentReleaseR26FoldValuesPrefixSemantics
open AspisV7ProductionSnapshotObserverR28AcceptedTail

theorem accepted_production_final256_canonical
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
    (_acceptedTail : AcceptedProductionTail inner chain) :
    CanonicalValues chain.prechallengeDispatch.foldedValues := by
  let dispatch := chain.prechallengeDispatch
  have canonical : CanonicalFinal256 dispatch.foldedValues :=
    successful_decode_and_absorb_final256_canonical
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
      (fun current value next success =>
        fixed_reader_next_qm31_canonical current next value success)
      dispatch.transcriptBeforeFinal dispatch.transcriptAfterFinalValues
      dispatch.fieldsAfterRelation dispatch.fieldsAfterFinal
      dispatch.foldedValues dispatch.foldedValuesRun
  intro index indexBound
  exact canonical index (by simpa [Array.length_eq] using indexBound)

#print axioms accepted_production_final256_canonical

end V7ProductionSnapshotObserverR30Final256Canonical
