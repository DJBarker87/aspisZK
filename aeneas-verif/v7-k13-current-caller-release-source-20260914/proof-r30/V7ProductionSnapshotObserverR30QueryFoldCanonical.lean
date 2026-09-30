import V7ProductionCallbacksR30CoordinatesCanonical
import V7ProductionSnapshotObserverR30CurrentTailCanonical

/-!
# Canonical production query-fold line in the accepted relation tail

The accepted tail now retains the literal observer callback invocation that
produced its authenticated query batch.  This file connects that invocation to
the callback coordinate certificate.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV7ProductionSnapshotObserverR30QueryFoldCanonical

open V7ProductionCallbacksR30CoordinatesCanonical
open AspisV7ProductionSnapshotObserverR28SourceBridge
open AspisV7ProductionSnapshotObserverR28ToR26Prechallenge
open AspisV7ProductionSnapshotObserverR30InitialFoldTail
open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge
open V7CallerCurrentReleaseR30OuterAccumulator
open V7CallerCurrentReleaseR30CircleAccumulator
open V7CallerCurrentReleaseR30InitialPrechallengeDispatch

/-- The authenticated line in a current accepted tail was returned by the
literal observer query-fold closure, and every one of its 16 coordinates is
canonical. -/
theorem accepted_current_fold_tail_line_x_canonical
    {hash : HashFn} {wire : Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement (hash, wire) () true transcript (some snapshot)}
    {chain : AcceptedInnerPrechallengeChain inner}
    {prepared : AcceptedPreparedAccumulator chain.outer}
    {accumulator : AcceptedCircleAccumulator prepared}
    {dispatch : AcceptedInitialPrechallengeDispatch accumulator.origin}
    (current : AcceptedCurrentFoldTail dispatch) :
    LineCanonical current.tail.authenticatedQueries.line_x := by
  exact successful_production_observer_query_fold_line_canonical
    hash wire current.tail.queryFoldView current.tail.authenticatedQueries
    current.tail.queryFoldRun

#print axioms accepted_current_fold_tail_line_x_canonical

end AspisV7ProductionSnapshotObserverR30QueryFoldCanonical
