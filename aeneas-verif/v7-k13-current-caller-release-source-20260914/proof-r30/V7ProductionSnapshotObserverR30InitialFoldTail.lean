import V7ProductionSnapshotObserverR30InitialFoldSemantics
import V7ProductionSnapshotObserverR28AcceptedTail

/-!
# Current initial fold and accepted relation tail share one production chain

This retains the semantic initial six-component fold and the shifted query
insertion / relation-tail witness from the exact same accepted production
execution.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace AspisV7ProductionSnapshotObserverR30InitialFoldTail

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ProductionSnapshotObserverR28
open AspisV7ProductionSnapshotObserverR28SourceBridge
open AspisV7ProductionSnapshotObserverR28ToR26Prechallenge
open AspisV7ProductionSnapshotObserverR28AcceptedTail
open AspisV7ProductionSnapshotObserverR30InitialFoldSemantics
open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge
open V7CallerCurrentReleaseR26AcceptedOnefoldPrefix
open V7CallerCurrentReleaseR26AcceptedPrechallengeComposition
open V7CallerCurrentReleaseR26AcceptedTailComposition
open V7CallerCurrentReleaseR30OuterAccumulator
open V7CallerCurrentReleaseR30CircleAccumulator
open V7CallerCurrentReleaseR30InitialPrechallengeDispatch
open V7CallerCurrentReleaseR30InitialFoldSixSemantics

abbrev RawQM31 := field.QM31
abbrev Snapshot := v6_transcript.V6QueryBatchPrechallengeSnapshot

/-- The accepted shifted query insertion and relation-tail source trace fed by
the exact post-initial-fold dispatch, rather than by a separately chosen
historical tail witness. -/
structure AcceptedCurrentFoldTail
    {hash : HashFn} {wire : Wire}
    {context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement} {queryFold : QueryFold}
    {transcript : Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement queryFold () true transcript (some snapshot)}
    {chain : AcceptedInnerPrechallengeChain inner}
    {prepared : AcceptedPreparedAccumulator chain.outer}
    {accumulator : AcceptedCircleAccumulator prepared}
    (dispatch : AcceptedInitialPrechallengeDispatch accumulator.origin) : Type where
  tail : V7CallerCurrentReleaseR26AcceptedTailDispatch.AcceptedShiftedTailDispatch
    queryFoldInst queryFold traceInst chain.outer.gamma dispatch.relationFields 0#u8
    inner.semanticPoint chain.outer.kappa dispatch.queries dispatch.compactCounter
    dispatch.frontierNodes dispatch.transcriptStateAfterQueries
    dispatch.prechallengeSnapshot dispatch.alpha dispatch.foldedValues
    dispatch.weights dispatch.runningClaim transcript (some snapshot)
    dispatch.traceAfterPrechallenge
  source : AcceptedTailSourceTrace chain.outer.gamma dispatch.relationFields 0#u8
    inner.semanticPoint chain.outer.kappa dispatch.queries dispatch.compactCounter
    dispatch.frontierNodes dispatch.transcriptStateAfterQueries
    dispatch.prechallengeSnapshot tail.queryBatchChallenge tail.authenticatedQueries
    tail.transcriptAfterClaim tail.traceAfterClaim tail.runningClaimAfter
    tail.weightsAfter dispatch.alpha dispatch.foldedValues transcript
    (some snapshot) dispatch.traceAfterPrechallenge
  snapshotExact : dispatch.prechallengeSnapshot = some snapshot

def ReachesCurrentInitialFoldAndTail
    (hash : HashFn) (wire : Wire)
    (context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) (queryFold : QueryFold)
    (transcript : Transcript)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot) :
    Prop :=
  Nonempty (Σ inner : AcceptedInnerDispatch terminalInst queryFoldInst
      prechallengeInst hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow statement queryFold () true transcript
      (some snapshot),
    Σ chain : AcceptedInnerPrechallengeChain inner,
    Σ prepared : AcceptedPreparedAccumulator chain.outer,
    Σ accumulator : AcceptedCircleAccumulator prepared,
    Σ dispatch : AcceptedInitialPrechallengeDispatch accumulator.origin,
    Σ trace : V7CallerCurrentReleaseR26WeightFoldLoopTrace.FirstDeferredFoldTrace
      accumulator.origin.state.2.2.2.2 dispatch.initialFold.alpha
      dispatch.initialFold.weights,
    Σ _semantics : InitialFoldSixSemantics accumulator.origin.state.2.2.2.2
      dispatch.initialFold.alpha dispatch.initialFold.weights trace
      prepared.mScale0 prepared.mScale1 prepared.mScale2 prepared.mPoint0
      prepared.mPoint1 prepared.mPoint2 prepared.rowGroups prepared.groupMasks
      (alloc.vec.Vec.new field.QM31) accumulator.step0.scale
      accumulator.step1.scale accumulator.step0.factors accumulator.step1.factors,
    AcceptedCurrentFoldTail dispatch)

theorem reaches_r26_prechallenge_reaches_current_initial_fold_and_tail
    (hash : HashFn) (wire : Wire)
    (context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) (queryFold : QueryFold)
    (transcript : Transcript)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot)
    (reaches : ReachesR26Prechallenge hash wire context hidingContext
      inactiveRowGroups inactiveGroupMasks checkPow statement queryFold
      transcript snapshot) :
    ReachesCurrentInitialFoldAndTail hash wire context hidingContext
      inactiveRowGroups inactiveGroupMasks checkPow statement queryFold
      transcript snapshot := by
  obtain ⟨inner, chain, prepared, accumulator, dispatch, trace, semantics⟩ :=
    Classical.choice
      (reaches_r26_prechallenge_reaches_current_initial_fold_semantics hash wire
        context hidingContext inactiveRowGroups inactiveGroupMasks checkPow
        statement queryFold transcript snapshot reaches)
  obtain ⟨snapshotReturned, tail⟩ :=
    accepted_after_prechallenge_returns_supplied_snapshot queryFoldInst traceInst
      dispatch.acceptedQueryTranscript wire.c1_frontier wire.c2_frontier
      v7_merkle208.V7_MERKLE_DIGEST_BYTES
      (V7CallerCurrentReleaseR26.transcript.label.V7_QUERY_BATCH_CHALLENGE,
        V7CallerCurrentReleaseR26.transcript.label.V7_QUERY_BATCH_CLAIM)
      false queryFold dispatch.traceAfterFinal chain.outer.gamma
      chain.outer.gammaPowers chain.outer.dPower dispatch.runningClaim
      dispatch.weights dispatch.alpha dispatch.foldedValues dispatch.relationFields
      0#u8 inner.semanticPoint chain.outer.kappa dispatch.queries
      dispatch.compactCounter dispatch.frontierNodes
      dispatch.transcriptStateAfterQueries dispatch.prechallengeSnapshot
      transcript (some snapshot) dispatch.traceAfterPrechallenge dispatch.success
  rcases tail with ⟨tail⟩
  obtain ⟨source⟩ := accepted_relation_loop_exposes_source_trace queryFoldInst
    traceInst tail.transcriptAfterClaim tail.traceAfterClaim chain.outer.gamma
    tail.runningClaimAfter tail.weightsAfter dispatch.alpha dispatch.foldedValues
    dispatch.relationFields 0#u8 inner.semanticPoint chain.outer.kappa
    dispatch.queries dispatch.compactCounter dispatch.frontierNodes
    dispatch.transcriptStateAfterQueries dispatch.prechallengeSnapshot
    tail.queryBatchChallenge tail.authenticatedQueries transcript (some snapshot)
    dispatch.traceAfterPrechallenge tail.tailSuccess
  exact ⟨⟨inner, chain, prepared, accumulator, dispatch, trace, semantics,
    { tail := tail, source := source, snapshotExact := snapshotReturned.symm }⟩⟩

#print axioms reaches_r26_prechallenge_reaches_current_initial_fold_and_tail

end AspisV7ProductionSnapshotObserverR30InitialFoldTail
