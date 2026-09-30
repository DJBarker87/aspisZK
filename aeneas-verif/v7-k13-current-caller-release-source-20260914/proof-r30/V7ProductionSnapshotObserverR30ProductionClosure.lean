import V7ProductionSnapshotObserverR30TerminalClosure

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV7ProductionSnapshotObserverR30ProductionClosure
open V7ProductionSnapshotObserverR28
open AspisV7ProductionSnapshotObserverR30TerminalClosure
open AspisV7ProductionSnapshotObserverR28SourceBridge
open AspisV7ProductionSnapshotObserverR28ToR26Prechallenge
open AspisV7ProductionSnapshotObserverR30InitialFoldTail
open AspisV7ProductionSnapshotObserverR30CurrentTailCanonical
open AspisV7ProductionSnapshotObserverR30QueryFoldCanonical
open AspisV7ProductionSnapshotObserverR30RunningCanonical
open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26AcceptedTerminalEndToEnd
open V7CallerCurrentReleaseR26QueryBatchAppend
open V7CallerCurrentReleaseR26QueryScaleExactLoop
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedFold
open V7CallerCurrentReleaseR30OuterAccumulator
open V7CallerCurrentReleaseR30CircleAccumulator
open V7CallerCurrentReleaseR30InitialPrechallengeDispatch
open V7CallerCurrentReleaseR30InitialFoldOrigin
open V7CallerCurrentReleaseR30InitialFoldSixSemantics
open AspisV5FriRelationCandidateBridge

def CurrentTerminalIdentity
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
    (current : AcceptedCurrentFoldTail dispatch)
    (trace : V7CallerCurrentReleaseR26WeightFoldLoopTrace.FirstDeferredFoldTrace
      accumulator.origin.state.2.2.2.2 dispatch.initialFold.alpha dispatch.initialFold.weights)
      (semantics : InitialFoldSixSemantics accumulator.origin.state.2.2.2.2
        dispatch.initialFold.alpha dispatch.initialFold.weights trace
        prepared.mScale0 prepared.mScale1 prepared.mScale2 prepared.mPoint0
        prepared.mPoint1 prepared.mPoint2 prepared.rowGroups prepared.groupMasks
        (alloc.vec.Vec.new field.QM31) accumulator.step0.scale accumulator.step1.scale
        accumulator.step0.factors accumulator.step1.factors) : Prop :=
      ∃ (lineScales : alloc.vec.Vec field.QM31) (lineXs : alloc.vec.Vec field.M31),
        lineScales.val = current.tail.insertion.scales.val ∧
        lineXs.val = current.tail.authenticatedQueries.line_x.val ∧
        GeneratedCanonicalQM31 current.source.roundThree.runningClaimAfter ∧
        sourceQm31ToModel (generatedQm31ToExact current.source.roundThree.runningClaimAfter) =
          candidateClaim
            (threeRoundWeightVector current.source.roundOne.alphaOne
              current.source.roundTwo.alphaTwo current.source.roundThree.alphaThree
              semantics.source.mScale0Out semantics.source.mScale1Out semantics.source.mScale2Out
              semantics.source.mPoint0Out semantics.source.mPoint1Out semantics.source.mPoint2Out
              dispatch.initialFold.alpha semantics.source.tScale0Out semantics.source.tScale1Out
              semantics.source.tFactors0Out semantics.source.tFactors1Out lineScales lineXs)
            (threeRoundValueVector dispatch.foldedValues current.source.roundOne.alphaOne
              current.source.roundTwo.alphaTwo current.source.roundThree.alphaThree)

def ReachesTerminalClosure
    (hash : HashFn) (wire : Wire)
    (context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement)
    (transcript : Transcript)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot) :
    Prop :=
  Nonempty (Σ inner : AcceptedInnerDispatch terminalInst queryFoldInst
      prechallengeInst hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow statement (hash, wire) () true transcript
      (some snapshot),
    Σ chain : AcceptedInnerPrechallengeChain inner,
    Σ prepared : AcceptedPreparedAccumulator chain.outer,
    Σ accumulator : AcceptedCircleAccumulator prepared,
    Σ dispatch : AcceptedInitialPrechallengeDispatch accumulator.origin,
    Σ trace : V7CallerCurrentReleaseR26WeightFoldLoopTrace.FirstDeferredFoldTrace
      accumulator.origin.state.2.2.2.2 dispatch.initialFold.alpha
      dispatch.initialFold.weights,
    Σ semantics : InitialFoldSixSemantics accumulator.origin.state.2.2.2.2
      dispatch.initialFold.alpha dispatch.initialFold.weights trace
      prepared.mScale0 prepared.mScale1 prepared.mScale2 prepared.mPoint0
      prepared.mPoint1 prepared.mPoint2 prepared.rowGroups prepared.groupMasks
      (alloc.vec.Vec.new field.QM31) accumulator.step0.scale
      accumulator.step1.scale accumulator.step0.factors accumulator.step1.factors,
    Σ current : AcceptedCurrentFoldTail dispatch,
      PLift (CurrentTerminalIdentity current trace semantics))
private theorem copied_rows_released
    (rows : Array Std.U8 64#usize)
    (run : aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_v3
      = ok rows) : rows.val = releasedRowGroups64.val := by
  unfold aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_v3 at run
  exact (congrArg Subtype.val (Result.ok.inj run).symm).trans (by rfl)

private theorem copied_masks_released
    (masks : Slice Std.U16)
    (run : aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_v3
      = ok masks) : masks.val = releasedMasks.val := by
  unfold aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_v3 at run
  exact (congrArg Subtype.val (Result.ok.inj run).symm).trans (by rfl)

theorem production_snapshot_observer_acceptance_reaches_terminal_closure
    (hash : HashFn) (proof : Slice Std.U8)
    (frontierNodes : Std.Usize) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (checkPow : Bool) (verified : v7_verifier.VerifiedV7ReadOnly)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot)
    (accepted :
      v7_verifier.observe_v7_read_only_with_statement_digest
          hash proof frontierNodes programId releaseBinding attemptId statement
          statementDigest checkPow = .ok (.Ok (verified, snapshot))) :
    ∃ (wire : Wire) (programBytes attemptBytes : Array Std.U8 32#usize)
      (hidingContext : HidingContext)
      (inactiveRowGroups : Array Std.U8 64#usize)
      (inactiveGroupMasks : Slice Std.U16) (transcript : Transcript),
      aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
          proof frontierNodes = .ok (.Ok wire) ∧
      solana_pubkey.Pubkey.to_bytes programId = .ok programBytes ∧
      solana_pubkey.Pubkey.to_bytes attemptId = .ok attemptBytes ∧
      aspis_core.state_only_hiding.StateOnlyHidingContext.atomic_spend_v3
          statementDigest attemptBytes = .ok hidingContext ∧
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_v3 =
        .ok inactiveRowGroups ∧
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_v3 =
        .ok inactiveGroupMasks ∧
      ReachesTerminalClosure hash wire
        { program_id := programBytes
          release_binding := releaseBinding
          statement_digest := statementDigest
          attempt_id := attemptBytes }
        hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
        transcript snapshot ∧
      verified =
        { transcript := transcript,
          folded_query_sum := transcript.folded_query_sum } := by
  rcases production_snapshot_observer_acceptance_reaches_r26_prechallenge
    hash proof frontierNodes programId releaseBinding attemptId statement statementDigest
    checkPow verified snapshot accepted with
    ⟨wire, programBytes, attemptBytes, hidingContext, inactiveRowGroups,
      inactiveGroupMasks, transcript, hparse, hprogram, hattempt, hhiding,
      hrows, hmasks, reaches, hverified⟩
  obtain ⟨inner, chain, prepared, accumulator, dispatch, trace, semantics, current⟩ :=
    Classical.choice
      (reaches_r26_prechallenge_reaches_current_initial_fold_and_tail hash wire
        { program_id := programBytes, release_binding := releaseBinding,
          statement_digest := statementDigest, attempt_id := attemptBytes }
        hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
        (hash, wire) transcript snapshot reaches)
  have identity : CurrentTerminalIdentity current trace semantics :=
    accepted_current_fold_tail_terminal_corresponds current trace semantics
      (copied_rows_released inactiveRowGroups hrows)
      (copied_masks_released inactiveGroupMasks hmasks)
  refine ⟨wire, programBytes, attemptBytes, hidingContext, inactiveRowGroups,
    inactiveGroupMasks, transcript, hparse, hprogram, hattempt, hhiding,
    hrows, hmasks, ?_, hverified⟩
  exact ⟨⟨inner, chain, prepared, accumulator, dispatch, trace, semantics, current,
    ⟨identity⟩⟩⟩

#print axioms production_snapshot_observer_acceptance_reaches_terminal_closure
end AspisV7ProductionSnapshotObserverR30ProductionClosure
