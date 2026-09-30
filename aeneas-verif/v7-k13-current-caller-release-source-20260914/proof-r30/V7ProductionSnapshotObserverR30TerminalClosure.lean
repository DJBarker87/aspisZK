import V7ProductionSnapshotObserverR30RunningCanonical
import V7ProductionSnapshotObserverR30QueryFoldCanonical
import V7CallerCurrentReleaseR26QueryBatchAppend

/-! Literal production source closure at the existing R26 terminal relation. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV7ProductionSnapshotObserverR30TerminalClosure
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

theorem accepted_current_fold_tail_terminal_corresponds
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
    ∀ (trace : V7CallerCurrentReleaseR26WeightFoldLoopTrace.FirstDeferredFoldTrace
      accumulator.origin.state.2.2.2.2 dispatch.initialFold.alpha dispatch.initialFold.weights)
      (semantics : InitialFoldSixSemantics accumulator.origin.state.2.2.2.2
        dispatch.initialFold.alpha dispatch.initialFold.weights trace
        prepared.mScale0 prepared.mScale1 prepared.mScale2 prepared.mPoint0
        prepared.mPoint1 prepared.mPoint2 prepared.rowGroups prepared.groupMasks
        (alloc.vec.Vec.new field.QM31) accumulator.step0.scale accumulator.step1.scale
        accumulator.step0.factors accumulator.step1.factors),
      inactiveRowGroups.val = releasedRowGroups64.val →
      inactiveGroupMasks.val = releasedMasks.val →
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
              current.source.roundTwo.alphaTwo current.source.roundThree.alphaThree) := by
  intro trace semantics rowsReleased masksReleased
  have rowGroupsReleased : prepared.rowGroups = releasedRowGroups64 := by
    apply Subtype.ext
    exact prepared.rowGroupsExact.trans rowsReleased
  have groupMasksReleased : prepared.groupMasks = releasedMasks := by
    apply Subtype.ext
    exact prepared.groupMasksExact.trans masksReleased
  have groupExact := semantics.groupExact
  simp only [Prod.mk.injEq] at groupExact
  rcases groupExact with ⟨groupRows, groupMasks, groupAlpha, groupValues⟩
  have beforeComponents := semantics.outputComponents
  simp only [groupRows, groupMasks, groupAlpha, groupValues,
    rowGroupsReleased, groupMasksReleased] at beforeComponents
  have capacity : dispatch.weights.components.val.length < Std.Usize.max := by
    rw [dispatch.initialFoldWeightsExact, beforeComponents]
    change 6 < Std.Usize.max
    scalar_tac
  obtain ⟨lineScales, lineXs, scalesExact, xsExact, logExact, afterComponents⟩ :=
    accepted_insertion_has_exact_append dispatch.weights dispatch.runningClaim
      dispatch.queries current.tail.authenticatedQueries current.tail.queryBatchChallenge
      current.tail.claimIncrement current.tail.weightsAfter current.tail.runningClaimAfter
      capacity current.tail.insertion
  simp only [dispatch.initialFoldWeightsExact, beforeComponents] at afterComponents
  simp only [List.cons_append, List.nil_append] at afterComponents
  have scalePrefix := successful_scale_loop_has_exact_shifted_powers
    current.tail.queryBatchChallenge (generatedQm31ToExact current.tail.queryBatchChallenge)
    current.tail.insertion.preparedRho current.tail.insertion.seed current.tail.insertion.scales
    (accepted_current_fold_tail_query_batch_challenge_canonical current) rfl
    current.tail.insertion.seedSuccess current.tail.insertion.preparedRhoSuccess
    current.tail.insertion.scalesLoopSuccess
  have scalesLength : lineScales.val.length = 16 := by
    rw [scalesExact]
    exact current.tail.insertion.scales.property
  have xsLength : lineXs.val.length = 16 := by
    rw [xsExact]
    exact current.tail.authenticatedQueries.line_x.property
  have scalesCanonical : CanonicalQM31Slice (alloc.vec.Vec.deref lineScales) := by
    intro index bound
    have indexBound : index < 16 := by simpa [alloc.vec.Vec.deref, scalesLength] using bound
    have canonical := scalePrefix.1 index indexBound
    have inBounds : index < current.tail.insertion.scales.val.length := by
      simpa [Array.length_eq] using indexBound
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem inBounds,
      Option.getD_some] at canonical
    simp only [alloc.vec.Vec.deref, scalesExact, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem inBounds, Option.getD_some]
    exact canonical
  have xsCanonical : CanonicalM31Slice (alloc.vec.Vec.deref lineXs) := by
    intro index bound
    have indexBound : index < 16 := by simpa [alloc.vec.Vec.deref, xsLength] using bound
    have canonical := accepted_current_fold_tail_line_x_canonical current index indexBound
    have inBounds : index < current.tail.authenticatedQueries.line_x.val.length := by
      simpa [Array.length_eq] using indexBound
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem inBounds,
      Option.getD_some] at canonical
    simp only [alloc.vec.Vec.deref, xsExact, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem inBounds, Option.getD_some]
    exact canonical
  obtain ⟨rowOne, rowTwo, rowThree⟩ := accepted_current_fold_tail_relation_rows_canonical current
  obtain ⟨alphaOne, alphaTwo, alphaThree⟩ := accepted_current_fold_tail_challenges_canonical current
  obtain ⟨terminalSemantics, terminalCanonical, terminalIdentity, threeRoundIdentity⟩ :=
    accepted_terminal_source_corresponds current.source
      semantics.source.mScale0Out semantics.source.mScale1Out semantics.source.mScale2Out
      semantics.source.mPoint0Out semantics.source.mPoint1Out semantics.source.mPoint2Out
      dispatch.initialFold.alpha (alloc.vec.Vec.new field.QM31)
      semantics.source.tScale0Out semantics.source.tScale1Out
      semantics.source.tFactors0Out semantics.source.tFactors1Out lineScales lineXs
      (accepted_current_fold_tail_running_canonical current)
      (accepted_current_fold_tail_final256_canonical current)
      rowOne rowTwo rowThree alphaOne alphaTwo alphaThree afterComponents
      dispatch.initialFold.alpha_canonical
      semantics.mScale0Canonical semantics.mScale1Canonical semantics.mScale2Canonical
      semantics.mPoint0Canonical semantics.mPoint1Canonical semantics.mPoint2Canonical
      semantics.mPoint0Length semantics.mPoint1Length semantics.mPoint2Length
      semantics.tScale0Canonical semantics.tScale1Canonical
      semantics.tFactors0Canonical semantics.tFactors1Canonical
      semantics.tFactors0Length semantics.tFactors1Length
      scalesLength xsLength scalesCanonical xsCanonical
  exact ⟨lineScales, lineXs, scalesExact, xsExact, terminalCanonical, threeRoundIdentity⟩

#print axioms accepted_current_fold_tail_terminal_corresponds
end AspisV7ProductionSnapshotObserverR30TerminalClosure
