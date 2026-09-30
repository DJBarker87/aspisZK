import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Accepted current post-prechallenge composition

The enclosing helper's successful shifted insertion feeds the accepted
relation loop, whose successful result returns the exact supplied capture.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedPrechallengeComposition

abbrev Snapshot := v6_transcript.V6QueryBatchPrechallengeSnapshot

/-- A successful Tag-73 post-prechallenge helper returns the exact snapshot
option with which it was invoked.  The witness also retains the shifted query
insertion and literal accepted-loop execution from the same call. -/
theorem accepted_after_prechallenge_returns_supplied_snapshot
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (transcript0 : transcript.Transcript)
    (c1Frontier c2Frontier : Slice Std.U8)
    (frontierNodeBytes : Std.Usize) (queryBatchLabels : Std.U8 × Std.U8)
    (exposeFinal256 : Bool) (queryFold : QueryFold) (trace0 : Trace)
    (gamma : field.QM31)
    (gammaPowers : state_only_spend_query.StateOnlySpendQueryPowers)
    (dPower runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option Snapshot)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option Snapshot) (traceOut : Trace)
    (success :
      v6_transcript.finish_onefold_relation_after_prechallenge queryFoldInst
        traceInst transcript0 c1Frontier c2Frontier frontierNodeBytes
        queryBatchLabels true exposeFinal256 queryFold trace0 gamma gammaPowers
        dPower runningClaim weights alpha foldedValues relationFields selector
        semanticPoint kappa queries compactCounter frontierNodes
        transcriptStateAfterQueries snapshot =
          ok (core.result.Result.Ok (verified, returnedSnapshot), traceOut)) :
    returnedSnapshot = snapshot ∧
      Nonempty
        (V7CallerCurrentReleaseR26AcceptedTailDispatch.AcceptedShiftedTailDispatch
          queryFoldInst queryFold traceInst gamma relationFields selector semanticPoint
          kappa queries compactCounter frontierNodes
          transcriptStateAfterQueries snapshot alpha foldedValues weights
          runningClaim verified returnedSnapshot traceOut) := by
  obtain ⟨dispatch⟩ :=
    V7CallerCurrentReleaseR26AcceptedTailDispatch.accepted_shifted_dispatch_feeds_tail
      queryFoldInst traceInst transcript0 c1Frontier c2Frontier
      frontierNodeBytes queryBatchLabels exposeFinal256 queryFold trace0 gamma
      gammaPowers dPower runningClaim weights alpha foldedValues relationFields
      selector semanticPoint kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries snapshot verified returnedSnapshot traceOut
      success
  exact ⟨
    V7CallerCurrentReleaseR26AcceptedTailSnapshot.V7CallerCurrentReleaseR26AcceptedTailDispatch.AcceptedShiftedTailDispatch.returnedSnapshotExact
      dispatch,
    ⟨dispatch⟩⟩

/-- Specialization for an enabled concrete capture: acceptance transports the
captured `some snapshot` value through the complete post-prechallenge helper. -/
theorem accepted_after_prechallenge_returns_captured_snapshot
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (transcript0 : transcript.Transcript)
    (c1Frontier c2Frontier : Slice Std.U8)
    (frontierNodeBytes : Std.Usize) (queryBatchLabels : Std.U8 × Std.U8)
    (exposeFinal256 : Bool) (queryFold : QueryFold) (trace0 : Trace)
    (gamma : field.QM31)
    (gammaPowers : state_only_spend_query.StateOnlySpendQueryPowers)
    (dPower runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Snapshot)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option Snapshot) (traceOut : Trace)
    (success :
      v6_transcript.finish_onefold_relation_after_prechallenge queryFoldInst
        traceInst transcript0 c1Frontier c2Frontier frontierNodeBytes
        queryBatchLabels true exposeFinal256 queryFold trace0 gamma gammaPowers
        dPower runningClaim weights alpha foldedValues relationFields selector
        semanticPoint kappa queries compactCounter frontierNodes
        transcriptStateAfterQueries (some snapshot) =
          ok (core.result.Result.Ok (verified, returnedSnapshot), traceOut)) :
    returnedSnapshot = some snapshot :=
  (accepted_after_prechallenge_returns_supplied_snapshot queryFoldInst traceInst
    transcript0 c1Frontier c2Frontier frontierNodeBytes queryBatchLabels
    exposeFinal256 queryFold trace0 gamma gammaPowers dPower runningClaim
    weights alpha foldedValues relationFields selector semanticPoint kappa
    queries compactCounter frontierNodes transcriptStateAfterQueries
    (some snapshot) verified returnedSnapshot traceOut success).1

#print axioms accepted_after_prechallenge_returns_supplied_snapshot
#print axioms accepted_after_prechallenge_returns_captured_snapshot

end V7CallerCurrentReleaseR26AcceptedPrechallengeComposition
