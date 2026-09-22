import V7CallerCurrentReleaseR24.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseR24TailSnapshotTransport

open V7CallerCurrentReleaseR24

abbrev QM31 := field.QM31
abbrev Snapshot := v6_transcript.V6QueryBatchPrechallengeSnapshot

/-- The terminal branch of the translated production relation tail returns the
same prechallenge snapshot it was given. This isolates the final source step
from the preceding parser/query checks without assuming that any branch is
successful. -/
theorem terminal_body_preserves_prechallenge_snapshot
  {QueryFold DeriveQueries Trace Fields Prechallenge : Type}
  (queryFoldInst : core.ops.function.FnOnce QueryFold v6_transcript.V6QueryBatchView
    (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch v6_onefold.V6WireError))
  (deriveQueriesInst : core.ops.function.FnOnce DeriveQueries transcript.Transcript
    (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
      (Array Std.U8 32#usize) × transcript.Transcript) v6_transcript.V6TranscriptError))
  (traceInst : core.ops.function.FnMut Trace v6_transcript.V6RelationDiagnosticPhase Unit)
  (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
  (prechallengeInst : core.ops.function.FnMut Prechallenge
    v6_transcript.V6QueryBatchPrechallengeView Unit)
  (selector : Std.U8) (semanticPoint : Array QM31 10#usize) (gamma kappa : QM31)
  (relationFields : Array (Array QM31 6#usize) 4#usize) (queries : Array Std.U32 16#usize)
  (compactCounter : Std.U8) (frontierNodes : Std.Usize)
  (transcriptStateAfterQueries : Array Std.U8 32#usize)
  (snapshot : Option Snapshot) (queryBatchChallenge : QM31)
  (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
  (iter iter1 : core.ops.range.Range Std.Usize) (transcript : transcript.Transcript)
  (trace trace1 : Trace) (runningClaim : QM31) (weights : sumcheck.WeightAccumulator)
  (alpha : Array QM31 4#usize) (foldedValues : Array QM31 256#usize)
  (slice : Slice QM31) (terminalDot : QM31)
  (hNext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (none, iter1))
  (hSlice : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice QM31)) foldedValues
      { «end» := 4#usize } = ok slice)
  (hDot : sumcheck.WeightAccumulator.impl.dot weights slice = ok terminalDot)
  (hTerminal : core.cmp.PartialEq.ne.trait_default field.QM31.Insts.CoreCmpPartialEqQM31
      terminalDot runningClaim = ok false)
  (hTrace : traceInst.call_mut trace v6_transcript.V6RelationDiagnosticPhase.Terminal =
      ok ((), trace1))
  (queryIter : core.array.iter.IntoIter QM31 16#usize)
  (hIntoIter : Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
      authenticatedQueries.values = ok queryIter)
  (foldedQuerySum : QM31)
  (hFold : core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
      (BuiltinFnMut (QM31 × QM31) QM31) queryIter field.QM31.ZERO
      (fun p => field.QM31.add p.1 p.2) = ok foldedQuerySum) :
  ∃ verified,
    v6_transcript.finish_onefold_relation_loop0_loop0_loop0.body
        queryFoldInst deriveQueriesInst traceInst fieldsInst prechallengeInst
        selector semanticPoint gamma kappa relationFields queries compactCounter frontierNodes
        transcriptStateAfterQueries snapshot queryBatchChallenge authenticatedQueries iter transcript
        trace runningClaim weights alpha foldedValues =
      ok (done (transcript, trace1, runningClaim, weights,
        core.result.Result.Ok (verified, snapshot))) := by
  simp only [v6_transcript.finish_onefold_relation_loop0_loop0_loop0.body]
  rw [hNext]
  simp only [bind_tc_ok]
  rw [hSlice]
  simp only [bind_tc_ok]
  rw [hDot]
  simp only [bind_tc_ok]
  rw [hTerminal]
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
  rw [hTrace]
  simp only [bind_tc_ok]
  rw [hIntoIter]
  simp only [bind_tc_ok]
  rw [hFold]
  simp only [bind_tc_ok]
  refine ⟨⟨gamma, kappa, alpha, queries, selector, compactCounter, frontierNodes,
    semanticPoint, queryBatchChallenge, foldedQuerySum, transcriptStateAfterQueries⟩, rfl⟩

#print axioms terminal_body_preserves_prechallenge_snapshot

end V7CallerCurrentReleaseR24TailSnapshotTransport
