import V7CallerCurrentReleaseR26AcceptedTailSemantics

/-!
# Composed current R26 accepted-tail source trace

This file composes the three fixed-round inversions and the accepted terminal
inversion from one successful execution of the literal generated loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedTailComposition

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26AcceptedTailSemantics

abbrev TailState (Trace : Type) :=
  V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace

/-- The four source steps obtained from one accepted production loop run. -/
structure AcceptedTailSourceTrace
    {Trace : Type}
    (gamma : field.QM31)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (transcript0 : transcript.Transcript) (trace0 : Trace)
    (runningClaim : field.QM31) (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace) : Type where
  afterOne : TailState Trace
  afterTwo : TailState Trace
  afterThree : TailState Trace
  roundOne : RoundOneSourceStep transcript0 runningClaim weights alpha
    foldedValues relationFields afterOne
  roundTwo : RoundTwoSourceStep afterOne.2.1 afterOne.2.2.2.1
    afterOne.2.2.2.2.1 afterOne.2.2.2.2.2.1 afterOne.2.2.2.2.2.2
    relationFields afterTwo
  roundThree : RoundThreeSourceStep afterTwo.2.1 afterTwo.2.2.2.1
    afterTwo.2.2.2.2.1 afterTwo.2.2.2.2.2.1 afterTwo.2.2.2.2.2.2
    relationFields afterThree
  terminal : AcceptedTerminalSourceStep gamma kappa selector semanticPoint
    queries compactCounter frontierNodes transcriptStateAfterQueries snapshot
    queryBatchChallenge authenticatedQueries afterThree.2.2.2.1
    afterThree.2.2.2.2.1 afterThree.2.2.2.2.2.1
    afterThree.2.2.2.2.2.2 verified returnedSnapshot traceOut

/-- One successful literal loop execution exposes all three fixed source
rounds and the accepted terminal comparison in order. -/
theorem accepted_relation_loop_exposes_source_trace
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (transcript0 : transcript.Transcript) (trace0 : Trace)
    (gamma runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace)
    (success :
      v6_transcript.finish_onefold_relation_after_prechallenge_loop
        queryFoldInst traceInst
        { start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS }
        transcript0 trace0 gamma runningClaim weights alpha foldedValues
        relationFields selector semanticPoint kappa queries compactCounter
        frontierNodes transcriptStateAfterQueries snapshot queryBatchChallenge
        authenticatedQueries =
          ok (core.result.Result.Ok (verified, returnedSnapshot), traceOut)) :
    Nonempty (AcceptedTailSourceTrace gamma relationFields selector
      semanticPoint kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries transcript0 trace0 runningClaim weights alpha
      foldedValues verified returnedSnapshot traceOut) := by
  obtain ⟨execution⟩ := accepted_relation_loop_has_three_round_execution
    queryFoldInst traceInst transcript0 trace0 gamma runningClaim weights alpha
    foldedValues relationFields selector semanticPoint kappa queries
    compactCounter frontierNodes transcriptStateAfterQueries snapshot
    queryBatchChallenge authenticatedQueries verified returnedSnapshot
    traceOut success
  obtain ⟨iteratorOne, iteratorTwo, iteratorThree, terminalIterator,
      iteratorTerminal⟩ := execution.iterator_equations queryFoldInst traceInst
    transcript0 trace0 gamma runningClaim weights alpha foldedValues
    relationFields selector semanticPoint kappa queries compactCounter
    frontierNodes transcriptStateAfterQueries snapshot queryBatchChallenge
    authenticatedQueries verified returnedSnapshot traceOut
  obtain ⟨roundOne⟩ := round_one_edge_exposes_source_step queryFoldInst
    traceInst gamma relationFields selector semanticPoint kappa queries
    compactCounter frontierNodes transcriptStateAfterQueries snapshot
    queryBatchChallenge authenticatedQueries transcript0 trace0 runningClaim
    weights alpha foldedValues execution.afterOne iteratorOne
    execution.roundOne
  obtain ⟨roundTwo⟩ := round_two_edge_exposes_source_step queryFoldInst
    traceInst gamma relationFields selector semanticPoint kappa queries
    compactCounter frontierNodes transcriptStateAfterQueries snapshot
    queryBatchChallenge authenticatedQueries execution.afterOne.1
    execution.afterOne.2.1 execution.afterOne.2.2.1
    execution.afterOne.2.2.2.1 execution.afterOne.2.2.2.2.1
    execution.afterOne.2.2.2.2.2.1 execution.afterOne.2.2.2.2.2.2
    execution.afterTwo iteratorTwo execution.roundTwo
  obtain ⟨roundThree⟩ := round_three_edge_exposes_source_step queryFoldInst
    traceInst gamma relationFields selector semanticPoint kappa queries
    compactCounter frontierNodes transcriptStateAfterQueries snapshot
    queryBatchChallenge authenticatedQueries execution.afterTwo.1
    execution.afterTwo.2.1 execution.afterTwo.2.2.1
    execution.afterTwo.2.2.2.1 execution.afterTwo.2.2.2.2.1
    execution.afterTwo.2.2.2.2.2.1 execution.afterTwo.2.2.2.2.2.2
    execution.afterThree iteratorThree execution.roundThree
  obtain ⟨terminal⟩ := terminal_edge_exposes_source_step queryFoldInst
    traceInst gamma relationFields selector semanticPoint kappa queries
    compactCounter frontierNodes transcriptStateAfterQueries snapshot
    queryBatchChallenge authenticatedQueries execution.afterThree.1
    terminalIterator execution.afterThree.2.1 execution.afterThree.2.2.1
    execution.afterThree.2.2.2.1 execution.afterThree.2.2.2.2.1
    execution.afterThree.2.2.2.2.2.1 execution.afterThree.2.2.2.2.2.2
    verified returnedSnapshot traceOut iteratorTerminal execution.terminal
  exact ⟨{
    afterOne := execution.afterOne
    afterTwo := execution.afterTwo
    afterThree := execution.afterThree
    roundOne := roundOne
    roundTwo := roundTwo
    roundThree := roundThree
    terminal := terminal }⟩

end V7CallerCurrentReleaseR26AcceptedTailComposition
