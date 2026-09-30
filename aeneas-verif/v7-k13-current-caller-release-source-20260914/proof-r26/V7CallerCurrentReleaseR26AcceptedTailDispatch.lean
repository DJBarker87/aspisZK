import V7CallerCurrentReleaseR26QueryBatchInsertion

/-!
# Accepted shifted query insertion feeds the current relation tail

This file inverts the successful enclosing post-prechallenge helper only as
far as the named relation loop.  It proves that the shifted query insertion
trace and the accepted tail invocation belong to the same translated source
execution.  The fixed three-round tail is inverted separately.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedTailDispatch

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev Snapshot := v6_transcript.V6QueryBatchPrechallengeSnapshot

/-- The exact shifted insertion result passed to the relation loop by one
successful execution of `finish_onefold_relation_after_prechallenge`. -/
structure AcceptedShiftedTailDispatch
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (queryFold : QueryFold)
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (gamma : RawQM31)
    (relationFields : Array (Array RawQM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array RawQM31 10#usize)
    (kappa : RawQM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option Snapshot) (alpha : Array RawQM31 4#usize)
    (foldedValues : Array RawQM31 256#usize)
    (weights : RawWeights) (runningClaim : RawQM31)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option Snapshot) (traceOut : Trace) : Type where
  queryBatchChallenge : RawQM31
  /-- The literal nonzero transcript sample that produced the scale used by
  the shifted query insertion.  Retaining this equation lets downstream
  canonicality proofs stay attached to the production execution. -/
  queryBatchChallengeRun :
    ∃ transcriptAbsorbed transcriptAfterChallenge,
      transcript.Transcript.impl.challenge_nonzero_qm31 transcriptAbsorbed =
        ok (.Ok queryBatchChallenge, transcriptAfterChallenge)
  /-- The successful callback invocation which produced the exact authenticated
  batch consumed by this tail.  Keeping the literal view and equation binds
  representation facts about callback output to the accepted source path. -/
  queryFoldView : v6_transcript.V6QueryBatchView
  authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch
  queryFoldRun : queryFoldInst.call_once queryFold queryFoldView =
    ok (.Ok authenticatedQueries)
  claimIncrement : RawQM31
  weightsAfter : RawWeights
  runningClaimAfter : RawQM31
  insertion :
    V7CallerCurrentReleaseR26QueryBatchInsertion.AcceptedQueryBatchInsertionTrace
      weights runningClaim queries authenticatedQueries queryBatchChallenge
      claimIncrement weightsAfter runningClaimAfter
  transcriptAfterClaim : transcript.Transcript
  traceAfterClaim : Trace
  tailSuccess :
    v6_transcript.finish_onefold_relation_after_prechallenge_loop queryFoldInst
      traceInst { start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS }
      transcriptAfterClaim traceAfterClaim gamma runningClaimAfter weightsAfter
      alpha foldedValues relationFields selector semanticPoint kappa queries
      compactCounter frontierNodes transcriptStateAfterQueries snapshot
      queryBatchChallenge authenticatedQueries =
        ok (core.result.Result.Ok (verified, returnedSnapshot), traceOut)

/-- Successful Tag-73 dispatch joins the literal shifted query insertion to
the exact relation-loop call that returned the accepted output. -/
theorem accepted_shifted_dispatch_feeds_tail
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
    (gamma : RawQM31)
    (gammaPowers : state_only_spend_query.StateOnlySpendQueryPowers)
    (dPower runningClaim : RawQM31) (weights : RawWeights)
    (alpha : Array RawQM31 4#usize)
    (foldedValues : Array RawQM31 256#usize)
    (relationFields : Array (Array RawQM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array RawQM31 10#usize)
    (kappa : RawQM31) (queries : Array Std.U32 16#usize)
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
    Nonempty (AcceptedShiftedTailDispatch queryFoldInst queryFold traceInst gamma
      relationFields selector semanticPoint kappa queries compactCounter
      frontierNodes transcriptStateAfterQueries snapshot alpha foldedValues
      weights runningClaim verified returnedSnapshot traceOut) := by
  unfold v6_transcript.finish_onefold_relation_after_prechallenge at success
  simp only [↓reduceIte, lift, Array.to_slice_mut, Bind.bind,
    Aeneas.Std.bind] at success
  by_cases hnode : frontierNodeBytes = 0#usize
  · simp [hnode] at success
  · simp [hnode] at success
    cases hc1rem : Slice.len c1Frontier % frontierNodeBytes <;>
      simp [hc1rem] at success
    rename_i c1Remainder
    by_cases hc1zero : c1Remainder.val = 0
    · simp [hc1zero] at success
      cases hc2rem : Slice.len c2Frontier % frontierNodeBytes <;>
        simp [hc2rem] at success
      rename_i c2Remainder
      by_cases hc2zero : c2Remainder.val = 0
      · simp [hc2zero] at success
        cases hc1nodes : Slice.len c1Frontier / frontierNodeBytes <;>
          simp [hc1nodes] at success
        rename_i c1Nodes
        cases hc2nodes : Slice.len c2Frontier / frontierNodeBytes <;>
          simp [hc2nodes] at success
        rename_i c2Nodes
        by_cases hc1count : c1Nodes.val = frontierNodes.val
        · simp [hc1count] at success
          by_cases hc2count : c2Nodes.val = frontierNodes.val
          · simp [hc2count] at success
            rcases queryBatchLabels with ⟨challengeLabel, claimLabel⟩
            cases habsorb : transcript.Transcript.impl.absorb transcript0
                challengeLabel (Array.to_slice (Std.Array.empty Std.U8)) <;>
              simp [habsorb] at success
            rename_i transcriptAbsorbed
            cases hchallenge : transcript.Transcript.impl.challenge_nonzero_qm31
                transcriptAbsorbed <;> simp [hchallenge] at success
            rename_i challengePair
            rcases challengePair with ⟨challengeResult, transcriptAfterChallenge⟩
            cases challengeResult with
            | Err error =>
                simp [core.result.Result.map_err,
                  v6_transcript.finish_onefold_relation_after_prechallenge.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at success
            | Ok queryBatchChallenge =>
                simp only [core.result.Result.map_err,
                  core.result.Result.Insts.CoreOpsTry.branch] at success
                cases htraceQueries : traceInst.call_mut trace0
                    v6_transcript.V6RelationDiagnosticPhase.Queries <;>
                  simp [htraceQueries] at success
                rename_i traceQueriesPair
                rcases traceQueriesPair with ⟨traceQueriesUnit, traceQueries⟩
                cases halphaZero : Array.index_usize alpha 0#usize <;>
                  simp [halphaZero] at success
                rename_i alphaZero
                by_cases hexpose : exposeFinal256 = true
                all_goals
                  first
                  | have hexposeTrue : exposeFinal256 = true := hexpose
                    simp [hexposeTrue] at success
                    cases href : Box.Insts.CoreConvertAsRef.as_ref Global
                        foldedValues <;> simp [href] at success
                    rename_i final256
                    generalize hfinal :
                      (some final256 : Option (Array RawQM31 256#usize)) =
                        exposedFinal at success
                  | have hexposeFalse : ¬ exposeFinal256 = true := hexpose
                    simp [hexposeFalse] at success
                    generalize hfinal :
                      (none : Option (Array RawQM31 256#usize)) =
                        exposedFinal at success
                  cases hqueryFold : queryFoldInst.call_once queryFold
                      { gamma := gamma, gamma_powers := gammaPowers,
                        d_power := dPower, alpha0 := alphaZero,
                        final256_coefficients := exposedFinal,
                        queries := queries, selector := selector,
                        compact_counter := compactCounter,
                        frontier_nodes := frontierNodes } <;>
                    simp [hqueryFold] at success
                  rename_i queryFoldResult
                  cases queryFoldResult with
                  | Err error =>
                      simp [BuiltinFnOnce, v6_transcript.V6TranscriptError.Wire,
                        core.result.Result.map_err,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at success
                  | Ok authenticatedQueries =>
                      simp only [core.result.Result.map_err,
                        core.result.Result.Insts.CoreOpsTry.branch] at success
                      cases hinsertion :
                          v6_query_batch.add_v7_final256_query_batch_shifted
                            weights runningClaim queries authenticatedQueries
                            queryBatchChallenge <;> simp [hinsertion] at success
                      rename_i insertionResult
                      rcases insertionResult with
                        ⟨claimResult, weightsAfter, runningClaimAfter⟩
                      cases claimResult with
                      | Err error =>
                          simp [core.result.Result.map_err,
                            v6_transcript.finish_onefold_relation_after_prechallenge.closure_1.Insts.CoreOpsFunctionFnOnceTupleV6QueryBatchErrorV6TranscriptError.call_once,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from] at success
                      | Ok claimIncrement =>
                          simp only [core.result.Result.map_err,
                            core.result.Result.Insts.CoreOpsTry.branch] at success
                          cases hwrite : field.QM31.write_le_bytes claimIncrement
                              (Array.to_slice (Array.repeat 16#usize 0#u8)) <;>
                            simp [hwrite] at success
                          rename_i writtenBytes
                          cases habsorbClaim : transcript.Transcript.impl.absorb
                              transcriptAfterChallenge claimLabel
                              (Array.to_slice ((Array.repeat 16#usize 0#u8).from_slice
                                writtenBytes)) <;>
                            simp [habsorbClaim] at success
                          rename_i transcriptAfterClaim
                          cases htraceBatch : traceInst.call_mut traceQueries
                              v6_transcript.V6RelationDiagnosticPhase.QueryBatch <;>
                            simp [htraceBatch] at success
                          rename_i traceBatchPair
                          rcases traceBatchPair with ⟨traceBatchUnit, traceAfterClaim⟩
                          have hinsertionTrace :=
                            V7CallerCurrentReleaseR26QueryBatchInsertion.accepted_query_batch_exposes_exact_insertion
                              weights runningClaim queries authenticatedQueries
                              queryBatchChallenge claimIncrement weightsAfter
                              runningClaimAfter hinsertion
                          rcases hinsertionTrace with ⟨insertion⟩
                          exact ⟨{
                            queryBatchChallenge := queryBatchChallenge
                            queryBatchChallengeRun := ⟨transcriptAbsorbed,
                              transcriptAfterChallenge, hchallenge⟩
                            queryFoldView :=
                              { gamma := gamma, gamma_powers := gammaPowers,
                                d_power := dPower, alpha0 := alphaZero,
                                final256_coefficients := exposedFinal,
                                queries := queries, selector := selector,
                                compact_counter := compactCounter,
                                frontier_nodes := frontierNodes }
                            queryFoldRun := hqueryFold
                            authenticatedQueries := authenticatedQueries
                            claimIncrement := claimIncrement
                            weightsAfter := weightsAfter
                            runningClaimAfter := runningClaimAfter
                            insertion := insertion
                            transcriptAfterClaim := transcriptAfterClaim
                            traceAfterClaim := traceAfterClaim
                            tailSuccess := success }⟩
          · simp [hc2count] at success
        · simp [hc1count] at success
      · simp [hc2zero] at success
    · simp [hc1zero] at success

#print axioms accepted_shifted_dispatch_feeds_tail

end V7CallerCurrentReleaseR26AcceptedTailDispatch
