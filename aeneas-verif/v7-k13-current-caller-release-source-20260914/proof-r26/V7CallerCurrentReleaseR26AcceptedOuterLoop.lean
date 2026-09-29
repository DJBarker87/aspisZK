import V7CallerCurrentReleaseR26AcceptedOnefoldPrefix

/-!
# Successful point-claim loop reaches the circle-sample loop

The outer generated loop adds the three point multilinears and the prepared
inactive-row weights.  This module uses partial-fixpoint inversion to show
that an accepted outer-loop result contains the exact successful invocation
of the nested circle-sample loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedOuterLoop

open V7CallerCurrentReleaseR26AcceptedOnefoldPrefix
open V7CallerCurrentReleaseR26AcceptedTailSnapshot

abbrev Snapshot := v6_transcript.V6QueryBatchPrechallengeSnapshot

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem branch_eq_ok_of_continue {Value Error : Type}
    (result : core.result.Result Value Error) (value : Value)
    (success : core.result.Result.Insts.CoreOpsTry.branch result =
      .ok (.Continue value)) :
    result = .Ok value := by
  cases result with
  | Ok actual =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch] using success
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at success

/-- Exact nested-loop invocation recovered from an accepted outer loop. -/
structure AcceptedCircleLoopDispatch
    {QueryFold DeriveQueries Trace Fields Prechallenge : Type}
    {queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError)}
    {deriveQueriesInst : core.ops.function.FnOnce DeriveQueries
      transcript.Transcript
      (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
        (Array Std.U8 32#usize) × transcript.Transcript)
        v6_transcript.V6TranscriptError)}
    {traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit}
    {fieldsInst : v6_onefold.V6FixedFieldStream Fields}
    {prechallengeInst : core.ops.function.FnMut Prechallenge
      v6_transcript.V6QueryBatchPrechallengeView Unit}
    {transcript0 : transcript.Transcript}
    {workNonces : Array Std.U8 24#usize}
    {c1Frontier c2Frontier : Slice Std.U8}
    {workBits : Array Std.U8 3#usize} {selector : Std.U8}
    {frontierNodeBytes : Std.Usize} {queryBatchLabels : Std.U8 × Std.U8}
    {exposeFinal256 : Bool} {deriveQueries : DeriveQueries} {fields0 : Fields}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {semanticPoint : Array field.QM31 10#usize}
    {pointClaims : Array (Array field.QM31 29#usize) 3#usize}
    {queryFold : QueryFold} {prechallenge : Prechallenge}
    {captureSnapshot : Bool} {trace0 : Trace}
    {verified : v6_transcript.V6VerifiedTranscript}
    {returnedSnapshot : Option Snapshot}
    (outer : AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot) : Type where
  weightsAfterPrepared : sumcheck.WeightAccumulator
  traceAfterPrepared : Trace
  innerLoopSuccess :
    v6_transcript.finish_onefold_relation_loop0_loop0 queryFoldInst
      deriveQueriesInst traceInst fieldsInst prechallengeInst
      { start := 0#i32, «end» := 2#i32 } outer.transcriptAfterPrefix
      workNonces c1Frontier c2Frontier workBits selector frontierNodeBytes
      queryBatchLabels true exposeFinal256 deriveQueries
      outer.fieldsAfterPrefix checkPow semanticPoint queryFold prechallenge
      captureSnapshot traceAfterPrepared outer.gamma outer.kappa outer.dPower
      outer.gammaPowers outer.runningClaim weightsAfterPrepared =
        ok (some (.Ok (verified, returnedSnapshot)))

/-- The accepted outer fixpoint can only return this accepted value through
its exhausted-iterator branch and the exact nested circle loop call. -/
theorem AcceptedOnefoldLoopDispatch.exposesCircleLoop
    {QueryFold DeriveQueries Trace Fields Prechallenge : Type}
    {queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError)}
    {deriveQueriesInst : core.ops.function.FnOnce DeriveQueries
      transcript.Transcript
      (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
        (Array Std.U8 32#usize) × transcript.Transcript)
        v6_transcript.V6TranscriptError)}
    {traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit}
    {fieldsInst : v6_onefold.V6FixedFieldStream Fields}
    {prechallengeInst : core.ops.function.FnMut Prechallenge
      v6_transcript.V6QueryBatchPrechallengeView Unit}
    {transcript0 : transcript.Transcript}
    {workNonces : Array Std.U8 24#usize}
    {c1Frontier c2Frontier : Slice Std.U8}
    {workBits : Array Std.U8 3#usize} {selector : Std.U8}
    {frontierNodeBytes : Std.Usize} {queryBatchLabels : Std.U8 × Std.U8}
    {exposeFinal256 : Bool} {deriveQueries : DeriveQueries} {fields0 : Fields}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {semanticPoint : Array field.QM31 10#usize}
    {pointClaims : Array (Array field.QM31 29#usize) 3#usize}
    {queryFold : QueryFold} {prechallenge : Prechallenge}
    {captureSnapshot : Bool} {trace0 : Trace}
    {verified : v6_transcript.V6VerifiedTranscript}
    {returnedSnapshot : Option Snapshot}
    (outer : AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot) :
    Nonempty (AcceptedCircleLoopDispatch outer) := by
  have loopSuccess := outer.loopSuccess
  unfold v6_transcript.finish_onefold_relation_loop0 at loopSuccess
  let body := fun (state : core.ops.range.Range Std.Usize ×
      sumcheck.WeightAccumulator) =>
    v6_transcript.finish_onefold_relation_loop0.body queryFoldInst
      deriveQueriesInst traceInst fieldsInst prechallengeInst
      outer.transcriptAfterPrefix workNonces c1Frontier c2Frontier workBits
      selector frontierNodeBytes queryBatchLabels true exposeFinal256
      deriveQueries outer.fieldsAfterPrefix inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint queryFold prechallenge
      captureSnapshot outer.traceAfterStart outer.gamma outer.kappa
      outer.points outer.pointScales outer.dPower outer.gammaPowers
      outer.runningClaim state.1 state.2
  have origin := loop_ok_has_done_origin_eq body
    ({ start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS },
      outer.weights)
    (some (.Ok (verified, returnedSnapshot))) loopSuccess
  obtain ⟨state, bodyRun⟩ := origin
  unfold body at bodyRun
  unfold v6_transcript.finish_onefold_relation_loop0.body at bodyRun
  rw [bind_eq_ok_iff] at bodyRun
  obtain ⟨iteratorPair, _, bodyRun⟩ := bodyRun
  rcases iteratorPair with ⟨option, iterNext⟩
  cases option with
  | none =>
      simp only at bodyRun
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨preparedPair, _, bodyRun⟩ := bodyRun
      rcases preparedPair with ⟨preparedResult, weightsAfterPrepared⟩
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨preparedMapped, _, bodyRun⟩ := bodyRun
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨preparedFlow, preparedBranch, bodyRun⟩ := bodyRun
      cases preparedFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at bodyRun
      | Continue preparedUnit =>
          have preparedExact := branch_eq_ok_of_continue preparedMapped
            preparedUnit preparedBranch
          simp only at bodyRun
          rw [bind_eq_ok_iff] at bodyRun
          obtain ⟨tracePair, _, bodyRun⟩ := bodyRun
          rcases tracePair with ⟨_, traceAfterPrepared⟩
          rw [bind_eq_ok_iff] at bodyRun
          obtain ⟨pendingReturn, innerRun, bodyRun⟩ := bodyRun
          cases pendingReturn with
          | none => simp at bodyRun
          | some innerResult =>
              have innerExact :
                  innerResult = .Ok (verified, returnedSnapshot) := by
                simpa using bodyRun
              subst innerResult
              exact ⟨{
                weightsAfterPrepared := weightsAfterPrepared
                traceAfterPrepared := traceAfterPrepared
                innerLoopSuccess := innerRun }⟩
  | some row =>
      simp only at bodyRun
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨scale, _, bodyRun⟩ := bodyRun
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨point, _, bodyRun⟩ := bodyRun
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨pointSlice, _, bodyRun⟩ := bodyRun
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨pointVec, _, bodyRun⟩ := bodyRun
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨multilinearPair, _, bodyRun⟩ := bodyRun
      rcases multilinearPair with ⟨multilinearResult, weightsNext⟩
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨multilinearMapped, _, bodyRun⟩ := bodyRun
      rw [bind_eq_ok_iff] at bodyRun
      obtain ⟨multilinearFlow, _, bodyRun⟩ := bodyRun
      cases multilinearFlow with
      | Continue _unit => simp at bodyRun
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at bodyRun

#print axioms AcceptedOnefoldLoopDispatch.exposesCircleLoop

end V7CallerCurrentReleaseR26AcceptedOuterLoop
