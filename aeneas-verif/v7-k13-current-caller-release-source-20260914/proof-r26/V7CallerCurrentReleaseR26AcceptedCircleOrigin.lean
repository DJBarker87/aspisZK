import V7CallerCurrentReleaseR26AcceptedOuterLoop

/-!
# Accepted circle loop has a literal successful body origin

This is the partial-fixpoint boundary for the nested circle-sample loop.  It
records a concrete generated body state whose `done` edge produced the
accepted verifier value.  The body is inverted separately to expose the
literal post-prechallenge call.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedCircleOrigin

open V7CallerCurrentReleaseR26AcceptedOnefoldPrefix
open V7CallerCurrentReleaseR26AcceptedOuterLoop
open V7CallerCurrentReleaseR26AcceptedTailSnapshot

abbrev Snapshot := v6_transcript.V6QueryBatchPrechallengeSnapshot
abbrev CircleState (Fields : Type) :=
  core.ops.range.Range Std.I32 × transcript.Transcript × Fields ×
    field.QM31 × sumcheck.WeightAccumulator

/-- One literal generated circle-loop body state returned the accepted value. -/
structure AcceptedCircleBodyOrigin
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
    {outer : AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot}
    (circle : AcceptedCircleLoopDispatch outer) : Type where
  state : CircleState Fields
  bodyRun :
    v6_transcript.finish_onefold_relation_loop0_loop0.body queryFoldInst
      deriveQueriesInst traceInst fieldsInst prechallengeInst workNonces
      c1Frontier c2Frontier workBits selector frontierNodeBytes
      queryBatchLabels true exposeFinal256 deriveQueries checkPow semanticPoint
      queryFold prechallenge captureSnapshot circle.traceAfterPrepared
      outer.gamma outer.kappa outer.dPower outer.gammaPowers state.1
      state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2 =
        ok (done (some (.Ok (verified, returnedSnapshot))))

/-- Partial correctness of the nested generated fixpoint exposes its exact
accepted `done` body equation. -/
theorem AcceptedCircleLoopDispatch.exposesBodyOrigin
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
    {outer : AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot}
    (circle : AcceptedCircleLoopDispatch outer) :
    Nonempty (AcceptedCircleBodyOrigin circle) := by
  have loopSuccess := circle.innerLoopSuccess
  unfold v6_transcript.finish_onefold_relation_loop0_loop0 at loopSuccess
  let body := fun (state : CircleState Fields) =>
    v6_transcript.finish_onefold_relation_loop0_loop0.body queryFoldInst
      deriveQueriesInst traceInst fieldsInst prechallengeInst workNonces
      c1Frontier c2Frontier workBits selector frontierNodeBytes
      queryBatchLabels true exposeFinal256 deriveQueries checkPow semanticPoint
      queryFold prechallenge captureSnapshot circle.traceAfterPrepared
      outer.gamma outer.kappa outer.dPower outer.gammaPowers state.1
      state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2
  have origin := loop_ok_has_done_origin_eq body
    ({ start := 0#i32, «end» := 2#i32 }, outer.transcriptAfterPrefix,
      outer.fieldsAfterPrefix, outer.runningClaim,
      circle.weightsAfterPrepared)
    (some (.Ok (verified, returnedSnapshot))) loopSuccess
  obtain ⟨state, bodyRun⟩ := origin
  exact ⟨{ state := state, bodyRun := bodyRun }⟩

#print axioms AcceptedCircleLoopDispatch.exposesBodyOrigin

end V7CallerCurrentReleaseR26AcceptedCircleOrigin
