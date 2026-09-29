import V7CallerCurrentReleaseR26AcceptedCircleOrigin

/-!
# Accepted circle body is the exhausted-iterator branch

Every sampled-circle branch either continues the loop or returns a verifier
error.  Therefore the literal body equation that returned an accepted value
must be the exhausted-iterator branch.  This fact lets the next module invert
only the terminal body and expose `finish_onefold_relation_after_prechallenge`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedCircleExhausted

open V7CallerCurrentReleaseR26AcceptedOnefoldPrefix
open V7CallerCurrentReleaseR26AcceptedOuterLoop
open V7CallerCurrentReleaseR26AcceptedCircleOrigin

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- The body state that produced acceptance has no remaining circle sample. -/
theorem AcceptedCircleBodyOrigin.iteratorExhausted
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
    {returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot}
    {outer : AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot}
    {circle : AcceptedCircleLoopDispatch outer}
    (origin : AcceptedCircleBodyOrigin circle) :
    ∃ iterNext,
      core.iter.range.IteratorRange.next core.iter.range.StepI32 origin.state.1 =
        ok (none, iterNext) := by
  have run := origin.bodyRun
  unfold v6_transcript.finish_onefold_relation_loop0_loop0.body at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨iteratorPair, iteratorRun, run⟩ := run
  rcases iteratorPair with ⟨option, iterNext⟩
  cases option with
  | none => exact ⟨iterNext, iteratorRun⟩
  | some sample =>
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨circlePair, _, run⟩ := run
      rcases circlePair with ⟨circleResult, transcript1⟩
      rw [bind_eq_ok_iff] at run
      obtain ⟨circleMapped, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨circleFlow, _, run⟩ := run
      cases circleFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
      | Continue circlePoint =>
          rw [bind_eq_ok_iff] at run
          obtain ⟨fieldPair, _, run⟩ := run
          rcases fieldPair with ⟨fieldResult, fields1⟩
          rw [bind_eq_ok_iff] at run
          obtain ⟨fieldFlow, _, run⟩ := run
          cases fieldFlow with
          | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error =>
                  cases converted :
                      v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from
                        error <;>
                    simp [converted,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                      at run
          | Continue circleValue =>
              simp only at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨sampleByte, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨record2, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨slicePair, _, run⟩ := run
              rcases slicePair with ⟨recordSlice, recordBack⟩
              rw [bind_eq_ok_iff] at run
              obtain ⟨writtenSlice, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨recordSlice2, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨transcript2, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨alphaPair, _, run⟩ := run
              rcases alphaPair with ⟨alphaResult, transcript3⟩
              rw [bind_eq_ok_iff] at run
              obtain ⟨alphaMapped, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨alphaFlow, _, run⟩ := run
              cases alphaFlow with
              | Break residual =>
                  cases residual with
                  | Ok impossible => nomatch impossible
                  | Err error =>
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at run
              | Continue alpha =>
                  rw [bind_eq_ok_iff] at run
                  obtain ⟨tensorPair, _, run⟩ := run
                  rcases tensorPair with ⟨tensorResult, weights1⟩
                  rw [bind_eq_ok_iff] at run
                  obtain ⟨tensorMapped, _, run⟩ := run
                  rw [bind_eq_ok_iff] at run
                  obtain ⟨tensorFlow, _, run⟩ := run
                  cases tensorFlow with
                  | Break residual =>
                      cases residual with
                      | Ok impossible => nomatch impossible
                      | Err error =>
                          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from] at run
                  | Continue _unit =>
                      rw [bind_eq_ok_iff] at run
                      obtain ⟨product, _, run⟩ := run
                      rw [bind_eq_ok_iff] at run
                      obtain ⟨runningClaim, _, run⟩ := run
                      simp at run

#print axioms AcceptedCircleBodyOrigin.iteratorExhausted

end V7CallerCurrentReleaseR26AcceptedCircleExhausted
