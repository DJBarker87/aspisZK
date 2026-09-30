import V7CallerCurrentReleaseR30InitialFoldOrigin

/-!
# Current initial fold reaches the literal post-prechallenge helper

This module retains the source-bound initial arity-four fold together with
the literal successful post-prechallenge call from the same accepted circle
terminal.  It closes the provenance gap between the six circle components
and the accumulator consumed by the accepted relation tail.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30InitialPrechallengeDispatch

open V7CallerCurrentReleaseR26AcceptedOnefoldPrefix
open V7CallerCurrentReleaseR26AcceptedOuterLoop
open V7CallerCurrentReleaseR26AcceptedCircleOrigin
open V7CallerCurrentReleaseR26AcceptedCircleExhausted
open V7CallerCurrentReleaseR30InitialFoldOrigin

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

private theorem initial_alpha_read_exact
    (sampledAlpha alpha : field.QM31) (values : Array field.QM31 4#usize)
    (updateRun : Array.update (Array.repeat 4#usize field.QM31.ZERO)
      0#usize sampledAlpha = ok values)
    (readRun : Array.index_usize values 0#usize = ok alpha) :
    alpha = sampledAlpha := by
  simp [Array.update, Array.index_usize] at updateRun readRun
  subst values
  simpa using readRun.symm

/-- Exact values passed from the accepted circle terminal to the existing
post-prechallenge verifier helper. -/
structure AcceptedInitialPrechallengeDispatch
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
    {circle : AcceptedCircleLoopDispatch outer}
    (origin : AcceptedCircleBodyOrigin circle) : Type where
  acceptedQueryTranscript : transcript.Transcript
  traceAfterFinal : Trace
  runningClaim : field.QM31
  weights : sumcheck.WeightAccumulator
  alpha : Array field.QM31 4#usize
  initialFold : AcceptedInitialFold origin
  initialFoldAlphaRead : Array.index_usize alpha 0#usize = ok initialFold.alpha
  initialFoldWeightsExact : weights = initialFold.weights
  foldedValues : Array field.QM31 256#usize
  transcriptBeforeFinal : transcript.Transcript
  transcriptAfterFinalValues : transcript.Transcript
  relationFields : Array (Array field.QM31 6#usize) 4#usize
  fieldsAfterRelation : Fields
  fieldsAfterFinal : Fields
  relationFieldsRun :
    v6_transcript.decode_compact_relation_fields fieldsInst
        origin.state.2.2.1 =
      ok (.Ok relationFields, fieldsAfterRelation)
  foldedValuesRun :
    v6_transcript.decode_and_absorb_final256 fieldsInst transcriptBeforeFinal
        fieldsAfterRelation =
      ok (.Ok foldedValues, transcriptAfterFinalValues, fieldsAfterFinal)
  queries : Array Std.U32 16#usize
  compactCounter : Std.U8
  frontierNodes : Std.Usize
  transcriptStateAfterQueries : Array Std.U8 32#usize
  prechallengeSnapshot : Option Snapshot
  traceAfterPrechallenge : Trace
  success :
    v6_transcript.finish_onefold_relation_after_prechallenge queryFoldInst
      traceInst acceptedQueryTranscript c1Frontier c2Frontier
      frontierNodeBytes queryBatchLabels true exposeFinal256 queryFold
      traceAfterFinal outer.gamma outer.gammaPowers outer.dPower runningClaim
      weights alpha foldedValues relationFields selector semanticPoint
      outer.kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries prechallengeSnapshot =
        ok (.Ok (verified, returnedSnapshot), traceAfterPrechallenge)

/-- The exact accepted circle body dispatches to one successful literal
post-prechallenge helper call. -/
theorem AcceptedCircleBodyOrigin.exposesInitialPrechallengeDispatch
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
    {circle : AcceptedCircleLoopDispatch outer}
    (origin : AcceptedCircleBodyOrigin circle) :
    Nonempty (AcceptedInitialPrechallengeDispatch origin) := by
  obtain ⟨iterNext, iteratorExhausted⟩ :=
    V7CallerCurrentReleaseR26AcceptedCircleExhausted.AcceptedCircleBodyOrigin.iteratorExhausted
      origin
  have run := origin.bodyRun
  unfold v6_transcript.finish_onefold_relation_loop0_loop0.body at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨iteratorPair, iteratorRun, run⟩ := run
  rw [iteratorExhausted] at iteratorRun
  have iteratorPairExact : iteratorPair = (none, iterNext) := by
    simpa using iteratorRun.symm
  subst iteratorPair
  simp only at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨traceCirclePair, _, run⟩ := run
  rcases traceCirclePair with ⟨_, traceAfterCircle⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨relationPair, relationRun, run⟩ := run
  rcases relationPair with ⟨relationResult, fieldsAfterRelation⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨relationFlow, relationBranch, run⟩ := run
  cases relationFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
  | Continue relationFields =>
      have relationExact := branch_eq_ok_of_continue relationResult
        relationFields relationBranch
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨traceRelationPair, _, run⟩ := run
      rcases traceRelationPair with ⟨_, traceAfterRelation⟩
      rw [bind_eq_ok_iff] at run
      obtain ⟨firstEncoded, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨firstPolynomial, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨transcriptAfterPolynomial, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨foldNonce, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨foldBits, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨foldCheckPair, _, run⟩ := run
      rcases foldCheckPair with ⟨foldCheckResult, transcriptAfterFoldWork⟩
      rw [bind_eq_ok_iff] at run
      obtain ⟨foldCheckFlow, _, run⟩ := run
      cases foldCheckFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
      | Continue _foldUnit =>
          simp only [↓reduceIte] at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaChallengePair, alphaChallengePairRun, run⟩ := run
          rcases alphaChallengePair with
            ⟨alphaChallengeResult, transcriptAfterAlpha⟩
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaSwapped, alphaSwappedRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaMapped, alphaMappedRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaFlow, alphaFlowRun, run⟩ := run
          cases alphaFlow with
          | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at run
          | Continue alphaZero =>
              have alphaMappedExact := branch_eq_ok_of_continue alphaMapped
                alphaZero alphaFlowRun
              have alphaSwappedExact : alphaSwapped =
                  (transcriptAfterAlpha, alphaChallengeResult) :=
                Result.ok.inj alphaSwappedRun.symm
              subst alphaSwapped
              have alphaChallengeExact : alphaChallengeResult = .Ok alphaZero := by
                rw [alphaMappedExact] at alphaMappedRun
                cases alphaChallengeResult with
                | Ok actual =>
                    have actualExact : actual = alphaZero := by
                      simpa [core.result.Result.map_err] using alphaMappedRun
                    subst actual
                    rfl
                | Err error =>
                    simp [core.result.Result.map_err,
                      v6_transcript.finish_onefold_relation.closure_7.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once]
                      at alphaMappedRun
              have sampleRun :
                  transcript.Transcript.impl.challenge_qm31_bound
                      transcriptAfterFoldWork transcript.V7_ALPHA_ZERO_BIND_ID =
                    ok (.Ok alphaZero, transcriptAfterAlpha) := by
                rw [alphaChallengeExact] at alphaChallengePairRun
                exact alphaChallengePairRun
              rw [bind_eq_ok_iff] at run
              obtain ⟨alpha, alphaUpdateRun, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨alphaZeroRead, alphaZeroReadRun, run⟩ := run
              have alphaExact := initial_alpha_read_exact alphaZero
                alphaZeroRead alpha alphaUpdateRun alphaZeroReadRun
              rw [bind_eq_ok_iff] at run
              obtain ⟨runningClaim, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨weights, foldRun, run⟩ := run
              let initialFold : AcceptedInitialFold origin := ⟨alphaZeroRead,
                alphaZero, transcriptAfterFoldWork, transcriptAfterAlpha,
                sampleRun, alphaExact, weights, foldRun⟩
              rw [bind_eq_ok_iff] at run
              obtain ⟨traceRoundPair, _, run⟩ := run
              rcases traceRoundPair with ⟨_, traceAfterRoundZero⟩
              rw [bind_eq_ok_iff] at run
              obtain ⟨finalPair, finalPairRun, run⟩ := run
              rcases finalPair with
                ⟨finalResult, transcriptAfterFinalValues, fieldsAfterFinal⟩
              rw [bind_eq_ok_iff] at run
              obtain ⟨finalFlow, finalBranch, run⟩ := run
              cases finalFlow with
              | Break residual =>
                  cases residual with
                  | Ok impossible => nomatch impossible
                  | Err error =>
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at run
              | Continue foldedValues =>
                  have finalExact := branch_eq_ok_of_continue finalResult
                    foldedValues finalBranch
                  rw [bind_eq_ok_iff] at run
                  obtain ⟨finishResult, _, run⟩ := run
                  rw [bind_eq_ok_iff] at run
                  obtain ⟨finishFlow, _, run⟩ := run
                  cases finishFlow with
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
                  | Continue _finishUnit =>
                      rw [bind_eq_ok_iff] at run
                      obtain ⟨traceFinalPair, _, run⟩ := run
                      rcases traceFinalPair with ⟨_, traceAfterFinal⟩
                      rw [bind_eq_ok_iff] at run
                      obtain ⟨finalNonce, _, run⟩ := run
                      rw [bind_eq_ok_iff] at run
                      obtain ⟨finalBits, _, run⟩ := run
                      rw [bind_eq_ok_iff] at run
                      obtain ⟨finalCheckPair, _, run⟩ := run
                      rcases finalCheckPair with
                        ⟨finalCheckResult, transcriptBeforeQueries⟩
                      rw [bind_eq_ok_iff] at run
                      obtain ⟨finalCheckFlow, _, run⟩ := run
                      cases finalCheckFlow with
                      | Break residual =>
                          cases residual with
                          | Ok impossible => nomatch impossible
                          | Err error =>
                              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                core.convert.FromSame.from] at run
                      | Continue _finalUnit =>
                          rw [bind_eq_ok_iff] at run
                          obtain ⟨queryResult, queryRun, run⟩ := run
                          rw [bind_eq_ok_iff] at run
                          obtain ⟨queryFlow, _, run⟩ := run
                          cases queryFlow with
                          | Break residual =>
                              cases residual with
                              | Ok impossible => nomatch impossible
                              | Err error =>
                                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                    core.convert.FromSame.from] at run
                          | Continue queryValues =>
                              rcases queryValues with ⟨queries, compactCounter,
                                frontierNodes, transcriptStateAfterQueries,
                                acceptedQueryTranscript⟩
                              simp only at run
                              rw [bind_eq_ok_iff] at run
                              obtain ⟨diagnosticState, _, run⟩ := run
                              rw [bind_eq_ok_iff] at run
                              obtain ⟨finalValuesRef, _, run⟩ := run
                              rw [bind_eq_ok_iff] at run
                              obtain ⟨prechallengeSnapshot, _, run⟩ := run
                              rw [bind_eq_ok_iff] at run
                              obtain ⟨prechallengePair, _, run⟩ := run
                              rcases prechallengePair with ⟨_, prechallengeAfter⟩
                              rw [bind_eq_ok_iff] at run
                              obtain ⟨afterPair, afterRun, run⟩ := run
                              rcases afterPair with
                                ⟨afterResult, traceAfterPrechallenge⟩
                              have afterExact :
                                  afterResult = .Ok (verified, returnedSnapshot) := by
                                simpa using run
                              subst afterResult
                              exact ⟨{
                                acceptedQueryTranscript := acceptedQueryTranscript
                                traceAfterFinal := traceAfterFinal
                                runningClaim := runningClaim
                                weights := weights
                                alpha := alpha
                                initialFold := initialFold
                                initialFoldAlphaRead := by
                                  simpa [initialFold] using alphaZeroReadRun
                                initialFoldWeightsExact := by rfl
                                foldedValues := foldedValues
                                transcriptBeforeFinal := transcriptAfterAlpha
                                transcriptAfterFinalValues :=
                                  transcriptAfterFinalValues
                                relationFields := relationFields
                                fieldsAfterRelation := fieldsAfterRelation
                                fieldsAfterFinal := fieldsAfterFinal
                                relationFieldsRun := by
                                  rw [relationExact] at relationRun
                                  exact relationRun
                                foldedValuesRun := by
                                  rw [finalExact] at finalPairRun
                                  exact finalPairRun
                                queries := queries
                                compactCounter := compactCounter
                                frontierNodes := frontierNodes
                                transcriptStateAfterQueries :=
                                  transcriptStateAfterQueries
                                prechallengeSnapshot := prechallengeSnapshot
                                traceAfterPrechallenge :=
                                  traceAfterPrechallenge
                                success := afterRun }⟩

#print axioms AcceptedCircleBodyOrigin.exposesInitialPrechallengeDispatch

end V7CallerCurrentReleaseR30InitialPrechallengeDispatch
