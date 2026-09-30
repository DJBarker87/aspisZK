import V7CallerCurrentReleaseR26AcceptedInnerDispatch

/-!
# Successful one-fold relation reaches its generated outer loop

This module inverts the non-loop prefix of the translated
`finish_onefold_relation` function.  It keeps the exact successful invocation
of the generated point-claim/weight loop, so later modules can invert that
loop and recover the literal post-prechallenge call.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedOnefoldPrefix

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

/-- Values passed by a successful non-loop prefix to the exact generated
outer loop. -/
structure AcceptedOnefoldLoopDispatch
    {QueryFold DeriveQueries Trace Fields Prechallenge : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (deriveQueriesInst : core.ops.function.FnOnce DeriveQueries
      transcript.Transcript
      (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
        (Array Std.U8 32#usize) × transcript.Transcript)
        v6_transcript.V6TranscriptError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (prechallengeInst : core.ops.function.FnMut Prechallenge
      v6_transcript.V6QueryBatchPrechallengeView Unit)
    (transcript0 : transcript.Transcript)
    (workNonces : Array Std.U8 24#usize)
    (c1Frontier c2Frontier : Slice Std.U8)
    (workBits : Array Std.U8 3#usize) (selector : Std.U8)
    (frontierNodeBytes : Std.Usize) (queryBatchLabels : Std.U8 × Std.U8)
    (exposeFinal256 : Bool)
    (deriveQueries : DeriveQueries) (fields0 : Fields)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (semanticPoint : Array field.QM31 10#usize)
    (pointClaims : Array (Array field.QM31 29#usize) 3#usize)
    (queryFold : QueryFold) (prechallenge : Prechallenge)
    (captureSnapshot : Bool) (trace0 : Trace)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option Snapshot) : Type where
  transcriptAfterPrefix : transcript.Transcript
  fieldsAfterPrefix : Fields
  traceAfterStart : Trace
  gamma : field.QM31
  kappa : field.QM31
  transcriptBeforeKappa : transcript.Transcript
  kappaSquared : field.QM31
  inactiveClaim : field.QM31
  points : Array (Array field.QM31 10#usize) 3#usize
  pointScales : Array field.QM31 3#usize
  combinedClaims : Array field.QM31 3#usize
  claimContribution : field.QM31
  dPower : field.QM31
  gammaPowers : state_only_spend_query.StateOnlySpendQueryPowers
  runningClaim : field.QM31
  weights : sumcheck.WeightAccumulator
  kappaRun :
    transcript.Transcript.impl.challenge_nonzero_qm31
        transcriptBeforeKappa =
      ok (.Ok kappa, transcriptAfterPrefix)
  pointsRun :
    v6_transcript.v6_statement_points semanticPoint = ok points
  kappaSquaredRun :
    field.QM31.square kappa = ok kappaSquared
  pointScalesExact :
    pointScales =
      Array.make 3#usize [field.QM31.ONE, kappa, kappaSquared]
  weightsRun :
    sumcheck.WeightAccumulator.impl.empty 10#u32 = ok weights
  inactiveClaimRun :
    fieldsInst.next_qm31 fields0 =
      ok (.Ok inactiveClaim, fieldsAfterPrefix)
  claimContributionRun :
    field.qm31_sum_products3 pointScales combinedClaims =
      ok claimContribution
  runningClaimRun :
    field.QM31.add inactiveClaim claimContribution = ok runningClaim
  loopSuccess :
    v6_transcript.finish_onefold_relation_loop0 queryFoldInst
      deriveQueriesInst traceInst fieldsInst prechallengeInst
      { start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }
      transcriptAfterPrefix workNonces c1Frontier c2Frontier workBits selector
      frontierNodeBytes queryBatchLabels true exposeFinal256
      deriveQueries fieldsAfterPrefix inactiveRowGroups inactiveGroupMasks
      checkPow semanticPoint queryFold prechallenge captureSnapshot
      traceAfterStart gamma kappa points pointScales dPower gammaPowers
      runningClaim weights = ok (some (.Ok (verified, returnedSnapshot)))

/-- Any accepted translated one-fold relation call reaches one exact
successful invocation of its generated outer loop. -/
theorem accepted_onefold_exposes_outer_loop
    {QueryFold DeriveQueries Trace Fields Prechallenge : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (deriveQueriesInst : core.ops.function.FnOnce DeriveQueries
      transcript.Transcript
      (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
        (Array Std.U8 32#usize) × transcript.Transcript)
        v6_transcript.V6TranscriptError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (prechallengeInst : core.ops.function.FnMut Prechallenge
      v6_transcript.V6QueryBatchPrechallengeView Unit)
    (transcript0 : transcript.Transcript)
    (workNonces : Array Std.U8 24#usize)
    (c1Frontier c2Frontier : Slice Std.U8)
    (workBits : Array Std.U8 3#usize) (selector : Std.U8)
    (frontierNodeBytes : Std.Usize) (queryBatchLabels : Std.U8 × Std.U8)
    (exposeFinal256 : Bool)
    (deriveQueries : DeriveQueries) (fields0 : Fields)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (semanticPoint : Array field.QM31 10#usize)
    (pointClaims : Array (Array field.QM31 29#usize) 3#usize)
    (queryFold : QueryFold) (prechallenge : Prechallenge)
    (captureSnapshot : Bool) (trace0 : Trace)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option Snapshot)
    (success :
      v6_transcript.finish_onefold_relation queryFoldInst deriveQueriesInst
        traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
        c2Frontier workBits selector frontierNodeBytes queryBatchLabels
        true exposeFinal256 deriveQueries fields0 inactiveRowGroups
        inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
        prechallenge captureSnapshot trace0 =
          ok (.Ok (verified, returnedSnapshot))) :
    Nonempty (AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot) := by
  unfold v6_transcript.finish_onefold_relation at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨tracePair, _, success⟩ := success
  rcases tracePair with ⟨_, traceAfterStart⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨batchNonce, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨batchBits, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨batchCheck, batchCheckRun, success⟩ := success
  rcases batchCheck with ⟨batchResult, transcript1⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨batchFlow, batchBranch, success⟩ := success
  cases batchFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at success
  | Continue batchUnit =>
      have batchExact := branch_eq_ok_of_continue batchResult batchUnit
        batchBranch
      rw [batchExact] at batchCheckRun
      simp only at success
      simp only [↓reduceIte] at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨gammaPair, gammaRun, success⟩ := success
      rcases gammaPair with ⟨gammaResult, transcript2⟩
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨gammaMapped, gammaMapRun, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨gammaMappedResult, gammaMappedRun, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨gammaFlow, gammaBranch, success⟩ := success
      cases gammaFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at success
      | Continue gamma =>
          have gammaExact := branch_eq_ok_of_continue gammaMappedResult gamma
            gammaBranch
          rw [gammaExact] at gammaMappedRun
          simp only at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨fieldPair, fieldRun, success⟩ := success
          rcases fieldPair with ⟨fieldResult, fieldsAfterPrefix⟩
          rw [bind_eq_ok_iff] at success
          obtain ⟨fieldFlow, fieldBranch, success⟩ := success
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
                      at success
          | Continue inactiveClaim =>
              have fieldExact := branch_eq_ok_of_continue fieldResult
                inactiveClaim fieldBranch
              rw [fieldExact] at fieldRun
              simp only at success
              rw [bind_eq_ok_iff] at success
              obtain ⟨slicePair, _, success⟩ := success
              rcases slicePair with ⟨inactiveSlice, inactiveBack⟩
              rw [bind_eq_ok_iff] at success
              obtain ⟨writtenSlice, _, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨inactiveBytes, _, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨transcriptBeforeKappa, _, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨kappaPair, kappaRun, success⟩ := success
              rcases kappaPair with ⟨kappaResult, transcriptAfterPrefix⟩
              simp only at success
              rw [bind_eq_ok_iff] at success
              obtain ⟨kappaMapped, kappaMapRun, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨kappaFlow, kappaBranch, success⟩ := success
              cases kappaFlow with
              | Break residual =>
                  cases residual with
                  | Ok impossible => nomatch impossible
                  | Err error =>
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at success
              | Continue kappa =>
                  have kappaExact := branch_eq_ok_of_continue kappaMapped kappa
                    kappaBranch
                  have kappaResultExact : kappaResult = .Ok kappa := by
                    rw [kappaExact] at kappaMapRun
                    cases kappaResult with
                    | Ok actual =>
                        have actualExact : actual = kappa := by
                          simpa [core.result.Result.map_err] using kappaMapRun
                        subst actual
                        rfl
                    | Err error =>
                        simp [core.result.Result.map_err,
                          v6_transcript.finish_onefold_relation.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once]
                          at kappaMapRun
                  rw [kappaResultExact] at kappaRun
                  simp only at success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨points, pointsRun, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨kappaSquared, kappaSquaredRun, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨claimPowers, _, success⟩ := success
                  rcases claimPowers with
                    ⟨combinedClaims, gammaPowers, dPower⟩
                  let pointScales : Array field.QM31 3#usize :=
                    Array.make 3#usize [field.QM31.ONE, kappa, kappaSquared]
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨claimContribution, claimContributionRun, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨runningClaim, runningClaimRun, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨weights, weightsRun, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨pendingReturn, loopRun, success⟩ := success
                  cases pendingReturn with
                  | none => simp at success
                  | some loopResult =>
                      have loopResultExact :
                          loopResult = .Ok (verified, returnedSnapshot) := by
                        simpa using success
                      subst loopResult
                      exact ⟨{
                        transcriptAfterPrefix := transcriptAfterPrefix
                        fieldsAfterPrefix := fieldsAfterPrefix
                        traceAfterStart := traceAfterStart
                        gamma := gamma
                        kappa := kappa
                        transcriptBeforeKappa := transcriptBeforeKappa
                        kappaSquared := kappaSquared
                        inactiveClaim := inactiveClaim
                        points := points
                        pointScales := pointScales
                        combinedClaims := combinedClaims
                        claimContribution := claimContribution
                        dPower := dPower
                        gammaPowers := gammaPowers
                        runningClaim := runningClaim
                        weights := weights
                        kappaRun := kappaRun
                        pointsRun := pointsRun
                        kappaSquaredRun := kappaSquaredRun
                        pointScalesExact := rfl
                        weightsRun := weightsRun
                        inactiveClaimRun := fieldRun
                        claimContributionRun := claimContributionRun
                        runningClaimRun := runningClaimRun
                        loopSuccess := loopRun }⟩

#print axioms accepted_onefold_exposes_outer_loop

end V7CallerCurrentReleaseR26AcceptedOnefoldPrefix
