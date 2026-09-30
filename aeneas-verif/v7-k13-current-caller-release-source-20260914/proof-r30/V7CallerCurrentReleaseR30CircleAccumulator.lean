import V7CallerCurrentReleaseR30OuterAccumulator
import V7CallerCurrentReleaseR26AcceptedCircleOrigin
import V7CallerCurrentReleaseR26AcceptedPrechallengeDispatch

/-!
# Exact circle-loop accumulator construction

The generated nested loop samples two secure-circle points, appends one
tensor component for each, and updates the running claim.  This module keeps
that exact six-component state and the terminal body witness that dispatches
to the already verified post-prechallenge tail.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30CircleAccumulator

open V7CallerCurrentReleaseR26AcceptedOnefoldPrefix
open V7CallerCurrentReleaseR26AcceptedOuterLoop
open V7CallerCurrentReleaseR26AcceptedCircleOrigin
open V7CallerCurrentReleaseR26AcceptedPrechallengeDispatch
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR30OuterAccumulator

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator

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

private theorem push_exact {T : Type}
    (values valuesOut : alloc.vec.Vec T) (value : T)
    (run : alloc.vec.Vec.push values value = ok valuesOut) :
    valuesOut.val = values.val ++ [value] := by
  unfold alloc.vec.Vec.push at run
  simp only at run
  split at run
  · simpa [List.concat_eq_append] using
      congrArg Subtype.val (Result.ok.inj run).symm
  · cases run

theorem successful_tensor_append_exact
    (weights weightsAfter : RawWeights) (scale : RawQM31)
    (factors : alloc.vec.Vec RawQM31)
    (run : sumcheck.WeightAccumulator.impl.add_tensor_factors
      weights scale factors = ok (.Ok (), weightsAfter)) :
    weightsAfter.log_len = weights.log_len ∧
      weightsAfter.components.val = weights.components.val ++
        [.Tensor scale factors] := by
  unfold sumcheck.WeightAccumulator.impl.add_tensor_factors at run
  simp only at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨casted, _, run⟩ := run
  split at run
  · cases run
  · rw [bind_eq_ok_iff] at run
    obtain ⟨componentsAfter, pushRun, run⟩ := run
    simp only [Result.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨_, rfl⟩
    exact ⟨rfl, push_exact weights.components componentsAfter
      (.Tensor scale factors) pushRun⟩

/-- A successful circle append exposes the literal factor vector handed to
the common tensor insertion helper. -/
theorem successful_circle_append_exact
    (weights weightsAfter : RawWeights) (scale : RawQM31)
    (point : circle.SecureCirclePoint)
    (run : sumcheck.WeightAccumulator.impl.add_circle_tensor
      weights scale point = ok (.Ok (), weightsAfter)) :
    ∃ factors : alloc.vec.Vec RawQM31,
      sumcheck.WeightAccumulator.impl.add_tensor_factors
          weights scale factors = ok (.Ok (), weightsAfter) ∧
      weightsAfter.log_len = weights.log_len ∧
      weightsAfter.components.val = weights.components.val ++
        [.Tensor scale factors] := by
  unfold sumcheck.WeightAccumulator.impl.add_circle_tensor at run
  split at run
  · cases run
  · rw [bind_eq_ok_iff] at run
    obtain ⟨capacity, _, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨factors1, _, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨factors2, _, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨factors3, _, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨slicePair, _, run⟩ := run
    rcases slicePair with ⟨slice, back⟩
    rw [bind_eq_ok_iff] at run
    obtain ⟨reversed, _, run⟩ := run
    let factors := back reversed
    have tensorRun :
        sumcheck.WeightAccumulator.impl.add_tensor_factors
            weights scale factors = ok (.Ok (), weightsAfter) := by
      simpa [factors] using run
    obtain ⟨logExact, componentsExact⟩ :=
      successful_tensor_append_exact weights weightsAfter scale factors
        tensorRun
    exact ⟨factors, tensorRun, logExact, componentsExact⟩

private theorem rangeNext0End2 :
    core.iter.range.IteratorRange.next core.iter.range.StepI32
        { start := 0#i32, «end» := 2#i32 } =
      ok (some 0#i32, { start := 1#i32, «end» := 2#i32 }) := by
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep,
    core.iter.range.IScalarStep.forward_checked,
    core.cmp.impls.PartialOrdI32.lt]
  split
  · rfl
  · rename_i h
    have bounds := (1#i32).hBounds
    scalar_tac

private theorem rangeNext1End2 :
    core.iter.range.IteratorRange.next core.iter.range.StepI32
        { start := 1#i32, «end» := 2#i32 } =
      ok (some 1#i32, { start := 2#i32, «end» := 2#i32 }) := by
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep,
    core.iter.range.IScalarStep.forward_checked,
    core.cmp.impls.PartialOrdI32.lt]
  split
  · rfl
  · rename_i h
    have bounds := (2#i32).hBounds
    scalar_tac

private theorem rangeDone2 :
    core.iter.range.IteratorRange.next core.iter.range.StepI32
        { start := 2#i32, «end» := 2#i32 } =
      ok (none, { start := 2#i32, «end» := 2#i32 }) := by
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep,
    core.cmp.impls.PartialOrdI32.lt]

/-- All source calls retained from one successful continuing circle-loop
edge. -/
structure AcceptedCircleStep {Fields : Type}
    (fieldsInst : v6_onefold.V6FixedFieldStream Fields)
    (state next : CircleState Fields)
    (iterNext : core.ops.range.Range Std.I32) : Type where
  point : circle.SecureCirclePoint
  transcriptAfterPoint : transcript.Transcript
  pointRun :
    transcript.Transcript.impl.challenge_secure_circle_point state.2.1 =
      ok (.Ok point, transcriptAfterPoint)
  fieldValue : RawQM31
  fieldsAfter : Fields
  fieldRun : fieldsInst.next_qm31 state.2.2.1 =
    ok (.Ok fieldValue, fieldsAfter)
  transcriptAfterAbsorb : transcript.Transcript
  scale : RawQM31
  transcriptAfterScale : transcript.Transcript
  scaleRun :
    transcript.Transcript.impl.challenge_qm31 transcriptAfterAbsorb =
      ok (.Ok scale, transcriptAfterScale)
  factors : alloc.vec.Vec RawQM31
  weightsAfter : RawWeights
  appendRun :
    sumcheck.WeightAccumulator.impl.add_circle_tensor state.2.2.2.2
        scale point = ok (.Ok (), weightsAfter)
  tensorRun :
    sumcheck.WeightAccumulator.impl.add_tensor_factors state.2.2.2.2
        scale factors = ok (.Ok (), weightsAfter)
  product : RawQM31
  runningAfter : RawQM31
  productRun : field.QM31.mul scale fieldValue = ok product
  runningRun : field.QM31.add state.2.2.2.1 product = ok runningAfter
  nextExact : next = (iterNext, transcriptAfterScale, fieldsAfter,
    runningAfter, weightsAfter)
  logLenExact : weightsAfter.log_len = state.2.2.2.2.log_len
  componentsExact : weightsAfter.components.val =
    state.2.2.2.2.components.val ++ [.Tensor scale factors]

/-- The selected accepted two-step circle execution and its exact
six-component terminal accumulator. -/
structure AcceptedCircleAccumulator
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
    {semanticPoint : Array RawQM31 10#usize}
    {pointClaims : Array (Array RawQM31 29#usize) 3#usize}
    {queryFold : QueryFold} {prechallenge : Prechallenge}
    {captureSnapshot : Bool} {trace0 : Trace}
    {verified : v6_transcript.V6VerifiedTranscript}
    {returnedSnapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot}
    {outer : AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot}
    (prepared : AcceptedPreparedAccumulator outer) : Type where
  state1 : CircleState Fields
  state2 : CircleState Fields
  step0 : AcceptedCircleStep fieldsInst
    ({ start := 0#i32, «end» := 2#i32 }, outer.transcriptAfterPrefix,
      outer.fieldsAfterPrefix, outer.runningClaim,
      prepared.circle.weightsAfterPrepared)
    state1 { start := 1#i32, «end» := 2#i32 }
  step1 : AcceptedCircleStep fieldsInst state1 state2
    { start := 2#i32, «end» := 2#i32 }
  origin : AcceptedCircleBodyOrigin prepared.circle
  originStateExact : origin.state = state2
  prechallengeDispatch : AcceptedPrechallengeDispatch origin
  componentsExact : origin.state.2.2.2.2.components.val =
    [.Multilinear prepared.mScale0 prepared.mPoint0,
     .Multilinear prepared.mScale1 prepared.mPoint1,
     .Multilinear prepared.mScale2 prepared.mPoint2,
     .Grouped64x16BinaryDeferred prepared.rowGroups prepared.groupMasks none
       (alloc.vec.Vec.new RawQM31),
     .Tensor step0.scale step0.factors,
     .Tensor step1.scale step1.factors]

theorem AcceptedPreparedAccumulator.exposesCircleAccumulator
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
    {semanticPoint : Array RawQM31 10#usize}
    {pointClaims : Array (Array RawQM31 29#usize) 3#usize}
    {queryFold : QueryFold} {prechallenge : Prechallenge}
    {captureSnapshot : Bool} {trace0 : Trace}
    {verified : v6_transcript.V6VerifiedTranscript}
    {returnedSnapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot}
    {outer : AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot}
    (prepared : AcceptedPreparedAccumulator outer) :
    Nonempty (AcceptedCircleAccumulator prepared) := by
  let body := fun (state : CircleState Fields) =>
    v6_transcript.finish_onefold_relation_loop0_loop0.body queryFoldInst
      deriveQueriesInst traceInst fieldsInst prechallengeInst workNonces
      c1Frontier c2Frontier workBits selector frontierNodeBytes
      queryBatchLabels true exposeFinal256 deriveQueries checkPow semanticPoint
      queryFold prechallenge captureSnapshot prepared.circle.traceAfterPrepared
      outer.gamma outer.kappa outer.dPower outer.gammaPowers state.1
      state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2
  have parseCont : ∀ (state next : CircleState Fields)
      (iterNext : core.ops.range.Range Std.I32) (sample : Std.I32),
      core.iter.range.IteratorRange.next core.iter.range.StepI32 state.1 =
        ok (some sample, iterNext) →
      body state = ok (cont next) →
      Nonempty (AcceptedCircleStep fieldsInst state next iterNext) := by
    intro state next iterNext sample iteratorExpected edge
    unfold body at edge
    unfold v6_transcript.finish_onefold_relation_loop0_loop0.body at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
    rw [iteratorExpected] at iteratorRun
    have iteratorExact := Result.ok.inj iteratorRun
    subst iteratorPair
    simp only at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨pointPair, pointRun, edge⟩ := edge
    rcases pointPair with ⟨pointResult, transcriptAfterPoint⟩
    rw [bind_eq_ok_iff] at edge
    obtain ⟨pointMapped, pointMapRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨pointFlow, pointBranchRun, edge⟩ := edge
    cases pointFlow with
    | Break residual =>
        cases residual with
        | Ok impossible => nomatch impossible
        | Err error =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at edge
    | Continue point =>
        have pointMappedExact := branch_eq_ok_of_continue pointMapped point
          pointBranchRun
        have pointResultExact : pointResult = .Ok point := by
          rw [pointMappedExact] at pointMapRun
          cases pointResult with
          | Ok actual =>
              have actualExact : actual = point := by
                simpa [core.result.Result.map_err] using pointMapRun
              subst actual
              rfl
          | Err error =>
              simp [core.result.Result.map_err,
                v6_transcript.finish_onefold_relation.closure_4.Insts.CoreOpsFunctionFnOnceTupleCirclePointSampleErrorV6TranscriptError.call_once]
                at pointMapRun
        rw [bind_eq_ok_iff] at edge
        obtain ⟨fieldPair, fieldRun, edge⟩ := edge
        rcases fieldPair with ⟨fieldResult, fieldsAfter⟩
        rw [bind_eq_ok_iff] at edge
        obtain ⟨fieldFlow, fieldBranchRun, edge⟩ := edge
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
                    at edge
        | Continue fieldValue =>
            have fieldResultExact := branch_eq_ok_of_continue fieldResult
              fieldValue fieldBranchRun
            simp only at edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨sampleByte, _, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨record, _, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨slicePair, _, edge⟩ := edge
            rcases slicePair with ⟨recordSlice, recordBack⟩
            rw [bind_eq_ok_iff] at edge
            obtain ⟨writtenSlice, _, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨recordSlice2, _, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨transcriptAfterAbsorb, _, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨scalePair, scaleRun, edge⟩ := edge
            rcases scalePair with ⟨scaleResult, transcriptAfterScale⟩
            rw [bind_eq_ok_iff] at edge
            obtain ⟨scaleMapped, scaleMapRun, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨scaleFlow, scaleBranchRun, edge⟩ := edge
            cases scaleFlow with
            | Break residual =>
                cases residual with
                | Ok impossible => nomatch impossible
                | Err error =>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from] at edge
            | Continue scale =>
                have scaleMappedExact := branch_eq_ok_of_continue scaleMapped
                  scale scaleBranchRun
                have scaleResultExact : scaleResult = .Ok scale := by
                  rw [scaleMappedExact] at scaleMapRun
                  cases scaleResult with
                  | Ok actual =>
                      have actualExact : actual = scale := by
                        simpa [core.result.Result.map_err] using scaleMapRun
                      subst actual
                      rfl
                  | Err error =>
                      simp [core.result.Result.map_err,
                        v6_transcript.finish_onefold_relation.closure_5.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once]
                        at scaleMapRun
                rw [bind_eq_ok_iff] at edge
                obtain ⟨tensorPair, tensorRun, edge⟩ := edge
                rcases tensorPair with ⟨tensorResult, weightsAfter⟩
                rw [bind_eq_ok_iff] at edge
                obtain ⟨tensorMapped, tensorMapRun, edge⟩ := edge
                rw [bind_eq_ok_iff] at edge
                obtain ⟨tensorFlow, tensorBranchRun, edge⟩ := edge
                cases tensorFlow with
                | Break residual =>
                    cases residual with
                    | Ok impossible => nomatch impossible
                    | Err error =>
                        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame.from] at edge
                | Continue unit =>
                    have tensorMappedExact := branch_eq_ok_of_continue
                      tensorMapped unit tensorBranchRun
                    have tensorResultExact : tensorResult = .Ok () := by
                      rw [tensorMappedExact] at tensorMapRun
                      cases tensorResult with
                      | Ok actual =>
                          have actualExact : actual = () := by
                            simpa [core.result.Result.map_err] using tensorMapRun
                          subst actual
                          rfl
                      | Err error =>
                          simp [core.result.Result.map_err,
                            v6_transcript.finish_onefold_relation.closure_6.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError.call_once]
                            at tensorMapRun
                    rw [bind_eq_ok_iff] at edge
                    obtain ⟨product, productRun, edge⟩ := edge
                    rw [bind_eq_ok_iff] at edge
                    obtain ⟨runningAfter, runningRun, edge⟩ := edge
                    have nextExact : next =
                        (iterNext, transcriptAfterScale, fieldsAfter,
                          runningAfter, weightsAfter) := by
                      simpa using (ControlFlow.cont.inj
                        (Result.ok.inj edge)).symm
                    have pointSuccess :
                        transcript.Transcript.impl.challenge_secure_circle_point
                            state.2.1 =
                          ok (.Ok point, transcriptAfterPoint) := by
                      simpa [pointResultExact] using pointRun
                    have fieldSuccess :
                        fieldsInst.next_qm31 state.2.2.1 =
                          ok (.Ok fieldValue, fieldsAfter) := by
                      simpa [fieldResultExact] using fieldRun
                    have scaleSuccess :
                        transcript.Transcript.impl.challenge_qm31
                            transcriptAfterAbsorb =
                          ok (.Ok scale, transcriptAfterScale) := by
                      simpa [scaleResultExact] using scaleRun
                    have tensorSuccess :
                        sumcheck.WeightAccumulator.impl.add_circle_tensor
                            state.2.2.2.2 scale point =
                          ok (.Ok (), weightsAfter) := by
                      simpa [tensorResultExact] using tensorRun
                    obtain ⟨factors, tensorRunExact, logExact,
                        componentsExact⟩ :=
                      successful_circle_append_exact state.2.2.2.2
                        weightsAfter scale point tensorSuccess
                    exact ⟨{
                      point := point
                      transcriptAfterPoint := transcriptAfterPoint
                      pointRun := pointSuccess
                      fieldValue := fieldValue
                      fieldsAfter := fieldsAfter
                      fieldRun := fieldSuccess
                      transcriptAfterAbsorb := transcriptAfterAbsorb
                      scale := scale
                      transcriptAfterScale := transcriptAfterScale
                      scaleRun := scaleSuccess
                      factors := factors
                      weightsAfter := weightsAfter
                      appendRun := tensorSuccess
                      tensorRun := tensorRunExact
                      product := product
                      runningAfter := runningAfter
                      productRun := productRun
                      runningRun := runningRun
                      nextExact := nextExact
                      logLenExact := logExact
                      componentsExact := componentsExact }⟩
  let terminalIter : core.ops.range.Range Std.I32 :=
    { start := 2#i32, «end» := 2#i32 }
  have terminalContImpossible : ∀ (state : CircleState Fields)
      (next : CircleState Fields), state.1 = terminalIter →
      body state = ok (cont next) → False := by
    intro state next stateIter edge
    unfold body at edge
    unfold v6_transcript.finish_onefold_relation_loop0_loop0.body at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
    rw [stateIter] at iteratorRun
    unfold terminalIter at iteratorRun
    rw [rangeDone2] at iteratorRun
    have iteratorExact := Result.ok.inj iteratorRun
    subst iteratorPair
    simp only at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨traceCirclePair, _, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨relationPair, _, edge⟩ := edge
    rcases relationPair with ⟨relationResult, fieldsAfterRelation⟩
    rw [bind_eq_ok_iff] at edge
    obtain ⟨relationFlow, _, edge⟩ := edge
    cases relationFlow with
    | Break residual =>
        cases residual with
        | Ok impossible => nomatch impossible
        | Err error =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at edge
    | Continue relationFields =>
        simp only at edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨traceRelationPair, _, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨firstEncoded, _, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨firstPolynomial, _, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨transcriptAfterPolynomial, _, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨foldNonce, _, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨foldBits, _, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨foldCheckPair, _, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨foldCheckFlow, _, edge⟩ := edge
        cases foldCheckFlow with
        | Break residual =>
            cases residual with
            | Ok impossible => nomatch impossible
            | Err error =>
                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at edge
        | Continue foldUnit =>
            simp only [↓reduceIte] at edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨alphaChallengePair, _, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨alphaSwapped, _, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨alphaMapped, _, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨alphaFlow, _, edge⟩ := edge
            cases alphaFlow with
            | Break residual =>
                cases residual with
                | Ok impossible => nomatch impossible
                | Err error =>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from] at edge
            | Continue alphaZero =>
                rw [bind_eq_ok_iff] at edge
                obtain ⟨alpha, _, edge⟩ := edge
                rw [bind_eq_ok_iff] at edge
                obtain ⟨alphaZeroRead, _, edge⟩ := edge
                rw [bind_eq_ok_iff] at edge
                obtain ⟨runningClaim, _, edge⟩ := edge
                rw [bind_eq_ok_iff] at edge
                obtain ⟨weights, _, edge⟩ := edge
                rw [bind_eq_ok_iff] at edge
                obtain ⟨traceRoundPair, _, edge⟩ := edge
                rw [bind_eq_ok_iff] at edge
                obtain ⟨finalPair, _, edge⟩ := edge
                rcases finalPair with
                  ⟨finalResult, transcriptAfterFinalValues, fieldsAfterFinal⟩
                rw [bind_eq_ok_iff] at edge
                obtain ⟨finalFlow, _, edge⟩ := edge
                cases finalFlow with
                | Break residual =>
                    cases residual with
                    | Ok impossible => nomatch impossible
                    | Err error =>
                        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame.from] at edge
                | Continue foldedValues =>
                    rw [bind_eq_ok_iff] at edge
                    obtain ⟨finishResult, _, edge⟩ := edge
                    rw [bind_eq_ok_iff] at edge
                    obtain ⟨finishFlow, _, edge⟩ := edge
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
                                at edge
                    | Continue finishUnit =>
                        rw [bind_eq_ok_iff] at edge
                        obtain ⟨traceFinalPair, _, edge⟩ := edge
                        rw [bind_eq_ok_iff] at edge
                        obtain ⟨finalNonce, _, edge⟩ := edge
                        rw [bind_eq_ok_iff] at edge
                        obtain ⟨finalBits, _, edge⟩ := edge
                        rw [bind_eq_ok_iff] at edge
                        obtain ⟨finalCheckPair, _, edge⟩ := edge
                        rw [bind_eq_ok_iff] at edge
                        obtain ⟨finalCheckFlow, _, edge⟩ := edge
                        cases finalCheckFlow with
                        | Break residual =>
                            cases residual with
                            | Ok impossible => nomatch impossible
                            | Err error =>
                                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  core.convert.FromSame.from] at edge
                        | Continue finalUnit =>
                            rw [bind_eq_ok_iff] at edge
                            obtain ⟨queryResult, _, edge⟩ := edge
                            rw [bind_eq_ok_iff] at edge
                            obtain ⟨queryFlow, _, edge⟩ := edge
                            cases queryFlow with
                            | Break residual =>
                                cases residual with
                                | Ok impossible => nomatch impossible
                                | Err error =>
                                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                      core.convert.FromSame.from] at edge
                            | Continue queryValues =>
                                rcases queryValues with ⟨queries, compactCounter,
                                  frontierNodes, transcriptStateAfterQueries,
                                  acceptedQueryTranscript⟩
                                simp only at edge
                                rw [bind_eq_ok_iff] at edge
                                obtain ⟨diagnosticState, _, edge⟩ := edge
                                rw [bind_eq_ok_iff] at edge
                                obtain ⟨finalValuesRef, _, edge⟩ := edge
                                rw [bind_eq_ok_iff] at edge
                                obtain ⟨prechallengeSnapshot, _, edge⟩ := edge
                                rw [bind_eq_ok_iff] at edge
                                obtain ⟨prechallengePair, _, edge⟩ := edge
                                rw [bind_eq_ok_iff] at edge
                                obtain ⟨afterPair, _, edge⟩ := edge
                                cases edge
  have loopSuccess := prepared.circle.innerLoopSuccess
  unfold v6_transcript.finish_onefold_relation_loop0_loop0 at loopSuccess
  obtain ⟨execution⟩ := loop_success_yields_exact_trace body
    ({ start := 0#i32, «end» := 2#i32 }, outer.transcriptAfterPrefix,
      outer.fieldsAfterPrefix, outer.runningClaim,
      prepared.circle.weightsAfterPrepared)
    (some (.Ok (verified, returnedSnapshot))) loopSuccess
  cases execution with
  | done edge =>
      let origin : AcceptedCircleBodyOrigin prepared.circle := {
        state := ({ start := 0#i32, «end» := 2#i32 },
          outer.transcriptAfterPrefix, outer.fieldsAfterPrefix,
          outer.runningClaim, prepared.circle.weightsAfterPrepared)
        bodyRun := edge }
      obtain ⟨iterNext, exhausted⟩ :=
        V7CallerCurrentReleaseR26AcceptedCircleExhausted.AcceptedCircleBodyOrigin.iteratorExhausted
          origin
      have rangeRun :
          core.iter.range.IteratorRange.next core.iter.range.StepI32
              origin.state.1 =
            ok (some 0#i32, { start := 1#i32, «end» := 2#i32 }) := by
        simpa [origin] using rangeNext0End2
      rw [rangeRun] at exhausted
      have pairExact := Result.ok.inj exhausted
      have optionExact := congrArg Prod.fst pairExact
      cases optionExact
  | cont edge tail0 =>
      rename_i state1
      obtain ⟨step0⟩ := parseCont _ _ _ _ rangeNext0End2 edge
      cases tail0 with
      | done edge =>
          let origin : AcceptedCircleBodyOrigin prepared.circle := {
            state := state1
            bodyRun := edge }
          obtain ⟨iterNext, exhausted⟩ :=
            V7CallerCurrentReleaseR26AcceptedCircleExhausted.AcceptedCircleBodyOrigin.iteratorExhausted
              origin
          have rangeRun :
              core.iter.range.IteratorRange.next core.iter.range.StepI32
                  origin.state.1 =
                ok (some 1#i32,
                  { start := 2#i32, «end» := 2#i32 }) := by
            dsimp [origin]
            rw [step0.nextExact]
            exact rangeNext1End2
          rw [rangeRun] at exhausted
          have pairExact := Result.ok.inj exhausted
          have optionExact := congrArg Prod.fst pairExact
          cases optionExact
      | cont edge tail1 =>
          rename_i state2
          have rangeRun1 :
              core.iter.range.IteratorRange.next core.iter.range.StepI32
                  state1.1 =
                ok (some 1#i32,
                  { start := 2#i32, «end» := 2#i32 }) := by
            rw [step0.nextExact]
            exact rangeNext1End2
          obtain ⟨step1⟩ := parseCont _ _ _ _ rangeRun1 edge
          cases tail1 with
          | cont edge tail =>
              rename_i state3
              have stateIter : state2.1 = terminalIter := by
                rw [step1.nextExact]
              exact False.elim
                (terminalContImpossible state2 state3 stateIter edge)
          | done edge =>
              let origin : AcceptedCircleBodyOrigin prepared.circle := {
                state := state2
                bodyRun := edge }
              obtain ⟨dispatch⟩ :=
                V7CallerCurrentReleaseR26AcceptedPrechallengeDispatch.AcceptedCircleBodyOrigin.exposesPrechallengeDispatch
                  origin
              have finalComponents : origin.state.2.2.2.2.components.val =
                  [.Multilinear prepared.mScale0 prepared.mPoint0,
                   .Multilinear prepared.mScale1 prepared.mPoint1,
                   .Multilinear prepared.mScale2 prepared.mPoint2,
                   .Grouped64x16BinaryDeferred prepared.rowGroups
                     prepared.groupMasks none (alloc.vec.Vec.new RawQM31),
                   .Tensor step0.scale step0.factors,
                   .Tensor step1.scale step1.factors] := by
                have state2Weights :
                    state2.2.2.2.2.components.val =
                      step1.weightsAfter.components.val :=
                  congrArg
                    (fun state : CircleState Fields =>
                      state.2.2.2.2.components.val)
                    step1.nextExact
                have state1Weights :
                    state1.2.2.2.2.components.val =
                      step0.weightsAfter.components.val :=
                  congrArg
                    (fun state : CircleState Fields =>
                      state.2.2.2.2.components.val)
                    step0.nextExact
                dsimp [origin]
                calc
                  state2.2.2.2.2.components.val =
                      step1.weightsAfter.components.val := state2Weights
                  _ = state1.2.2.2.2.components.val ++
                      [.Tensor step1.scale step1.factors] :=
                    step1.componentsExact
                  _ = step0.weightsAfter.components.val ++
                      [.Tensor step1.scale step1.factors] := by
                    rw [state1Weights]
                  _ = (prepared.circle.weightsAfterPrepared.components.val ++
                        [.Tensor step0.scale step0.factors]) ++
                      [.Tensor step1.scale step1.factors] := by
                    rw [step0.componentsExact]
                  _ = _ := by
                    rw [prepared.componentsExact]
                    rfl
              exact ⟨{
                state1 := state1
                state2 := state2
                step0 := step0
                step1 := step1
                origin := origin
                originStateExact := rfl
                prechallengeDispatch := dispatch
                componentsExact := finalComponents }⟩

#print axioms successful_tensor_append_exact
#print axioms successful_circle_append_exact
#print axioms AcceptedPreparedAccumulator.exposesCircleAccumulator

end V7CallerCurrentReleaseR30CircleAccumulator
