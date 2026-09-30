import V7ProductionSnapshotObserverR30InitialClaimCanonical
import V7CallerCurrentReleaseR26AcceptedOuterLoop

/-!
# Exact outer accumulator construction

The generated outer relation loop appends the three statement-point
multilinears and then the prepared grouped component.  This module follows
that exact loop trace and retains the literal four-component accumulator
passed to the nested circle loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30OuterAccumulator

open V7CallerCurrentReleaseR26AcceptedOnefoldPrefix
open V7CallerCurrentReleaseR26AcceptedOuterLoop
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR30StatementPointsCanonical
open V7ProductionSnapshotObserverR30InitialClaimCanonical

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev RawComponent := sumcheck.WeightComponent

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

private theorem array_index_exact
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (bound : index.val < N.val)
    (run : Array.index_usize values index = ok value) :
    value = values.val[index.val]! := by
  obtain ⟨expected, expectedRun, expectedExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_usize_spec values index (by
        simpa [Array.length_eq] using bound))
  have valueExact : value = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [valueExact, expectedExact]
  exact (List.getElem!_of_getElem? (by simp)).symm

private theorem to_vec_exact {T : Type}
    (cloneInst : core.clone.Clone T) (slice : Slice T)
    (cloneExact : ∀ value, value ∈ slice.val → cloneInst.clone value = ok value)
    (vector : alloc.vec.Vec T)
    (run : alloc.slice.Slice.to_vec cloneInst slice = ok vector) :
    vector.val = slice.val := by
  obtain ⟨expected, expectedRun, expectedExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.slice.Slice.to_vec_spec cloneInst slice cloneExact)
  have vectorExact : vector = expected :=
    Result.ok.inj (run.symm.trans expectedRun)
  rw [vectorExact]
  exact congrArg Subtype.val expectedExact.symm

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

theorem successful_empty_exact
    (weights : RawWeights)
    (run : sumcheck.WeightAccumulator.impl.empty 10#u32 = ok weights) :
    weights.log_len = 10#u32 ∧ weights.components.val = [] := by
  unfold sumcheck.WeightAccumulator.impl.empty at run
  simp only [Result.ok.injEq] at run
  subst weights
  simp [alloc.vec.Vec.new]

theorem successful_multilinear_append_exact
    (weights weightsAfter : RawWeights) (scale : RawQM31)
    (point : alloc.vec.Vec RawQM31)
    (run : sumcheck.WeightAccumulator.impl.add_multilinear weights scale point =
      ok (.Ok (), weightsAfter)) :
    weightsAfter.log_len = weights.log_len ∧
      weightsAfter.components.val = weights.components.val ++
        [.Multilinear scale point] := by
  unfold sumcheck.WeightAccumulator.impl.add_multilinear at run
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
      (.Multilinear scale point) pushRun⟩

private theorem prepared_body_cannot_return_success
    (rowGroups : Array Std.U8 64#usize) (groupMasks : Slice Std.U16)
    (high : Std.Usize)
    (run :
      sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared_loop.body
          rowGroups groupMasks high =
        ok (done (some (.Ok ())))) : False := by
  unfold sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared_loop.body at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨rowSlice, _, run⟩ := run
  dsimp only at run
  split at run
  · rw [bind_eq_ok_iff] at run
    obtain ⟨group, _, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨groupIndex, _, run⟩ := run
    split at run
    · cases run
    · rw [bind_eq_ok_iff] at run
      obtain ⟨next, _, run⟩ := run
      cases run
  · cases run

private theorem prepared_trace_cannot_return_success
    (rowGroups : Array Std.U8 64#usize) (groupMasks : Slice Std.U16) :
    ∀ {high : Std.Usize},
      ExactLoopTrace
          (fun current =>
            sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared_loop.body
              rowGroups groupMasks current)
          high (some (.Ok ())) → False
  | _, .done equation =>
      prepared_body_cannot_return_success rowGroups groupMasks _ equation
  | _, .cont _ tail =>
      prepared_trace_cannot_return_success rowGroups groupMasks tail

private theorem prepared_loop_cannot_return_success
    (rowGroups : Array Std.U8 64#usize) (groupMasks : Slice Std.U16)
    (high : Std.Usize)
    (run :
      sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared_loop
          rowGroups groupMasks high =
        ok (some (.Ok ()))) : False := by
  unfold sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared_loop at run
  let body := fun current =>
    sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared_loop.body
      rowGroups groupMasks current
  obtain ⟨trace⟩ := loop_success_yields_exact_trace body high
    (some (.Ok ())) run
  exact prepared_trace_cannot_return_success rowGroups groupMasks trace

private theorem successful_install_prepared_exact
    (weights weightsAfter : RawWeights)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (run :
      sumcheck.WeightAccumulator.impl.install_grouped_64x16_binary_masks_deferred_prepared
          weights rowGroups groupMasks = ok weightsAfter) :
    weightsAfter.log_len = weights.log_len ∧
      weightsAfter.components.val = weights.components.val ++
        [.Grouped64x16BinaryDeferred rowGroups groupMasks none
          (alloc.vec.Vec.new RawQM31)] := by
  unfold sumcheck.WeightAccumulator.impl.install_grouped_64x16_binary_masks_deferred_prepared at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨componentsAfter, pushRun, run⟩ := run
  simp only [Result.ok.injEq] at run
  subst weightsAfter
  exact ⟨rfl, push_exact weights.components componentsAfter
    (.Grouped64x16BinaryDeferred rowGroups groupMasks none
      (alloc.vec.Vec.new RawQM31)) pushRun⟩

theorem successful_prepared_append_exact
    (weights weightsAfter : RawWeights)
    (rowGroups : Array Std.U8 64#usize) (groupMasks : Slice Std.U16)
    (run :
      sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared
          weights rowGroups groupMasks = ok (.Ok (), weightsAfter)) :
    ∃ rowGroupsVec : alloc.vec.Vec Std.U8,
      ∃ groupMasksVec : alloc.vec.Vec Std.U16,
        rowGroupsVec.val = rowGroups.val ∧
        groupMasksVec.val = groupMasks.val ∧
        weightsAfter.log_len = weights.log_len ∧
        weightsAfter.components.val = weights.components.val ++
          [.Grouped64x16BinaryDeferred rowGroupsVec groupMasksVec none
            (alloc.vec.Vec.new RawQM31)] := by
  unfold sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared at run
  split at run
  · cases run
  · rw [bind_eq_ok_iff] at run
    obtain ⟨empty, _, run⟩ := run
    split at run
    · cases run
    · rw [bind_eq_ok_iff] at run
      obtain ⟨pending, pendingRun, run⟩ := run
      cases pending with
      | some result =>
          have resultExact : result = .Ok () := by
            simpa using congrArg Prod.fst (Result.ok.inj run)
          subst result
          exact False.elim
            (prepared_loop_cannot_return_success rowGroups groupMasks 0#usize
              pendingRun)
      | none =>
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨rowSlice, rowSliceRun, run⟩ := run
          have rowSliceExact : rowSlice = Array.to_slice rowGroups := by
            simpa [Std.lift] using (Result.ok.inj rowSliceRun).symm
          subst rowSlice
          rw [bind_eq_ok_iff] at run
          obtain ⟨rowGroupsVec, rowVecRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨groupMasksVec, maskVecRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨installed, installRun, run⟩ := run
          have installedExact : installed = weightsAfter := by
            simpa using congrArg Prod.snd (Result.ok.inj run)
          subst installed
          obtain ⟨logExact, componentsExact⟩ :=
            successful_install_prepared_exact weights weightsAfter
              rowGroupsVec groupMasksVec installRun
          have rowExact : rowGroupsVec.val = rowGroups.val := by
            obtain ⟨expected, expectedRun, expectedExact⟩ :=
              Aeneas.Std.WP.spec_imp_exists
                (alloc.slice.Slice.to_vec_spec core.clone.CloneU8
                  (Array.to_slice rowGroups) (by
                    intro value _
                    rfl))
            have vectorExact : rowGroupsVec = expected :=
              Result.ok.inj (rowVecRun.symm.trans expectedRun)
            rw [vectorExact]
            exact congrArg Subtype.val expectedExact.symm
          have maskExact : groupMasksVec.val = groupMasks.val := by
            obtain ⟨expected, expectedRun, expectedExact⟩ :=
              Aeneas.Std.WP.spec_imp_exists
                (alloc.slice.Slice.to_vec_spec core.clone.CloneU16
                  groupMasks (by
                    intro value _
                    rfl))
            have vectorExact : groupMasksVec = expected :=
              Result.ok.inj (maskVecRun.symm.trans expectedRun)
            rw [vectorExact]
            exact congrArg Subtype.val expectedExact.symm
          exact ⟨rowGroupsVec, groupMasksVec, rowExact, maskExact,
            logExact, componentsExact⟩

private theorem rangeNext0End3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS } =
      ok (some 0#usize,
        { start := 1#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }) := by
  have hmax : 0 < UScalar.max .Usize := by
    have h := (1#usize).hBounds
    scalar_tac
  simp [v6_onefold.V6_POINT_CLAIM_ROWS,
    core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext1End3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS } =
      ok (some 1#usize,
        { start := 2#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }) := by
  have hmax : 1 < UScalar.max .Usize := by
    have h := (2#usize).hBounds
    scalar_tac
  simp [v6_onefold.V6_POINT_CLAIM_ROWS,
    core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext2End3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS } =
      ok (some 2#usize,
        { start := 3#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }) := by
  have hmax : 2 < UScalar.max .Usize := by
    have h := (3#usize).hBounds
    scalar_tac
  simp [v6_onefold.V6_POINT_CLAIM_ROWS,
    core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeDone3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 3#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS } =
      ok (none,
        { start := 3#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }) := by
  simp [v6_onefold.V6_POINT_CLAIM_ROWS,
    core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

/-- The exact four-component accumulator selected by one successful outer
loop, paired with the nested circle loop that consumes it. -/
structure AcceptedPreparedAccumulator
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
    (outer : AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot) : Type where
  circle : AcceptedCircleLoopDispatch outer
  mScale0 : RawQM31
  mScale1 : RawQM31
  mScale2 : RawQM31
  mPoint0 : alloc.vec.Vec RawQM31
  mPoint1 : alloc.vec.Vec RawQM31
  mPoint2 : alloc.vec.Vec RawQM31
  rowGroups : alloc.vec.Vec Std.U8
  groupMasks : alloc.vec.Vec Std.U16
  scale0Run : Array.index_usize outer.pointScales 0#usize = ok mScale0
  scale1Run : Array.index_usize outer.pointScales 1#usize = ok mScale1
  scale2Run : Array.index_usize outer.pointScales 2#usize = ok mScale2
  point0Exact : mPoint0.val = outer.points.val[0]!.val
  point1Exact : mPoint1.val = outer.points.val[1]!.val
  point2Exact : mPoint2.val = outer.points.val[2]!.val
  rowGroupsExact : rowGroups.val = inactiveRowGroups.val
  groupMasksExact : groupMasks.val = inactiveGroupMasks.val
  logLenExact : circle.weightsAfterPrepared.log_len = 10#u32
  componentsExact : circle.weightsAfterPrepared.components.val =
    [.Multilinear mScale0 mPoint0,
     .Multilinear mScale1 mPoint1,
     .Multilinear mScale2 mPoint2,
     .Grouped64x16BinaryDeferred rowGroups groupMasks none
       (alloc.vec.Vec.new RawQM31)]

theorem AcceptedOnefoldLoopDispatch.exposesPreparedAccumulator
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
    (outer : AcceptedOnefoldLoopDispatch queryFoldInst deriveQueriesInst
      traceInst fieldsInst prechallengeInst transcript0 workNonces c1Frontier
      c2Frontier workBits selector frontierNodeBytes queryBatchLabels
      exposeFinal256 deriveQueries fields0 inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint pointClaims queryFold
      prechallenge captureSnapshot trace0 verified returnedSnapshot) :
    Nonempty (AcceptedPreparedAccumulator outer) := by
  let body := fun (state : core.ops.range.Range Std.Usize × RawWeights) =>
    v6_transcript.finish_onefold_relation_loop0.body queryFoldInst
      deriveQueriesInst traceInst fieldsInst prechallengeInst
      outer.transcriptAfterPrefix workNonces c1Frontier c2Frontier workBits
      selector frontierNodeBytes queryBatchLabels true exposeFinal256
      deriveQueries outer.fieldsAfterPrefix inactiveRowGroups
      inactiveGroupMasks checkPow semanticPoint queryFold prechallenge
      captureSnapshot outer.traceAfterStart outer.gamma outer.kappa
      outer.points outer.pointScales outer.dPower outer.gammaPowers
      outer.runningClaim state.1 state.2
  have parseCont : ∀ (iter iterNext : core.ops.range.Range Std.Usize)
      (weights : RawWeights) (row : Std.Usize)
      (next : core.ops.range.Range Std.Usize × RawWeights),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        ok (some row, iterNext) →
      body (iter, weights) = ok (cont next) →
      ∃ scale : RawQM31, ∃ point : Array RawQM31 10#usize,
        ∃ pointVec : alloc.vec.Vec RawQM31, ∃ weightsNext : RawWeights,
          Array.index_usize outer.pointScales row = ok scale ∧
          Array.index_usize outer.points row = ok point ∧
          pointVec.val = point.val ∧
          next = (iterNext, weightsNext) ∧
          weightsNext.log_len = weights.log_len ∧
          weightsNext.components.val = weights.components.val ++
            [.Multilinear scale pointVec] := by
    intro iter iterNext weights row next iteratorExpected edge
    unfold body at edge
    unfold v6_transcript.finish_onefold_relation_loop0.body at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
    rw [iteratorExpected] at iteratorRun
    have iteratorExact := Result.ok.inj iteratorRun
    subst iteratorPair
    simp only at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨scale, scaleRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨point, pointRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨pointSlice, pointSliceRun, edge⟩ := edge
    have pointSliceExact : pointSlice = Array.to_slice point := by
      simpa [Std.lift] using (Result.ok.inj pointSliceRun).symm
    subst pointSlice
    rw [bind_eq_ok_iff] at edge
    obtain ⟨pointVec, pointVecRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨multilinearPair, multilinearRun, edge⟩ := edge
    rcases multilinearPair with ⟨multilinearResult, weightsNext⟩
    rw [bind_eq_ok_iff] at edge
    obtain ⟨multilinearMapped, multilinearMapRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨flow, branchRun, edge⟩ := edge
    cases flow with
    | Break residual =>
        cases residual with
        | Ok impossible => nomatch impossible
        | Err error =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at edge
    | Continue unit =>
        have mappedExact := branch_eq_ok_of_continue multilinearMapped unit
          branchRun
        have resultExact : multilinearResult = .Ok () := by
          rw [mappedExact] at multilinearMapRun
          cases multilinearResult with
          | Ok actual =>
              have actualExact : actual = () := by
                simpa [core.result.Result.map_err] using multilinearMapRun
              subst actual
              rfl
          | Err error =>
              simp [core.result.Result.map_err,
                v6_transcript.finish_onefold_relation.closure_2.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError.call_once]
                at multilinearMapRun
        have appendExact := successful_multilinear_append_exact weights
          weightsNext scale pointVec (by simpa [resultExact] using multilinearRun)
        have nextExact : next = (iterNext, weightsNext) := by
          simpa using (ControlFlow.cont.inj (Result.ok.inj edge)).symm
        have pointExact : pointVec.val = point.val :=
          to_vec_exact field.QM31.Insts.CoreCloneClone
            (Array.to_slice point) (by
              intro value _
              simp [field.QM31.Insts.CoreCloneClone.clone]) pointVec pointVecRun
        exact ⟨scale, point, pointVec, weightsNext, scaleRun, pointRun,
          pointExact, nextExact, appendExact.1, appendExact.2⟩
  have rowDoneImpossible : ∀
      (iter iterNext : core.ops.range.Range Std.Usize)
      (weights : RawWeights) (row : Std.Usize),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        ok (some row, iterNext) →
      body (iter, weights) =
        ok (done (some (.Ok (verified, returnedSnapshot)))) → False := by
    intro iter iterNext weights row iteratorExpected edge
    unfold body at edge
    unfold v6_transcript.finish_onefold_relation_loop0.body at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
    rw [iteratorExpected] at iteratorRun
    have iteratorExact := Result.ok.inj iteratorRun
    subst iteratorPair
    simp only at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨scale, _, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨point, _, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨pointSlice, _, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨pointVec, _, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨multilinearPair, _, edge⟩ := edge
    rcases multilinearPair with ⟨multilinearResult, weightsNext⟩
    rw [bind_eq_ok_iff] at edge
    obtain ⟨multilinearMapped, _, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨flow, _, edge⟩ := edge
    cases flow with
    | Continue unit => cases edge
    | Break residual =>
        cases residual with
        | Ok impossible => nomatch impossible
        | Err error =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at edge
  let terminalIter : core.ops.range.Range Std.Usize :=
    { start := 3#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }
  have parseDone : ∀ (weights : RawWeights),
      body (terminalIter, weights) =
        ok (done (some (.Ok (verified, returnedSnapshot)))) →
      ∃ circle : AcceptedCircleLoopDispatch outer,
        sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared
            weights inactiveRowGroups inactiveGroupMasks =
          ok (.Ok (), circle.weightsAfterPrepared) := by
    intro weights edge
    unfold body at edge
    unfold v6_transcript.finish_onefold_relation_loop0.body at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
    unfold terminalIter at iteratorRun
    rw [rangeDone3] at iteratorRun
    have iteratorExact := Result.ok.inj iteratorRun
    subst iteratorPair
    simp only at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨preparedPair, preparedRun, edge⟩ := edge
    rcases preparedPair with ⟨preparedResult, weightsAfterPrepared⟩
    rw [bind_eq_ok_iff] at edge
    obtain ⟨preparedMapped, preparedMapRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨flow, branchRun, edge⟩ := edge
    cases flow with
    | Break residual =>
        cases residual with
        | Ok impossible => nomatch impossible
        | Err error =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at edge
    | Continue unit =>
        have mappedExact := branch_eq_ok_of_continue preparedMapped unit
          branchRun
        have resultExact : preparedResult = .Ok () := by
          rw [mappedExact] at preparedMapRun
          cases preparedResult with
          | Ok actual =>
              have actualExact : actual = () := by
                simpa [core.result.Result.map_err] using preparedMapRun
              subst actual
              rfl
          | Err error =>
              simp [core.result.Result.map_err,
                v6_transcript.finish_onefold_relation.closure_3.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError.call_once]
                at preparedMapRun
        have preparedSuccess :
            sumcheck.WeightAccumulator.impl.add_grouped_64x16_binary_masks_deferred_prepared
                weights inactiveRowGroups inactiveGroupMasks =
              ok (.Ok (), weightsAfterPrepared) := by
          simpa [resultExact] using preparedRun
        simp only at edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨tracePair, _, edge⟩ := edge
        rcases tracePair with ⟨_, traceAfterPrepared⟩
        rw [bind_eq_ok_iff] at edge
        obtain ⟨pendingReturn, innerRun, edge⟩ := edge
        cases pendingReturn with
        | none => simp at edge
        | some innerResult =>
            have innerExact :
                innerResult = .Ok (verified, returnedSnapshot) := by
              simpa using edge
            subst innerResult
            let circle : AcceptedCircleLoopDispatch outer := {
              weightsAfterPrepared := weightsAfterPrepared
              traceAfterPrepared := traceAfterPrepared
              innerLoopSuccess := innerRun }
            exact ⟨circle, preparedSuccess⟩
  have terminalContImpossible : ∀ (weights : RawWeights)
      (next : core.ops.range.Range Std.Usize × RawWeights),
      body (terminalIter, weights) = ok (cont next) → False := by
    intro weights next edge
    unfold body at edge
    unfold v6_transcript.finish_onefold_relation_loop0.body at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
    unfold terminalIter at iteratorRun
    rw [rangeDone3] at iteratorRun
    have iteratorExact := Result.ok.inj iteratorRun
    subst iteratorPair
    simp only at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨preparedPair, _, edge⟩ := edge
    rcases preparedPair with ⟨preparedResult, weightsAfterPrepared⟩
    rw [bind_eq_ok_iff] at edge
    obtain ⟨preparedMapped, _, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨flow, _, edge⟩ := edge
    cases flow with
    | Break residual =>
        cases residual with
        | Ok impossible => nomatch impossible
        | Err error =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at edge
    | Continue unit =>
        simp only at edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨tracePair, _, edge⟩ := edge
        rw [bind_eq_ok_iff] at edge
        obtain ⟨pendingReturn, _, edge⟩ := edge
        cases pendingReturn <;> cases edge
  have loopSuccess := outer.loopSuccess
  unfold v6_transcript.finish_onefold_relation_loop0 at loopSuccess
  obtain ⟨execution⟩ := loop_success_yields_exact_trace body
    ({ start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS },
      outer.weights)
    (some (.Ok (verified, returnedSnapshot))) loopSuccess
  cases execution with
  | done edge =>
      exact False.elim (rowDoneImpossible _ _ _ _ rangeNext0End3 edge)
  | cont edge tail0 =>
      obtain ⟨scale0, point0, pointVec0, weights1, scale0Run, point0Run,
          pointVec0Exact, next0Exact, log1, components1⟩ :=
        parseCont _ _ _ _ _ rangeNext0End3 edge
      rw [next0Exact] at tail0
      cases tail0 with
      | done edge =>
          exact False.elim (rowDoneImpossible _ _ _ _ rangeNext1End3 edge)
      | cont edge tail1 =>
          obtain ⟨scale1, point1, pointVec1, weights2, scale1Run,
              point1Run, pointVec1Exact, next1Exact, log2, components2⟩ :=
            parseCont _ _ _ _ _ rangeNext1End3 edge
          rw [next1Exact] at tail1
          cases tail1 with
          | done edge =>
              exact False.elim
                (rowDoneImpossible _ _ _ _ rangeNext2End3 edge)
          | cont edge tail2 =>
              obtain ⟨scale2, point2, pointVec2, weights3, scale2Run,
                  point2Run, pointVec2Exact, next2Exact, log3,
                  components3⟩ :=
                parseCont _ _ _ _ _ rangeNext2End3 edge
              rw [next2Exact] at tail2
              cases tail2 with
              | cont edge tail =>
                  exact False.elim (terminalContImpossible weights3 _ edge)
              | done edge =>
                  obtain ⟨circle, preparedRun⟩ := parseDone weights3 edge
                  obtain ⟨rowGroups, groupMasks, rowGroupsExact,
                      groupMasksExact, log4, components4⟩ :=
                    successful_prepared_append_exact weights3
                      circle.weightsAfterPrepared inactiveRowGroups
                      inactiveGroupMasks preparedRun
                  obtain ⟨initialLog, initialComponents⟩ :=
                    successful_empty_exact outer.weights outer.weightsRun
                  have finalLog : circle.weightsAfterPrepared.log_len =
                      10#u32 := by
                    rw [log4, log3, log2, log1, initialLog]
                  have finalComponents :
                      circle.weightsAfterPrepared.components.val =
                        [.Multilinear scale0 pointVec0,
                         .Multilinear scale1 pointVec1,
                         .Multilinear scale2 pointVec2,
                         .Grouped64x16BinaryDeferred rowGroups groupMasks none
                           (alloc.vec.Vec.new RawQM31)] := by
                    rw [components4, components3, components2, components1,
                      initialComponents]
                    rfl
                  have point0Array : point0 = outer.points.val[0]! :=
                    array_index_exact outer.points 0#usize point0 (by decide)
                      point0Run
                  have point1Array : point1 = outer.points.val[1]! :=
                    array_index_exact outer.points 1#usize point1 (by decide)
                      point1Run
                  have point2Array : point2 = outer.points.val[2]! :=
                    array_index_exact outer.points 2#usize point2 (by decide)
                      point2Run
                  exact ⟨{
                    circle := circle
                    mScale0 := scale0
                    mScale1 := scale1
                    mScale2 := scale2
                    mPoint0 := pointVec0
                    mPoint1 := pointVec1
                    mPoint2 := pointVec2
                    rowGroups := rowGroups
                    groupMasks := groupMasks
                    scale0Run := scale0Run
                    scale1Run := scale1Run
                    scale2Run := scale2Run
                    point0Exact := by simpa [point0Array] using pointVec0Exact
                    point1Exact := by simpa [point1Array] using pointVec1Exact
                    point2Exact := by simpa [point2Array] using pointVec2Exact
                    rowGroupsExact := rowGroupsExact
                    groupMasksExact := groupMasksExact
                    logLenExact := finalLog
                    componentsExact := finalComponents }⟩

#print axioms successful_empty_exact
#print axioms successful_multilinear_append_exact
#print axioms successful_prepared_append_exact
#print axioms AcceptedOnefoldLoopDispatch.exposesPreparedAccumulator

end V7CallerCurrentReleaseR30OuterAccumulator
