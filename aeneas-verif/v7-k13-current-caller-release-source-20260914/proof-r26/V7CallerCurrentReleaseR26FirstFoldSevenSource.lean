import V7CallerCurrentReleaseR26FirstFoldTraversal
import V7CallerCurrentReleaseR26GroupedFold
import V7CallerCurrentReleaseR26GroupedRows

/-!
# Exact seven-component output of the current first fold

The accepted accumulator has three multilinear components, the released
deferred grouped component, two tensor components, and the appended line
batch.  This file exposes the exact helper call and returned constructor for
each of those seven source cells.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26FirstFoldSevenSource

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26WeightFoldLoopTrace
open V7CallerCurrentReleaseR26FirstFoldComponentTrace
open V7CallerCurrentReleaseR26FirstFoldTraversal
open V7CallerCurrentReleaseR26GroupedFold
open V7CallerCurrentReleaseR26GroupedRows

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier
abbrev Component := sumcheck.WeightComponent
abbrev Components := alloc.vec.Vec Component

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem multilinearDispatch
    (currentLog : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (componentOut : Component)
    (success : foldDeferredComponent currentLog alpha alpha2 preparedAlpha
      preparedAlpha2 alpha3 (.Multilinear scale point) = ok componentOut) :
    ∃ scaleOut pointOut,
      sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
          scale point alpha alpha2 alpha3 = ok (scaleOut, pointOut) ∧
      componentOut = .Multilinear scaleOut pointOut := by
  unfold foldDeferredComponent at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨pair, run, success⟩ := success
  rcases pair with ⟨scaleOut, pointOut⟩
  exact ⟨scaleOut, pointOut, run, Result.ok.inj success |>.symm⟩

private theorem tensorDispatch
    (currentLog : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (componentOut : Component)
    (success : foldDeferredComponent currentLog alpha alpha2 preparedAlpha
      preparedAlpha2 alpha3 (.Tensor scale factors) = ok componentOut) :
    ∃ scaleOut factorsOut,
      sumcheck.WeightAccumulator.impl.fold_tensor_arity4
          scale factors alpha3 preparedAlpha preparedAlpha2 =
        ok (scaleOut, factorsOut) ∧
      componentOut = .Tensor scaleOut factorsOut := by
  unfold foldDeferredComponent at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨pair, run, success⟩ := success
  rcases pair with ⟨scaleOut, factorsOut⟩
  exact ⟨scaleOut, factorsOut, run, Result.ok.inj success |>.symm⟩

private theorem groupedDispatch
    (currentLog : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (componentOut : Component)
    (success : foldDeferredComponent currentLog alpha alpha2 preparedAlpha
      preparedAlpha2 alpha3
        (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha
          groupValues) = ok componentOut) :
    ∃ rowGroupsOut groupMasksOut firstAlphaOut groupValuesOut,
      sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4
          rowGroups groupMasks firstAlpha groupValues currentLog alpha alpha2
            alpha3 =
        ok (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut) ∧
      componentOut = .Grouped64x16BinaryDeferred rowGroupsOut groupMasksOut
        firstAlphaOut groupValuesOut := by
  unfold foldDeferredComponent at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨output, run, success⟩ := success
  rcases output with ⟨rowGroupsOut, groupMasksOut, firstAlphaOut,
    groupValuesOut⟩
  exact ⟨rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut, run,
    Result.ok.inj success |>.symm⟩

private theorem lineBatchDispatch
    (currentLog : Std.U32) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (alpha3 : RawQM31)
    (scales : alloc.vec.Vec RawQM31) (xs : alloc.vec.Vec RawM31)
    (deferred : Std.U8) (componentOut : Component)
    (success : foldDeferredComponent currentLog alpha alpha2 preparedAlpha
      preparedAlpha2 alpha3 (.LineM31Batch scales xs deferred) =
        ok componentOut) :
    ∃ scalesOut xsOut deferredOut,
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
          (alloc.vec.Vec.deref_mut scales).1
          (alloc.vec.Vec.deref_mut xs).1 deferred alpha alpha2 alpha3 =
        ok (scalesOut, xsOut, deferredOut) ∧
      componentOut = .LineM31Batch
        ((alloc.vec.Vec.deref_mut scales).2 scalesOut)
        ((alloc.vec.Vec.deref_mut xs).2 xsOut) deferredOut := by
  unfold foldDeferredComponent at success
  simp only [Std.lift, bind_tc_ok] at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨output, run, success⟩ := success
  rcases output with ⟨scalesOut, xsOut, deferredOut⟩
  exact ⟨scalesOut, xsOut, deferredOut, run,
    Result.ok.inj success |>.symm⟩

structure FirstFoldSevenSourceTrace
    (input : sumcheck.WeightAccumulator) (alpha : RawQM31)
    (output : sumcheck.WeightAccumulator)
    (trace : FirstDeferredFoldTrace input alpha output)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (alpha0 : RawQM31) (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31) : Type where
  mScale0Out : RawQM31
  mScale1Out : RawQM31
  mScale2Out : RawQM31
  mPoint0Out : alloc.vec.Vec RawQM31
  mPoint1Out : alloc.vec.Vec RawQM31
  mPoint2Out : alloc.vec.Vec RawQM31
  rowGroupsOut : alloc.vec.Vec Std.U8
  groupMasksOut : alloc.vec.Vec Std.U16
  firstAlphaOut : Option RawQM31
  groupValuesOut : alloc.vec.Vec RawQM31
  tScale0Out : RawQM31
  tScale1Out : RawQM31
  tFactors0Out : alloc.vec.Vec RawQM31
  tFactors1Out : alloc.vec.Vec RawQM31
  lineScalesSliceOut : Slice RawQM31
  lineXsSliceOut : Slice RawM31
  lineDeferredOut : Std.U8
  multilinear0Run :
    sumcheck.WeightAccumulator.impl.fold_multilinear_arity4 mScale0 mPoint0
      alpha trace.alphaSquared trace.alphaCubed =
        ok (mScale0Out, mPoint0Out)
  multilinear1Run :
    sumcheck.WeightAccumulator.impl.fold_multilinear_arity4 mScale1 mPoint1
      alpha trace.alphaSquared trace.alphaCubed =
        ok (mScale1Out, mPoint1Out)
  multilinear2Run :
    sumcheck.WeightAccumulator.impl.fold_multilinear_arity4 mScale2 mPoint2
      alpha trace.alphaSquared trace.alphaCubed =
        ok (mScale2Out, mPoint2Out)
  groupedRun :
    sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4
      releasedRowGroups64 releasedMasks (some alpha0) groupValues input.log_len
      alpha trace.alphaSquared trace.alphaCubed =
        ok (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut)
  tensor0Run :
    sumcheck.WeightAccumulator.impl.fold_tensor_arity4 tScale0 tFactors0
      trace.alphaCubed trace.preparedAlpha trace.preparedAlphaSquared =
        ok (tScale0Out, tFactors0Out)
  tensor1Run :
    sumcheck.WeightAccumulator.impl.fold_tensor_arity4 tScale1 tFactors1
      trace.alphaCubed trace.preparedAlpha trace.preparedAlphaSquared =
        ok (tScale1Out, tFactors1Out)
  lineBatchRun :
    sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
      (alloc.vec.Vec.deref_mut lineScales).1
      (alloc.vec.Vec.deref_mut lineXs).1 0#u8 alpha trace.alphaSquared
      trace.alphaCubed =
        ok (lineScalesSliceOut, lineXsSliceOut, lineDeferredOut)
  cell0 : trace.foldedComponents.val[0]! =
    .Multilinear mScale0Out mPoint0Out
  cell1 : trace.foldedComponents.val[1]! =
    .Multilinear mScale1Out mPoint1Out
  cell2 : trace.foldedComponents.val[2]! =
    .Multilinear mScale2Out mPoint2Out
  cell3 : trace.foldedComponents.val[3]! =
    .Grouped64x16BinaryDeferred rowGroupsOut groupMasksOut firstAlphaOut
      groupValuesOut
  cell4 : trace.foldedComponents.val[4]! =
    .Tensor tScale0Out tFactors0Out
  cell5 : trace.foldedComponents.val[5]! =
    .Tensor tScale1Out tFactors1Out
  cell6 : trace.foldedComponents.val[6]! =
    .LineM31Batch ((alloc.vec.Vec.deref_mut lineScales).2 lineScalesSliceOut)
      ((alloc.vec.Vec.deref_mut lineXs).2 lineXsSliceOut) lineDeferredOut
  outputLength : trace.foldedComponents.val.length = 7

theorem first_fold_exposes_seven_source_components
    (input : sumcheck.WeightAccumulator) (alpha : RawQM31)
    (output : sumcheck.WeightAccumulator)
    (trace : FirstDeferredFoldTrace input alpha output)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (alpha0 : RawQM31) (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (inputComponents : input.components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Multilinear mScale2 mPoint2,
       .Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks
         (some alpha0) groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs 0#u8]) :
    ∃ sourceTrace : FirstFoldSevenSourceTrace input alpha output trace
        mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 alpha0 groupValues
        tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs,
      True := by
  have exactTrace := trace.componentTrace
  have expose (target : Nat) (bound : target < 7) :=
    exact_trace_exposes_component input.log_len alpha trace.alphaSquared
      trace.preparedAlpha trace.preparedAlphaSquared trace.alphaCubed
      input.components trace.foldedComponents 0#usize target (by norm_num)
      (by rw [inputComponents]; simpa using bound) exactTrace
  obtain ⟨component0, run0, cell0⟩ := expose 0 (by omega)
  obtain ⟨component1, run1, cell1⟩ := expose 1 (by omega)
  obtain ⟨component2, run2, cell2⟩ := expose 2 (by omega)
  obtain ⟨component3, run3, cell3⟩ := expose 3 (by omega)
  obtain ⟨component4, run4, cell4⟩ := expose 4 (by omega)
  obtain ⟨component5, run5, cell5⟩ := expose 5 (by omega)
  obtain ⟨component6, run6, cell6⟩ := expose 6 (by omega)
  simp only [inputComponents, List.getElem!_cons_zero,
    List.getElem!_cons_succ] at run0 run1 run2 run3 run4 run5 run6
  obtain ⟨mScale0Out, mPoint0Out, mrun0, component0Exact⟩ :=
    multilinearDispatch input.log_len alpha trace.alphaSquared
      trace.preparedAlpha trace.preparedAlphaSquared trace.alphaCubed
      mScale0 mPoint0 component0 run0
  obtain ⟨mScale1Out, mPoint1Out, mrun1, component1Exact⟩ :=
    multilinearDispatch input.log_len alpha trace.alphaSquared
      trace.preparedAlpha trace.preparedAlphaSquared trace.alphaCubed
      mScale1 mPoint1 component1 run1
  obtain ⟨mScale2Out, mPoint2Out, mrun2, component2Exact⟩ :=
    multilinearDispatch input.log_len alpha trace.alphaSquared
      trace.preparedAlpha trace.preparedAlphaSquared trace.alphaCubed
      mScale2 mPoint2 component2 run2
  obtain ⟨rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut,
      groupedRun, component3Exact⟩ :=
    groupedDispatch input.log_len alpha trace.alphaSquared trace.preparedAlpha
      trace.preparedAlphaSquared trace.alphaCubed releasedRowGroups64
      releasedMasks (some alpha0) groupValues component3 run3
  obtain ⟨tScale0Out, tFactors0Out, trun0, component4Exact⟩ :=
    tensorDispatch input.log_len alpha trace.alphaSquared trace.preparedAlpha
      trace.preparedAlphaSquared trace.alphaCubed tScale0 tFactors0
      component4 run4
  obtain ⟨tScale1Out, tFactors1Out, trun1, component5Exact⟩ :=
    tensorDispatch input.log_len alpha trace.alphaSquared trace.preparedAlpha
      trace.preparedAlphaSquared trace.alphaCubed tScale1 tFactors1
      component5 run5
  obtain ⟨lineScalesSliceOut, lineXsSliceOut, lineDeferredOut, lineRun,
      component6Exact⟩ :=
    lineBatchDispatch input.log_len alpha trace.alphaSquared trace.preparedAlpha
      trace.preparedAlphaSquared trace.alphaCubed lineScales lineXs 0#u8
      component6 run6
  have outputLength : trace.foldedComponents.val.length = 7 := by
    rw [exact_trace_preserves_length input.log_len alpha trace.alphaSquared
      trace.preparedAlpha trace.preparedAlphaSquared trace.alphaCubed
      input.components 0#usize trace.foldedComponents exactTrace,
      inputComponents]
    rfl
  refine ⟨{
    mScale0Out := mScale0Out
    mScale1Out := mScale1Out
    mScale2Out := mScale2Out
    mPoint0Out := mPoint0Out
    mPoint1Out := mPoint1Out
    mPoint2Out := mPoint2Out
    rowGroupsOut := rowGroupsOut
    groupMasksOut := groupMasksOut
    firstAlphaOut := firstAlphaOut
    groupValuesOut := groupValuesOut
    tScale0Out := tScale0Out
    tScale1Out := tScale1Out
    tFactors0Out := tFactors0Out
    tFactors1Out := tFactors1Out
    lineScalesSliceOut := lineScalesSliceOut
    lineXsSliceOut := lineXsSliceOut
    lineDeferredOut := lineDeferredOut
    multilinear0Run := mrun0
    multilinear1Run := mrun1
    multilinear2Run := mrun2
    groupedRun := groupedRun
    tensor0Run := trun0
    tensor1Run := trun1
    lineBatchRun := lineRun
    cell0 := cell0.trans component0Exact
    cell1 := cell1.trans component1Exact
    cell2 := cell2.trans component2Exact
    cell3 := cell3.trans component3Exact
    cell4 := cell4.trans component4Exact
    cell5 := cell5.trans component5Exact
    cell6 := cell6.trans component6Exact
    outputLength := outputLength }, trivial⟩

#print axioms first_fold_exposes_seven_source_components

end V7CallerCurrentReleaseR26FirstFoldSevenSource
