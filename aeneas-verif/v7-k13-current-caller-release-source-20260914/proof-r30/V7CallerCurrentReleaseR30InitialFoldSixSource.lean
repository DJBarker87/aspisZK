import V7CallerCurrentReleaseR30InitialPrechallengeDispatch
import V7CallerCurrentReleaseR26FirstFoldTraversal

/-!
# Exact six-component output of the production initial fold

The current circle terminal supplies six components at log length ten.  The
first deferred fold is traced cell-by-cell so the accumulator passed to query
insertion retains its exact source constructors without unfolding the loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30InitialFoldSixSource

open V7CallerCurrentReleaseR26FirstFoldComponentTrace
open V7CallerCurrentReleaseR26FirstFoldTraversal
open V7CallerCurrentReleaseR26WeightFoldLoopTrace

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

private theorem multilinear_dispatch
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

private theorem tensor_dispatch
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

private theorem grouped_dispatch
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

structure InitialFoldSixSourceTrace
    (input : sumcheck.WeightAccumulator) (alpha : RawQM31)
    (output : sumcheck.WeightAccumulator)
    (trace : FirstDeferredFoldTrace input alpha output)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31) : Type where
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
      rowGroups groupMasks none groupValues input.log_len
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
  cell0 : trace.foldedComponents.val[0]! = .Multilinear mScale0Out mPoint0Out
  cell1 : trace.foldedComponents.val[1]! = .Multilinear mScale1Out mPoint1Out
  cell2 : trace.foldedComponents.val[2]! = .Multilinear mScale2Out mPoint2Out
  cell3 : trace.foldedComponents.val[3]! =
    .Grouped64x16BinaryDeferred rowGroupsOut groupMasksOut firstAlphaOut
      groupValuesOut
  cell4 : trace.foldedComponents.val[4]! = .Tensor tScale0Out tFactors0Out
  cell5 : trace.foldedComponents.val[5]! = .Tensor tScale1Out tFactors1Out
  outputLength : trace.foldedComponents.val.length = 6

theorem initial_fold_exposes_six_source_components
    (input : sumcheck.WeightAccumulator) (alpha : RawQM31)
    (output : sumcheck.WeightAccumulator)
    (trace : FirstDeferredFoldTrace input alpha output)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (inputComponents : input.components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Multilinear mScale2 mPoint2,
       .Grouped64x16BinaryDeferred rowGroups groupMasks none groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1]) :
    ∃ sourceTrace : InitialFoldSixSourceTrace input alpha output trace
        mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 rowGroups groupMasks
        groupValues tScale0 tScale1 tFactors0 tFactors1,
      True := by
  have exactTrace := trace.componentTrace
  have expose (target : Nat) (bound : target < 6) :=
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
  simp only [inputComponents, List.getElem!_cons_zero,
    List.getElem!_cons_succ] at run0 run1 run2 run3 run4 run5
  obtain ⟨mScale0Out, mPoint0Out, mrun0, component0Exact⟩ :=
    multilinear_dispatch input.log_len alpha trace.alphaSquared
      trace.preparedAlpha trace.preparedAlphaSquared trace.alphaCubed
      mScale0 mPoint0 component0 run0
  obtain ⟨mScale1Out, mPoint1Out, mrun1, component1Exact⟩ :=
    multilinear_dispatch input.log_len alpha trace.alphaSquared
      trace.preparedAlpha trace.preparedAlphaSquared trace.alphaCubed
      mScale1 mPoint1 component1 run1
  obtain ⟨mScale2Out, mPoint2Out, mrun2, component2Exact⟩ :=
    multilinear_dispatch input.log_len alpha trace.alphaSquared
      trace.preparedAlpha trace.preparedAlphaSquared trace.alphaCubed
      mScale2 mPoint2 component2 run2
  obtain ⟨rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut,
      groupedRun, component3Exact⟩ :=
    grouped_dispatch input.log_len alpha trace.alphaSquared trace.preparedAlpha
      trace.preparedAlphaSquared trace.alphaCubed rowGroups groupMasks none
      groupValues component3 run3
  obtain ⟨tScale0Out, tFactors0Out, trun0, component4Exact⟩ :=
    tensor_dispatch input.log_len alpha trace.alphaSquared trace.preparedAlpha
      trace.preparedAlphaSquared trace.alphaCubed tScale0 tFactors0 component4
      run4
  obtain ⟨tScale1Out, tFactors1Out, trun1, component5Exact⟩ :=
    tensor_dispatch input.log_len alpha trace.alphaSquared trace.preparedAlpha
      trace.preparedAlphaSquared trace.alphaCubed tScale1 tFactors1 component5
      run5
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
    multilinear0Run := mrun0
    multilinear1Run := mrun1
    multilinear2Run := mrun2
    groupedRun := groupedRun
    tensor0Run := trun0
    tensor1Run := trun1
    cell0 := cell0.trans component0Exact
    cell1 := cell1.trans component1Exact
    cell2 := cell2.trans component2Exact
    cell3 := cell3.trans component3Exact
    cell4 := cell4.trans component4Exact
    cell5 := cell5.trans component5Exact
    outputLength := by
      rw [exact_trace_preserves_length input.log_len alpha trace.alphaSquared
        trace.preparedAlpha trace.preparedAlphaSquared trace.alphaCubed
        input.components 0#usize trace.foldedComponents exactTrace]
      rw [inputComponents]
      norm_num
  }, trivial⟩

/-- The six component witnesses reconstruct the exact vector returned by the
initial fold. -/
theorem InitialFoldSixSourceTrace.output_components_exact
    {input output : sumcheck.WeightAccumulator} {alpha : RawQM31}
    {trace : FirstDeferredFoldTrace input alpha output}
    {mScale0 mScale1 mScale2 : RawQM31}
    {mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31}
    {rowGroups : alloc.vec.Vec Std.U8} {groupMasks : alloc.vec.Vec Std.U16}
    {groupValues : alloc.vec.Vec RawQM31}
    {tScale0 tScale1 : RawQM31}
    {tFactors0 tFactors1 : alloc.vec.Vec RawQM31}
    (source : InitialFoldSixSourceTrace input alpha output trace
      mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 rowGroups groupMasks
      groupValues tScale0 tScale1 tFactors0 tFactors1) :
    output.components.val =
      [.Multilinear source.mScale0Out source.mPoint0Out,
       .Multilinear source.mScale1Out source.mPoint1Out,
       .Multilinear source.mScale2Out source.mPoint2Out,
       .Grouped64x16BinaryDeferred source.rowGroupsOut source.groupMasksOut
         source.firstAlphaOut source.groupValuesOut,
       .Tensor source.tScale0Out source.tFactors0Out,
       .Tensor source.tScale1Out source.tFactors1Out] := by
  rw [trace.outputComponents]
  apply List.ext_getElem
  · simpa using source.outputLength
  · intro index leftBound rightBound
    rw [List.Inhabited_getElem_eq_getElem!
      trace.foldedComponents.val index leftBound]
    have indexBound : index < 6 := by simpa using rightBound
    interval_cases index
    · simpa only [List.getElem_cons_zero] using source.cell0
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell1
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell2
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell3
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell4
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell5

#print axioms initial_fold_exposes_six_source_components
#print axioms InitialFoldSixSourceTrace.output_components_exact

end V7CallerCurrentReleaseR30InitialFoldSixSource
