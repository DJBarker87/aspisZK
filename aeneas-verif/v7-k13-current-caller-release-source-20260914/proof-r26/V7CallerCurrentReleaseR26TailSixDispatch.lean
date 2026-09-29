import V7CallerCurrentReleaseR26TailSixSource

/-!
# Source helper calls inside the accepted six-component tail

These records invert each successful option-valued component step into the
literal pair of source helper calls used by that component constructor.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TailSixDispatch

open V7CallerCurrentReleaseR26TailWeightFoldTrace
open V7CallerCurrentReleaseR26TailComponentTrace

abbrev RawQM31 := field.QM31
abbrev Component := sumcheck.WeightComponent

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

structure TailMultilinearSourceTrace
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (componentOut : Component) : Type where
  scaleOne : RawQM31
  pointOne : alloc.vec.Vec RawQM31
  scaleTwo : RawQM31
  pointTwo : alloc.vec.Vec RawQM31
  firstRun : sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
    scale point tail.alpha1 tail.alpha1Squared tail.alpha1Cubed =
      ok (scaleOne, pointOne)
  secondRun : sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
    scaleOne pointOne tail.alpha2 tail.alpha2Squared tail.alpha2Cubed =
      ok (scaleTwo, pointTwo)
  outputExact : componentOut = .Multilinear scaleTwo pointTwo

theorem tail_multilinear_step_exposes_source
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (componentOut : Component)
    (run : foldTailComponent alphas
      (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
      (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
      (Array.make 2#usize
        [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
      (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
      (.Multilinear scale point) = ok (some componentOut)) :
    Nonempty (TailMultilinearSourceTrace tail scale point componentOut) := by
  unfold foldTailComponent at run
  rw [tail.alpha1Read, tail.alpha2Read] at run
  simp [Array.index_usize] at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨firstPair, firstRun, run⟩ := run
  rcases firstPair with ⟨scaleOne, pointOne⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨secondPair, secondRun, run⟩ := run
  rcases secondPair with ⟨scaleTwo, pointTwo⟩
  have outputExact : componentOut = .Multilinear scaleTwo pointTwo := by
    simpa using (Result.ok.inj run).symm
  exact ⟨{
    scaleOne := scaleOne
    pointOne := pointOne
    scaleTwo := scaleTwo
    pointTwo := pointTwo
    firstRun := firstRun
    secondRun := secondRun
    outputExact := outputExact }⟩

structure TailTensorSourceTrace
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (componentOut : Component) : Type where
  scaleOne : RawQM31
  factorsOne : alloc.vec.Vec RawQM31
  scaleTwo : RawQM31
  factorsTwo : alloc.vec.Vec RawQM31
  firstRun : sumcheck.WeightAccumulator.impl.fold_tensor_arity4
    scale factors tail.alpha1Cubed tail.preparedAlpha1
      tail.preparedAlpha1Squared = ok (scaleOne, factorsOne)
  secondRun : sumcheck.WeightAccumulator.impl.fold_tensor_arity4
    scaleOne factorsOne tail.alpha2Cubed tail.preparedAlpha2
      tail.preparedAlpha2Squared = ok (scaleTwo, factorsTwo)
  outputExact : componentOut = .Tensor scaleTwo factorsTwo

theorem tail_tensor_step_exposes_source
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (componentOut : Component)
    (run : foldTailComponent alphas
      (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
      (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
      (Array.make 2#usize
        [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
      (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
      (.Tensor scale factors) = ok (some componentOut)) :
    Nonempty (TailTensorSourceTrace tail scale factors componentOut) := by
  unfold foldTailComponent at run
  simp [Array.index_usize] at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨firstPair, firstRun, run⟩ := run
  rcases firstPair with ⟨scaleOne, factorsOne⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨secondPair, secondRun, run⟩ := run
  rcases secondPair with ⟨scaleTwo, factorsTwo⟩
  have outputExact : componentOut = .Tensor scaleTwo factorsTwo := by
    simpa using (Result.ok.inj run).symm
  exact ⟨{
    scaleOne := scaleOne
    factorsOne := factorsOne
    scaleTwo := scaleTwo
    factorsTwo := factorsTwo
    firstRun := firstRun
    secondRun := secondRun
    outputExact := outputExact }⟩

structure TailGroupedSourceTrace
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (componentOut : Component) : Type where
  foldedGroups : alloc.vec.Vec Std.U8
  foldedValues : alloc.vec.Vec RawQM31
  masksEmpty : alloc.vec.Vec.is_empty Global groupMasks = ok true
  firstNone : firstAlpha = none
  rowsLength : rowGroups.val.length = 64
  foldRun : sumcheck.fold_grouped_rows_twice
    (alloc.vec.Vec.deref rowGroups) (alloc.vec.Vec.deref groupValues)
    tail.alpha1 tail.alpha2 = ok (foldedGroups, foldedValues)
  outputExact : componentOut = .Grouped64x16BinaryDeferred foldedGroups
    groupMasks firstAlpha foldedValues

theorem tail_grouped_step_exposes_source
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (componentOut : Component)
    (run : foldTailComponent alphas
      (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
      (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
      (Array.make 2#usize
        [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
      (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
      (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha
        groupValues) = ok (some componentOut)) :
    Nonempty (TailGroupedSourceTrace tail rowGroups groupMasks firstAlpha
      groupValues componentOut) := by
  unfold foldTailComponent at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨masksEmptyValue, masksEmpty, run⟩ := run
  cases masksEmptyValue with
  | false => simp at run
  | true =>
      cases firstAlpha with
      | some first => simp at run
      | none =>
          by_cases wrongLength : alloc.vec.Vec.len rowGroups != 64#usize
          · simp [wrongLength] at run
          · simp only [wrongLength, Bool.false_eq_true, ↓reduceIte] at run
            rw [tail.alpha1Read, tail.alpha2Read] at run
            simp at run
            cases foldRun : sumcheck.fold_grouped_rows_twice
                (alloc.vec.Vec.deref rowGroups)
                (alloc.vec.Vec.deref groupValues) tail.alpha1 tail.alpha2 with
            | fail error => simp [foldRun] at run
            | div => simp [foldRun] at run
            | ok foldedPair =>
                rcases foldedPair with ⟨foldedGroups, foldedValues⟩
                simp [foldRun] at run
                have rowsLength : rowGroups.val.length = 64 := by
                  have sameScalar : alloc.vec.Vec.len rowGroups = 64#usize := by
                    apply UScalar.val_eq_imp
                    simpa using wrongLength
                  exact congrArg UScalar.val sameScalar
                have outputExact : componentOut =
                    .Grouped64x16BinaryDeferred foldedGroups groupMasks none
                      foldedValues := run.symm
                exact ⟨{
                  foldedGroups := foldedGroups
                  foldedValues := foldedValues
                  masksEmpty := masksEmpty
                  firstNone := rfl
                  rowsLength := rowsLength
                  foldRun := foldRun
                  outputExact := outputExact }⟩

structure TailLineBatchSourceTrace
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scales : alloc.vec.Vec RawQM31) (xs : alloc.vec.Vec field.M31)
    (deferred : Std.U8) (componentOut : Component) : Type where
  scalesOne : Slice RawQM31
  xsOne : Slice field.M31
  deferredOne : Std.U8
  scalesTwo : Slice RawQM31
  xsTwo : Slice field.M31
  deferredTwo : Std.U8
  firstRun : sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
    (alloc.vec.Vec.deref_mut scales).1 (alloc.vec.Vec.deref_mut xs).1
    deferred tail.alpha1 tail.alpha1Squared tail.alpha1Cubed =
      ok (scalesOne, xsOne, deferredOne)
  secondRun : sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
    (alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut scales).2 scalesOne)).1
    (alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut xs).2 xsOne)).1
    deferredOne tail.alpha2 tail.alpha2Squared tail.alpha2Cubed =
      ok (scalesTwo, xsTwo, deferredTwo)
  outputExact : componentOut = .LineM31Batch
    ((alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut scales).2 scalesOne)).2 scalesTwo)
    ((alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut xs).2 xsOne)).2 xsTwo)
    deferredTwo

theorem tail_line_batch_step_exposes_source
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scales : alloc.vec.Vec RawQM31) (xs : alloc.vec.Vec field.M31)
    (deferred : Std.U8) (componentOut : Component)
    (run : foldTailComponent alphas
      (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
      (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
      (Array.make 2#usize
        [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
      (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
      (.LineM31Batch scales xs deferred) = ok (some componentOut)) :
    Nonempty (TailLineBatchSourceTrace tail scales xs deferred
      componentOut) := by
  unfold foldTailComponent at run
  rw [tail.alpha1Read, tail.alpha2Read] at run
  simp [Array.index_usize, Std.lift] at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨firstOutput, firstRun, run⟩ := run
  rcases firstOutput with ⟨scalesOne, xsOne, deferredOne⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨secondOutput, secondRun, run⟩ := run
  rcases secondOutput with ⟨scalesTwo, xsTwo, deferredTwo⟩
  have outputExact : componentOut = .LineM31Batch
      ((alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut scales).2 scalesOne)).2 scalesTwo)
      ((alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut xs).2 xsOne)).2 xsTwo)
      deferredTwo := by
    simpa using (Result.ok.inj run).symm
  exact ⟨{
    scalesOne := scalesOne
    xsOne := xsOne
    deferredOne := deferredOne
    scalesTwo := scalesTwo
    xsTwo := xsTwo
    deferredTwo := deferredTwo
    firstRun := firstRun
    secondRun := secondRun
    outputExact := outputExact }⟩

#print axioms tail_multilinear_step_exposes_source
#print axioms tail_tensor_step_exposes_source
#print axioms tail_grouped_step_exposes_source
#print axioms tail_line_batch_step_exposes_source

end V7CallerCurrentReleaseR26TailSixDispatch
