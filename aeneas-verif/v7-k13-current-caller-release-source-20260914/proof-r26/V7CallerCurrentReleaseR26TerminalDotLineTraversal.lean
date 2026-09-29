import V7CallerCurrentReleaseR26TerminalLineSource

/-!
# Six-component line traversals inside terminal dot

The accepted accumulator has five non-line components followed by one folded
line batch.  These lemmas establish the exact max-deferred scan and the exact
zero-initialized line accumulation traversal without unfolding line
arithmetic.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalDotLineTraversal

open V7CallerCurrentReleaseR26TerminalLineBatchZero

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev Component := sumcheck.WeightComponent
abbrev LineState := Std.Usize × (Array RawM31 4#usize) ×
  (Array (Array Std.U64 4#usize) 3#usize) ×
  (Array (Array RawM31 4#usize) 3#usize)

private theorem vecIndexRun
    (components : alloc.vec.Vec Component) (position : Std.Usize)
    (bound : position.val < components.val.length) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice Component)
        components position = ok components.val[position.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec components position (by simpa using bound))
  have listExact : components.val[position.val] =
      components.val[position.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  rw [alloc.vec.Vec.index_slice_index]
  simpa [exact, listExact] using run

private theorem componentAtSix
    (components : alloc.vec.Vec Component)
    (c0 c1 c2 c3 c4 c5 : Component)
    (componentsExact : components.val = [c0, c1, c2, c3, c4, c5])
    (position : Std.Usize) (positionBound : position.val < 6) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice Component)
        components position =
      ok [c0, c1, c2, c3, c4, c5][position.val]! := by
  have bound : position.val < components.val.length := by
    simpa [componentsExact] using positionBound
  simpa [componentsExact] using vecIndexRun components position bound

private theorem usizeZeroSucc :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (1#usize).hSize; scalar_tac)]
  norm_num

private theorem usizeOneSucc :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#usize).hSize; scalar_tac)]
  norm_num

private theorem usizeTwoSucc :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#usize).hSize; scalar_tac)]
  norm_num

private theorem usizeThreeSucc :
    Std.Usize.wrapping_add 3#usize 1#usize = 4#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#usize).hSize; scalar_tac)]
  norm_num

private theorem usizeFourSucc :
    Std.Usize.wrapping_add 4#usize 1#usize = 5#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (5#usize).hSize; scalar_tac)]
  norm_num

private theorem usizeFiveSucc :
    Std.Usize.wrapping_add 5#usize 1#usize = 6#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (6#usize).hSize; scalar_tac)]
  norm_num

theorem dot_max_deferred_six
    (components : alloc.vec.Vec Component)
    (mScale0 mScale1 tScale0 tScale1 : RawQM31)
    (mPoint0 mPoint1 tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (groupValues : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (deferred : Std.U8)
    (componentsExact : components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Grouped64x16BinaryDeferred rowGroups groupMasks none groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs deferred]) :
    sumcheck.WeightAccumulator.impl.dot_loop0 components 0#u8 0#usize =
      ok deferred := by
  have read0 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 0#usize =
      ok (.Multilinear mScale0 mPoint0) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      0#usize (by norm_num)
  have read1 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 1#usize =
      ok (.Multilinear mScale1 mPoint1) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      1#usize (by norm_num)
  have read2 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 2#usize =
      ok (.Grouped64x16BinaryDeferred rowGroups groupMasks none
        groupValues) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      2#usize (by norm_num)
  have read3 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 3#usize =
      ok (.Tensor tScale0 tFactors0) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      3#usize (by norm_num)
  have read4 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 4#usize =
      ok (.Tensor tScale1 tFactors1) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      4#usize (by norm_num)
  have read5 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 5#usize =
      ok (.LineM31Batch lineScales lineXs deferred) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      5#usize (by norm_num)
  have step0 : sumcheck.WeightAccumulator.impl.dot_loop0.body components
      0#u8 0#usize = ok (cont (0#u8, 1#usize)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop0.body
    simp only [alloc.vec.Vec.len_val]
    rw [if_pos (by simpa [componentsExact]), read0]
    simp [sumcheck.WeightAccumulator.impl.line_batch_deferred_halvings,
      Std.lift, usizeZeroSucc]
  have step1 : sumcheck.WeightAccumulator.impl.dot_loop0.body components
      0#u8 1#usize = ok (cont (0#u8, 2#usize)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop0.body
    simp only [alloc.vec.Vec.len_val]
    rw [if_pos (by simpa [componentsExact]), read1]
    simp [sumcheck.WeightAccumulator.impl.line_batch_deferred_halvings,
      Std.lift, usizeOneSucc]
  have step2 : sumcheck.WeightAccumulator.impl.dot_loop0.body components
      0#u8 2#usize = ok (cont (0#u8, 3#usize)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop0.body
    simp only [alloc.vec.Vec.len_val]
    rw [if_pos (by simpa [componentsExact]), read2]
    simp [sumcheck.WeightAccumulator.impl.line_batch_deferred_halvings,
      Std.lift, usizeTwoSucc]
  have step3 : sumcheck.WeightAccumulator.impl.dot_loop0.body components
      0#u8 3#usize = ok (cont (0#u8, 4#usize)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop0.body
    simp only [alloc.vec.Vec.len_val]
    rw [if_pos (by simpa [componentsExact]), read3]
    simp [sumcheck.WeightAccumulator.impl.line_batch_deferred_halvings,
      Std.lift, usizeThreeSucc]
  have step4 : sumcheck.WeightAccumulator.impl.dot_loop0.body components
      0#u8 4#usize = ok (cont (0#u8, 5#usize)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop0.body
    simp only [alloc.vec.Vec.len_val]
    rw [if_pos (by simpa [componentsExact]), read4]
    simp [sumcheck.WeightAccumulator.impl.line_batch_deferred_halvings,
      Std.lift, usizeFourSucc]
  have step5 : sumcheck.WeightAccumulator.impl.dot_loop0.body components
      0#u8 5#usize = ok (cont (deferred, 6#usize)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop0.body
    simp only [alloc.vec.Vec.len_val]
    rw [if_pos (by simpa [componentsExact]), read5]
    simp only [bind_tc_ok,
      sumcheck.WeightAccumulator.impl.line_batch_deferred_halvings]
    by_cases positive : deferred > 0#u8
    · rw [if_pos positive]
      simp [Std.lift, usizeFiveSucc]
    · rw [if_neg positive]
      have deferredZero : deferred = 0#u8 := by
        apply UScalar.val_eq_imp
        change ¬ 0 < deferred.val at positive
        norm_num
        exact Nat.eq_zero_of_not_pos positive
      subst deferred
      simp [Std.lift, usizeFiveSucc]
  have done : sumcheck.WeightAccumulator.impl.dot_loop0.body components
      deferred 6#usize = ok (done deferred) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop0.body
    simp [componentsExact]
  unfold sumcheck.WeightAccumulator.impl.dot_loop0
  rw [loop.eq_1]
  simp only
  rw [step0]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step1]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step2]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step3]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step4]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step5]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [done]

theorem dot_accumulate_line_six
    (components : alloc.vec.Vec Component)
    (mScale0 mScale1 tScale0 tScale1 : RawQM31)
    (mPoint0 mPoint1 tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (groupValues : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (deferred : Std.U8) (batch : LineState)
    (componentsExact : components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Grouped64x16BinaryDeferred rowGroups groupMasks none groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs deferred])
    (batchRun :
      sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot deferred
          (alloc.vec.Vec.deref lineScales) (alloc.vec.Vec.deref lineXs)
          deferred 0#usize zeroLineConstant zeroLineRaw zeroLineSums =
        ok batch) :
    sumcheck.WeightAccumulator.impl.dot_loop1 components deferred 0#usize
        0#usize zeroLineConstant zeroLineRaw zeroLineSums = ok batch := by
  have read0 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 0#usize =
      ok (.Multilinear mScale0 mPoint0) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      0#usize (by norm_num)
  have read1 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 1#usize =
      ok (.Multilinear mScale1 mPoint1) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      1#usize (by norm_num)
  have read2 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 2#usize =
      ok (.Grouped64x16BinaryDeferred rowGroups groupMasks none
        groupValues) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      2#usize (by norm_num)
  have read3 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 3#usize =
      ok (.Tensor tScale0 tFactors0) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      3#usize (by norm_num)
  have read4 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 4#usize =
      ok (.Tensor tScale1 tFactors1) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      4#usize (by norm_num)
  have read5 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 5#usize =
      ok (.LineM31Batch lineScales lineXs deferred) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      5#usize (by norm_num)
  have step0 : sumcheck.WeightAccumulator.impl.dot_loop1.body components
      deferred 0#usize 0#usize zeroLineConstant zeroLineRaw zeroLineSums =
        ok (cont (1#usize, 0#usize, zeroLineConstant, zeroLineRaw,
          zeroLineSums)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop1.body
    rw [if_pos (by simpa [componentsExact]), read0]
    simp [sumcheck.WeightAccumulator.impl.accumulate_line_component_dot,
      Std.lift, usizeZeroSucc]
  have step1 : sumcheck.WeightAccumulator.impl.dot_loop1.body components
      deferred 1#usize 0#usize zeroLineConstant zeroLineRaw zeroLineSums =
        ok (cont (2#usize, 0#usize, zeroLineConstant, zeroLineRaw,
          zeroLineSums)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop1.body
    rw [if_pos (by simpa [componentsExact]), read1]
    simp [sumcheck.WeightAccumulator.impl.accumulate_line_component_dot,
      Std.lift, usizeOneSucc]
  have step2 : sumcheck.WeightAccumulator.impl.dot_loop1.body components
      deferred 2#usize 0#usize zeroLineConstant zeroLineRaw zeroLineSums =
        ok (cont (3#usize, 0#usize, zeroLineConstant, zeroLineRaw,
          zeroLineSums)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop1.body
    rw [if_pos (by simpa [componentsExact]), read2]
    simp [sumcheck.WeightAccumulator.impl.accumulate_line_component_dot,
      Std.lift, usizeTwoSucc]
  have step3 : sumcheck.WeightAccumulator.impl.dot_loop1.body components
      deferred 3#usize 0#usize zeroLineConstant zeroLineRaw zeroLineSums =
        ok (cont (4#usize, 0#usize, zeroLineConstant, zeroLineRaw,
          zeroLineSums)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop1.body
    rw [if_pos (by simpa [componentsExact]), read3]
    simp [sumcheck.WeightAccumulator.impl.accumulate_line_component_dot,
      Std.lift, usizeThreeSucc]
  have step4 : sumcheck.WeightAccumulator.impl.dot_loop1.body components
      deferred 4#usize 0#usize zeroLineConstant zeroLineRaw zeroLineSums =
        ok (cont (5#usize, 0#usize, zeroLineConstant, zeroLineRaw,
          zeroLineSums)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop1.body
    rw [if_pos (by simpa [componentsExact]), read4]
    simp [sumcheck.WeightAccumulator.impl.accumulate_line_component_dot,
      Std.lift, usizeFourSucc]
  have step5 : sumcheck.WeightAccumulator.impl.dot_loop1.body components
      deferred 5#usize 0#usize zeroLineConstant zeroLineRaw zeroLineSums =
        ok (cont (6#usize, batch.1, batch.2.1, batch.2.2.1,
          batch.2.2.2)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop1.body
    rw [if_pos (by simpa [componentsExact]), read5]
    simp only [bind_tc_ok,
      sumcheck.WeightAccumulator.impl.accumulate_line_component_dot]
    rw [batchRun]
    simp [Std.lift, usizeFiveSucc]
  have done : sumcheck.WeightAccumulator.impl.dot_loop1.body components
      deferred 6#usize batch.1 batch.2.1 batch.2.2.1 batch.2.2.2 =
        ok (done batch) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop1.body
    simp [componentsExact]
  unfold sumcheck.WeightAccumulator.impl.dot_loop1
  rw [loop.eq_1]
  simp only
  rw [step0]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step1]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step2]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step3]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step4]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [step5]
  simp only [bind_tc_ok]
  rw [loop.eq_1]
  simp only
  rw [done]

#print axioms dot_max_deferred_six
#print axioms dot_accumulate_line_six

end V7CallerCurrentReleaseR26TerminalDotLineTraversal
