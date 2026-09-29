import V7CallerCurrentReleaseR26TerminalStructuredComponents

/-!
# Terminal dot semantics for the released grouped component

At log length two the released row-group vector is `[0, 1, 2, 3]`.
The generated terminal loop therefore evaluates the represented grouped
weight vector against the four terminal values in source order.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalGroupedComponent

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsStaged
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open V7CallerCurrentReleaseR26TerminalStructuredComponents
open AspisV5FriRelationCandidateBridge
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity

abbrev RawQM31 := field.QM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

private theorem sliceIndexRun
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (bound : index.val < values.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec values index (by simpa using bound))
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  simpa [exact, listExact] using run

private theorem fromU8ToUsizeExact (value : Std.U8) :
    core.convert.num.FromUsizeU8.from value = UScalar.cast .Usize value := by
  apply UScalar.val_eq_imp
  rw [core.convert.num.FromUsizeU8.from_val_eq, UScalar.cast_val_eq]
  rw [Nat.mod_eq_of_lt]
  have h := value.hBounds
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [UScalarTy.numBits, hbits] at h ⊢ <;> omega

@[simp] private theorem castU8ToUsizeVal (value : Std.U8) :
    (UScalar.cast .Usize value).val = value.val := by
  rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
  have h := value.hBounds
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [UScalarTy.numBits, hbits] at h ⊢ <;> omega

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

private theorem groupedBodyStep
    (values : Slice RawQM31) (rowGroups : Slice Std.U8)
    (groupValues : Slice RawQM31) (sum value groupValue product next : RawQM31)
    (index groupIndex nextIndex : Std.Usize) (group : Std.U8)
    (active : index < Slice.len values)
    (valueRead : Slice.index_usize values index = ok value)
    (groupRead : Slice.index_usize rowGroups index = ok group)
    (groupCast : UScalar.cast .Usize group = groupIndex)
    (groupValueRead : Slice.index_usize groupValues groupIndex = ok groupValue)
    (mulRun : field.QM31.mul value groupValue = ok product)
    (addRun : field.QM31.add sum product = ok next)
    (succ : Std.Usize.wrapping_add index 1#usize = nextIndex) :
    sumcheck.WeightAccumulator.impl.dot_grouped_binary_terminal_loop.body
        values rowGroups groupValues sum index = ok (cont (next, nextIndex)) := by
  unfold sumcheck.WeightAccumulator.impl.dot_grouped_binary_terminal_loop.body
  rw [if_pos active, valueRead, groupRead]
  simp only [bind_tc_ok, Std.lift]
  rw [fromU8ToUsizeExact, groupCast, groupValueRead]
  simp only [bind_tc_ok]
  rw [mulRun]
  simp only [bind_tc_ok]
  rw [addRun, succ]
  simp

private theorem groupedBodyDone
    (values : Slice RawQM31) (rowGroups : Slice Std.U8)
    (groupValues : Slice RawQM31) (sum : RawQM31) (index : Std.Usize)
    (done : ¬ index < Slice.len values) :
    sumcheck.WeightAccumulator.impl.dot_grouped_binary_terminal_loop.body
        values rowGroups groupValues sum index = ok (ControlFlow.done sum) := by
  unfold sumcheck.WeightAccumulator.impl.dot_grouped_binary_terminal_loop.body
  rw [if_neg done]

private theorem generatedZeroExact :
    generatedQm31ToExact field.QM31.ZERO = 0 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact, field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact, field.QM31.ZERO]

private theorem groupedTerminalExact
    (values : Slice RawQM31) (g0 g1 g2 g3 : RawQM31)
    (valuesLength : values.length = 4) :
    candidateClaim
        (representedGroupedWeights releasedRowGroups4
          (releasedFourValues g0 g1 g2 g3))
        (terminalValues values) =
      exactRaw values.val[0]! * exactRaw g0 +
      exactRaw values.val[1]! * exactRaw g1 +
      exactRaw values.val[2]! * exactRaw g2 +
      exactRaw values.val[3]! * exactRaw g3 := by
  unfold candidateClaim
  rw [Fin.sum_univ_four]
  simp [representedGroupedWeights, releasedRowGroups4, releasedFourValues,
    terminalValues, valuesLength]

theorem dot_terminal_released_grouped_corresponds
    (values : Slice RawQM31) (groupMasks : alloc.vec.Vec Std.U16)
    (g0 g1 g2 g3 : RawQM31)
    (valuesCanonical : CanonicalSlice values)
    (valuesLength : values.length = 4)
    (groupsCanonical : CanonicalFour g0 g1 g2 g3) :
    ∃ out,
      sumcheck.WeightAccumulator.impl.dot_terminal_component
          (.Grouped64x16BinaryDeferred releasedRowGroups4
            groupMasks none (releasedFourValues g0 g1 g2 g3)) values = ok out ∧
      GeneratedCanonicalQM31 out ∧
      exactRaw out =
        candidateClaim
          (representedGroupedWeights releasedRowGroups4
            (releasedFourValues g0 g1 g2 g3))
          (terminalValues values) := by
  let v0 := values.val[0]!
  let v1 := values.val[1]!
  let v2 := values.val[2]!
  let v3 := values.val[3]!
  have readV0 : Slice.index_usize values 0#usize = ok v0 := by
    simpa [v0] using sliceIndexRun values 0#usize (by simpa [valuesLength])
  have readV1 : Slice.index_usize values 1#usize = ok v1 := by
    simpa [v1] using sliceIndexRun values 1#usize (by simpa [valuesLength])
  have readV2 : Slice.index_usize values 2#usize = ok v2 := by
    simpa [v2] using sliceIndexRun values 2#usize (by simpa [valuesLength])
  have readV3 : Slice.index_usize values 3#usize = ok v3 := by
    simpa [v3] using sliceIndexRun values 3#usize (by simpa [valuesLength])
  have cv0 : GeneratedCanonicalQM31 v0 :=
    valuesCanonical 0 (by simpa [valuesLength])
  have cv1 : GeneratedCanonicalQM31 v1 :=
    valuesCanonical 1 (by simpa [valuesLength])
  have cv2 : GeneratedCanonicalQM31 v2 :=
    valuesCanonical 2 (by simpa [valuesLength])
  have cv3 : GeneratedCanonicalQM31 v3 :=
    valuesCanonical 3 (by simpa [valuesLength])
  rcases groupsCanonical with ⟨cg0, cg1, cg2, cg3⟩
  obtain ⟨p0, hp0, cp0, ep0⟩ :=
    generated_qm31_mul_corresponds v0 g0 cv0 cg0
  obtain ⟨s0, hs0, cs0, es0⟩ :=
    generated_qm31_add_corresponds field.QM31.ZERO p0
      (by
        norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
          AspisAeneasCM31Multiplicative.CanonicalRawM31, field.QM31.ZERO]) cp0
  obtain ⟨p1, hp1, cp1, ep1⟩ :=
    generated_qm31_mul_corresponds v1 g1 cv1 cg1
  obtain ⟨s1, hs1, cs1, es1⟩ :=
    generated_qm31_add_corresponds s0 p1 cs0 cp1
  obtain ⟨p2, hp2, cp2, ep2⟩ :=
    generated_qm31_mul_corresponds v2 g2 cv2 cg2
  obtain ⟨s2, hs2, cs2, es2⟩ :=
    generated_qm31_add_corresponds s1 p2 cs1 cp2
  obtain ⟨p3, hp3, cp3, ep3⟩ :=
    generated_qm31_mul_corresponds v3 g3 cv3 cg3
  obtain ⟨s3, hs3, cs3, es3⟩ :=
    generated_qm31_add_corresponds s2 p3 cs2 cp3
  have run :
      sumcheck.WeightAccumulator.impl.dot_grouped_binary_terminal
          values (alloc.vec.Vec.deref releasedRowGroups4)
            (alloc.vec.Vec.deref (releasedFourValues g0 g1 g2 g3)) = ok s3 := by
    unfold sumcheck.WeightAccumulator.impl.dot_grouped_binary_terminal
    unfold sumcheck.WeightAccumulator.impl.dot_grouped_binary_terminal_loop
    rw [loop.eq_1]
    dsimp only
    rw [groupedBodyStep values (alloc.vec.Vec.deref releasedRowGroups4)
      (alloc.vec.Vec.deref (releasedFourValues g0 g1 g2 g3))
      field.QM31.ZERO v0 g0 p0 s0 0#usize 0#usize 1#usize 0#u8
      (by simpa [valuesLength]) readV0
      (by simp [releasedRowGroups4, alloc.vec.Vec.deref, Slice.index_usize])
      (by apply UScalar.val_eq_imp; simp)
      (by simp [releasedFourValues, alloc.vec.Vec.deref, Slice.index_usize])
      hp0 hs0 usizeZeroSucc]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    dsimp only
    rw [groupedBodyStep values (alloc.vec.Vec.deref releasedRowGroups4)
      (alloc.vec.Vec.deref (releasedFourValues g0 g1 g2 g3))
      s0 v1 g1 p1 s1 1#usize 1#usize 2#usize 1#u8
      (by simpa [valuesLength]) readV1
      (by simp [releasedRowGroups4, alloc.vec.Vec.deref, Slice.index_usize])
      (by apply UScalar.val_eq_imp; simp)
      (by simp [releasedFourValues, alloc.vec.Vec.deref, Slice.index_usize])
      hp1 hs1 usizeOneSucc]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    dsimp only
    rw [groupedBodyStep values (alloc.vec.Vec.deref releasedRowGroups4)
      (alloc.vec.Vec.deref (releasedFourValues g0 g1 g2 g3))
      s1 v2 g2 p2 s2 2#usize 2#usize 3#usize 2#u8
      (by simpa [valuesLength]) readV2
      (by simp [releasedRowGroups4, alloc.vec.Vec.deref, Slice.index_usize])
      (by apply UScalar.val_eq_imp; simp)
      (by simp [releasedFourValues, alloc.vec.Vec.deref, Slice.index_usize])
      hp2 hs2 usizeTwoSucc]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    dsimp only
    rw [groupedBodyStep values (alloc.vec.Vec.deref releasedRowGroups4)
      (alloc.vec.Vec.deref (releasedFourValues g0 g1 g2 g3))
      s2 v3 g3 p3 s3 3#usize 3#usize 4#usize 3#u8
      (by simpa [valuesLength]) readV3
      (by simp [releasedRowGroups4, alloc.vec.Vec.deref, Slice.index_usize])
      (by apply UScalar.val_eq_imp; simp)
      (by simp [releasedFourValues, alloc.vec.Vec.deref, Slice.index_usize])
      hp3 hs3 usizeThreeSucc]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    dsimp only
    rw [groupedBodyDone values (alloc.vec.Vec.deref releasedRowGroups4)
      (alloc.vec.Vec.deref (releasedFourValues g0 g1 g2 g3)) s3 4#usize
      (by
        intro active
        rw [UScalar.lt_equiv, Slice.len_val] at active
        simpa [valuesLength] using active)]
  refine ⟨s3, ?_, cs3, ?_⟩
  · simpa [sumcheck.WeightAccumulator.impl.dot_terminal_component,
      alloc.vec.Vec.deref] using run
  · unfold exactRaw
    rw [es3, es2, es1, es0, ep0, ep1, ep2, ep3]
    simp only [sourceQm31ToModel_add, sourceQm31ToModel_mul]
    rw [groupedTerminalExact values g0 g1 g2 g3 valuesLength]
    rw [generatedZeroExact, sourceQm31ToModel_zero]
    change
      0 + exactRaw v0 * exactRaw g0 + exactRaw v1 * exactRaw g1 +
        exactRaw v2 * exactRaw g2 + exactRaw v3 * exactRaw g3 =
      exactRaw v0 * exactRaw g0 + exactRaw v1 * exactRaw g1 +
        exactRaw v2 * exactRaw g2 + exactRaw v3 * exactRaw g3
    ring

#print axioms dot_terminal_released_grouped_corresponds

end V7CallerCurrentReleaseR26TerminalGroupedComponent
