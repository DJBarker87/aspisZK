import V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3

/-!
# Symbolic contribution steps for the optimized grouped fold

These lemmas isolate the three branches of the generated contribution loop:
the singleton-at-slot-zero shortcut, a repeated slot-zero group, and an
ordinary weighted group.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceContributionStep

abbrev RawQM31 := field.QM31

theorem fromU8ToUsizeExact (value : Std.U8) :
    core.convert.num.FromUsizeU8.from value = UScalar.cast .Usize value := by
  apply UScalar.val_eq_imp
  rw [core.convert.num.FromUsizeU8.from_val_eq, UScalar.cast_val_eq]
  rw [Nat.mod_eq_of_lt]
  have h := value.hBounds
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [UScalarTy.numBits, hbits] at h ⊢ <;> omega

theorem contributionSpecialStep
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 16#usize)
    (coefficients : Array RawQM31 16#usize)
    (counts firstSlots : Array Std.U8 16#usize)
    (uniqueLength position positionOut : Std.Usize)
    (group : Std.U8) (groupIndex : Std.Usize)
    (value groupValue valueOut : RawQM31)
    (active : position < uniqueLength)
    (uniqueRead : Array.index_usize uniqueGroups position = ok group)
    (groupCast : UScalar.cast .Usize group = groupIndex)
    (groupValueRead : Slice.index_usize groupValues groupIndex = ok groupValue)
    (firstSlotRead : Array.index_usize firstSlots position = ok 0#u8)
    (countRead : Array.index_usize counts position = ok 1#u8)
    (addRun : field.QM31.add value groupValue = ok valueOut)
    (positionSucc : Std.Usize.wrapping_add position 1#usize = positionOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop1.body groupValues uniqueGroups
      coefficients counts firstSlots uniqueLength value position =
    ok (cont (valueOut, positionOut)) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop1.body
  rw [if_pos active, uniqueRead]
  simp only [bind_tc_ok, Std.lift, fromU8ToUsizeExact, groupCast,
    groupValueRead, firstSlotRead]
  simp only [if_true]
  rw [countRead]
  simp only [bind_tc_ok, if_true]
  rw [addRun]
  simp only [bind_tc_ok, Std.lift, positionSucc]

theorem contributionRepeatedZeroStep
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 16#usize)
    (coefficients : Array RawQM31 16#usize)
    (counts firstSlots : Array Std.U8 16#usize)
    (uniqueLength position positionOut : Std.Usize)
    (group count : Std.U8) (groupIndex : Std.Usize)
    (value groupValue coefficient product valueOut : RawQM31)
    (active : position < uniqueLength)
    (uniqueRead : Array.index_usize uniqueGroups position = ok group)
    (groupCast : UScalar.cast .Usize group = groupIndex)
    (groupValueRead : Slice.index_usize groupValues groupIndex = ok groupValue)
    (firstSlotRead : Array.index_usize firstSlots position = ok 0#u8)
    (countRead : Array.index_usize counts position = ok count)
    (countNotOne : count ≠ 1#u8)
    (coefficientRead : Array.index_usize coefficients position = ok coefficient)
    (mulRun : field.QM31.mul groupValue coefficient = ok product)
    (addRun : field.QM31.add value product = ok valueOut)
    (positionSucc : Std.Usize.wrapping_add position 1#usize = positionOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop1.body groupValues uniqueGroups
      coefficients counts firstSlots uniqueLength value position =
    ok (cont (valueOut, positionOut)) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop1.body
  rw [if_pos active, uniqueRead]
  simp only [bind_tc_ok, Std.lift, fromU8ToUsizeExact, groupCast,
    groupValueRead, firstSlotRead]
  simp only [if_true]
  rw [countRead]
  simp only [bind_tc_ok, if_neg countNotOne]
  rw [coefficientRead]
  simp only [bind_tc_ok]
  rw [mulRun]
  simp only [bind_tc_ok]
  rw [addRun]
  simp only [bind_tc_ok, Std.lift, positionSucc]

theorem contributionWeightedStep
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 16#usize)
    (coefficients : Array RawQM31 16#usize)
    (counts firstSlots : Array Std.U8 16#usize)
    (uniqueLength position positionOut : Std.Usize)
    (group firstSlot : Std.U8) (groupIndex : Std.Usize)
    (value groupValue coefficient product valueOut : RawQM31)
    (active : position < uniqueLength)
    (uniqueRead : Array.index_usize uniqueGroups position = ok group)
    (groupCast : UScalar.cast .Usize group = groupIndex)
    (groupValueRead : Slice.index_usize groupValues groupIndex = ok groupValue)
    (firstSlotRead : Array.index_usize firstSlots position = ok firstSlot)
    (firstSlotNonzero : firstSlot ≠ 0#u8)
    (coefficientRead : Array.index_usize coefficients position = ok coefficient)
    (mulRun : field.QM31.mul groupValue coefficient = ok product)
    (addRun : field.QM31.add value product = ok valueOut)
    (positionSucc : Std.Usize.wrapping_add position 1#usize = positionOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop1.body groupValues uniqueGroups
      coefficients counts firstSlots uniqueLength value position =
    ok (cont (valueOut, positionOut)) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop1.body
  rw [if_pos active, uniqueRead]
  simp only [bind_tc_ok, Std.lift, fromU8ToUsizeExact, groupCast,
    groupValueRead, firstSlotRead]
  rw [if_neg firstSlotNonzero, coefficientRead]
  simp only [bind_tc_ok]
  rw [mulRun]
  simp only [bind_tc_ok]
  rw [addRun]
  simp only [bind_tc_ok, Std.lift, positionSucc]

theorem contributionDone
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 16#usize)
    (coefficients : Array RawQM31 16#usize)
    (counts firstSlots : Array Std.U8 16#usize)
    (uniqueLength position : Std.Usize) (value : RawQM31)
    (finished : ¬ position < uniqueLength) :
    sumcheck.fold_grouped_rows_twice_loop0_loop1.body groupValues uniqueGroups
      coefficients counts firstSlots uniqueLength value position = ok (done value) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop1.body
  rw [if_neg finished]

#print axioms contributionSpecialStep
#print axioms contributionRepeatedZeroStep
#print axioms contributionWeightedStep
#print axioms contributionDone

end V7CallerCurrentReleaseR26GroupedRowsTwiceContributionStep
