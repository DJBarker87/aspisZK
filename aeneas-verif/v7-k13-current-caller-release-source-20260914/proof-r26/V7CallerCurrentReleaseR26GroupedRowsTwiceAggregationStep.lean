import V7CallerCurrentReleaseR26GroupedRowsTwiceFourTrace

/-!
# Symbolic steps of the optimized sixteen-slot aggregation

These lemmas isolate one search edge and one source aggregation edge.  Fixed
release chunks can therefore be replayed as sixteen named transitions without
unfolding the complete nested loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceAggregationStep

abbrev RawQM31 := field.QM31

theorem arrayIndexExact
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize)
    (bound : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem (by rw [values.property]; exact bound)]
  apply congrArg Result.ok
  symm
  apply List.getElem!_of_getElem?
  simp [bound]

theorem sliceIndexExact
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (bound : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [bound]

theorem arrayUpdateExact
    {T : Type} {N : Std.Usize} (values : Array T N)
    (index : Std.Usize) (bound : index.val < N.val) (value : T) :
    Array.update values index value = ok (values.set index value) := by
  unfold Array.update
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem (by rw [values.property]; exact bound)]
  apply congrArg Result.ok
  apply Subtype.ext
  rfl

theorem castUsizeToU8Exact (value : Std.Usize) (output : Std.U8)
    (valueExact : value.val = output.val)
    (small : value.val < 2 ^ UScalarTy.U8.numBits) :
    UScalar.cast .U8 value = output := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt small]
  exact valueExact

theorem usizeWrappingSuccExact (value output : Std.Usize)
    (valueExact : value.val + 1 = output.val)
    (small : value.val + 1 < UScalar.size .Usize) :
    Std.Usize.wrapping_add value 1#usize = output := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq]
  have oneExact : (1#usize).val = 1 := rfl
  rw [oneExact, Nat.mod_eq_of_lt small]
  exact valueExact

theorem u8WrappingSuccExact (value output : Std.U8)
    (valueExact : value.val + 1 = output.val)
    (small : value.val + 1 < UScalar.size .U8) :
    Std.U8.wrapping_add value 1#u8 = output := by
  apply UScalar.val_eq_imp
  rw [Std.U8.wrapping_add_val_eq]
  have oneExact : (1#u8).val = 1 := rfl
  rw [oneExact, Nat.mod_eq_of_lt small]
  exact valueExact

private theorem searchBodyNext
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (group found : Std.U8) (position next : Std.Usize)
    (active : position < uniqueLength)
    (readRun : Array.index_usize uniqueGroups position = ok found)
    (different : found ≠ group)
    (nextRun : Std.Usize.wrapping_add position 1#usize = next) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0.body uniqueGroups
      uniqueLength group position = ok (cont next) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0.body
  rw [if_pos active, readRun]
  simp only [bind_tc_ok, bne_iff_ne, ne_eq, UScalar.neq_to_neq_val]
  have differentVal : found.val ≠ group.val := by
    intro same
    apply different
    exact UScalar.val_eq_imp found group same
  rw [if_pos differentVal]
  simp only [Std.lift, nextRun, bind_tc_ok]

private theorem searchBodyDoneMatch
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (group : Std.U8) (position : Std.Usize)
    (active : position < uniqueLength)
    (readRun : Array.index_usize uniqueGroups position = ok group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0.body uniqueGroups
      uniqueLength group position = ok (done position) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0.body
  rw [if_pos active, readRun]
  simp

private theorem searchBodyDoneEnd
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength position : Std.Usize)
    (finished : ¬ position < uniqueLength) (group : Std.U8) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0.body uniqueGroups
      uniqueLength group position = ok (done position) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0.body
  rw [if_neg finished]

theorem searchEmpty
    (uniqueGroups : Array Std.U8 16#usize) (group : Std.U8) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups 0#usize
      group 0#usize = ok 0#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyDoneEnd uniqueGroups 0#usize 0#usize
    (by decide) group]

theorem searchAt0
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (group : Std.U8) (active0 : 0#usize < uniqueLength)
    (read0 : Array.index_usize uniqueGroups 0#usize = ok group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups uniqueLength
      group 0#usize = ok 0#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyDoneMatch uniqueGroups uniqueLength group 0#usize
    active0 read0]

private theorem zeroSucc :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (1#usize).hSize; scalar_tac)]
  norm_num
private theorem oneSucc :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#usize).hSize; scalar_tac)]
  norm_num
private theorem twoSucc :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#usize).hSize; scalar_tac)]
  norm_num
private theorem threeSucc :
    Std.Usize.wrapping_add 3#usize 1#usize = 4#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#usize).hSize; scalar_tac)]
  norm_num

theorem searchAt1
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (group found0 : Std.U8) (active0 : 0#usize < uniqueLength)
    (active1 : 1#usize < uniqueLength)
    (read0 : Array.index_usize uniqueGroups 0#usize = ok found0)
    (different0 : found0 ≠ group)
    (read1 : Array.index_usize uniqueGroups 1#usize = ok group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups uniqueLength
      group 0#usize = ok 1#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found0
    0#usize 1#usize active0 read0 different0 zeroSucc]
  simp only
  rw [loop.eq_1, searchBodyDoneMatch uniqueGroups uniqueLength group 1#usize
    active1 read1]

theorem searchAt2
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (group found0 found1 : Std.U8)
    (active0 : 0#usize < uniqueLength) (active1 : 1#usize < uniqueLength)
    (active2 : 2#usize < uniqueLength)
    (read0 : Array.index_usize uniqueGroups 0#usize = ok found0)
    (read1 : Array.index_usize uniqueGroups 1#usize = ok found1)
    (different0 : found0 ≠ group) (different1 : found1 ≠ group)
    (read2 : Array.index_usize uniqueGroups 2#usize = ok group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups uniqueLength
      group 0#usize = ok 2#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found0
    0#usize 1#usize active0 read0 different0 zeroSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found1
    1#usize 2#usize active1 read1 different1 oneSucc]
  simp only
  rw [loop.eq_1, searchBodyDoneMatch uniqueGroups uniqueLength group 2#usize
    active2 read2]

theorem searchAt3
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (group found0 found1 found2 : Std.U8)
    (active0 : 0#usize < uniqueLength) (active1 : 1#usize < uniqueLength)
    (active2 : 2#usize < uniqueLength) (active3 : 3#usize < uniqueLength)
    (read0 : Array.index_usize uniqueGroups 0#usize = ok found0)
    (read1 : Array.index_usize uniqueGroups 1#usize = ok found1)
    (read2 : Array.index_usize uniqueGroups 2#usize = ok found2)
    (different0 : found0 ≠ group) (different1 : found1 ≠ group)
    (different2 : found2 ≠ group)
    (read3 : Array.index_usize uniqueGroups 3#usize = ok group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups uniqueLength
      group 0#usize = ok 3#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found0
    0#usize 1#usize active0 read0 different0 zeroSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found1
    1#usize 2#usize active1 read1 different1 oneSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found2
    2#usize 3#usize active2 read2 different2 twoSucc]
  simp only
  rw [loop.eq_1, searchBodyDoneMatch uniqueGroups uniqueLength group 3#usize
    active3 read3]

theorem searchAt4
    (uniqueGroups : Array Std.U8 16#usize) (uniqueLength : Std.Usize)
    (group found0 found1 found2 found3 : Std.U8)
    (active0 : 0#usize < uniqueLength) (active1 : 1#usize < uniqueLength)
    (active2 : 2#usize < uniqueLength) (active3 : 3#usize < uniqueLength)
    (active4 : 4#usize < uniqueLength)
    (read0 : Array.index_usize uniqueGroups 0#usize = ok found0)
    (read1 : Array.index_usize uniqueGroups 1#usize = ok found1)
    (read2 : Array.index_usize uniqueGroups 2#usize = ok found2)
    (read3 : Array.index_usize uniqueGroups 3#usize = ok found3)
    (different0 : found0 ≠ group) (different1 : found1 ≠ group)
    (different2 : found2 ≠ group) (different3 : found3 ≠ group)
    (read4 : Array.index_usize uniqueGroups 4#usize = ok group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups uniqueLength
      group 0#usize = ok 4#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found0
    0#usize 1#usize active0 read0 different0 zeroSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found1
    1#usize 2#usize active1 read1 different1 oneSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found2
    2#usize 3#usize active2 read2 different2 twoSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups uniqueLength group found3
    3#usize 4#usize active3 read3 different3 threeSucc]
  simp only
  rw [loop.eq_1, searchBodyDoneMatch uniqueGroups uniqueLength group 4#usize
    active4 read4]

theorem searchNew1
    (uniqueGroups : Array Std.U8 16#usize) (group found0 : Std.U8)
    (read0 : Array.index_usize uniqueGroups 0#usize = ok found0)
    (different0 : found0 ≠ group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups 1#usize
      group 0#usize = ok 1#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyNext uniqueGroups 1#usize group found0
    0#usize 1#usize (by decide) read0 different0 zeroSucc]
  simp only
  rw [loop.eq_1, searchBodyDoneEnd uniqueGroups 1#usize 1#usize
    (by decide) group]

theorem searchNew2
    (uniqueGroups : Array Std.U8 16#usize) (group found0 found1 : Std.U8)
    (read0 : Array.index_usize uniqueGroups 0#usize = ok found0)
    (read1 : Array.index_usize uniqueGroups 1#usize = ok found1)
    (different0 : found0 ≠ group) (different1 : found1 ≠ group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups 2#usize
      group 0#usize = ok 2#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyNext uniqueGroups 2#usize group found0
    0#usize 1#usize (by decide) read0 different0 zeroSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups 2#usize group found1
    1#usize 2#usize (by decide) read1 different1 oneSucc]
  simp only
  rw [loop.eq_1, searchBodyDoneEnd uniqueGroups 2#usize 2#usize
    (by decide) group]

theorem searchNew3
    (uniqueGroups : Array Std.U8 16#usize)
    (group found0 found1 found2 : Std.U8)
    (read0 : Array.index_usize uniqueGroups 0#usize = ok found0)
    (read1 : Array.index_usize uniqueGroups 1#usize = ok found1)
    (read2 : Array.index_usize uniqueGroups 2#usize = ok found2)
    (different0 : found0 ≠ group) (different1 : found1 ≠ group)
    (different2 : found2 ≠ group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups 3#usize
      group 0#usize = ok 3#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyNext uniqueGroups 3#usize group found0
    0#usize 1#usize (by decide) read0 different0 zeroSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups 3#usize group found1
    1#usize 2#usize (by decide) read1 different1 oneSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups 3#usize group found2
    2#usize 3#usize (by decide) read2 different2 twoSucc]
  simp only
  rw [loop.eq_1, searchBodyDoneEnd uniqueGroups 3#usize 3#usize
    (by decide) group]

theorem searchNew4
    (uniqueGroups : Array Std.U8 16#usize)
    (group found0 found1 found2 found3 : Std.U8)
    (read0 : Array.index_usize uniqueGroups 0#usize = ok found0)
    (read1 : Array.index_usize uniqueGroups 1#usize = ok found1)
    (read2 : Array.index_usize uniqueGroups 2#usize = ok found2)
    (read3 : Array.index_usize uniqueGroups 3#usize = ok found3)
    (different0 : found0 ≠ group) (different1 : found1 ≠ group)
    (different2 : found2 ≠ group) (different3 : found3 ≠ group) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0 uniqueGroups 4#usize
      group 0#usize = ok 4#usize := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
  rw [loop.eq_1, searchBodyNext uniqueGroups 4#usize group found0
    0#usize 1#usize (by decide) read0 different0 zeroSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups 4#usize group found1
    1#usize 2#usize (by decide) read1 different1 oneSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups 4#usize group found2
    2#usize 3#usize (by decide) read2 different2 twoSucc]
  simp only
  rw [loop.eq_1, searchBodyNext uniqueGroups 4#usize group found3
    3#usize 4#usize (by decide) read3 different3 threeSucc]
  simp only
  rw [loop.eq_1, searchBodyDoneEnd uniqueGroups 4#usize 4#usize
    (by decide) group]

theorem aggregationNewStep
    (basis : Array RawQM31 16#usize) (chunk : Slice Std.U8)
    (uniqueGroups uniqueGroupsOut : Array Std.U8 16#usize)
    (coefficients coefficientsOut : Array RawQM31 16#usize)
    (counts countsOut : Array Std.U8 16#usize)
    (firstSlots firstSlotsOut : Array Std.U8 16#usize)
    (uniqueLength uniqueLengthOut slot slotOut : Std.Usize)
    (group slotU8 : Std.U8) (coefficient : RawQM31)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk slot = ok group)
    (searchRun : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueGroups uniqueLength group 0#usize = ok uniqueLength)
    (uniqueUpdate : Array.update uniqueGroups uniqueLength group =
      ok uniqueGroupsOut)
    (basisRun : Array.index_usize basis slot = ok coefficient)
    (coefficientUpdate : Array.update coefficients uniqueLength coefficient =
      ok coefficientsOut)
    (countUpdate : Array.update counts uniqueLength 1#u8 = ok countsOut)
    (slotCast : UScalar.cast .U8 slot = slotU8)
    (firstSlotUpdate : Array.update firstSlots uniqueLength slotU8 =
      ok firstSlotsOut)
    (uniqueLengthSucc : Std.Usize.wrapping_add uniqueLength 1#usize =
      uniqueLengthOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk uniqueGroups
      coefficients counts firstSlots uniqueLength slot =
    ok (cont (uniqueGroupsOut, coefficientsOut, countsOut, firstSlotsOut,
      uniqueLengthOut, slotOut)) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0.body
  rw [if_pos slotActive, groupRun]
  simp only [bind_tc_ok]
  rw [searchRun]
  simp only [bind_tc_ok, ite_true]
  rw [uniqueUpdate]
  simp only [bind_tc_ok]
  rw [basisRun]
  simp only [bind_tc_ok]
  rw [coefficientUpdate]
  simp only [bind_tc_ok]
  rw [countUpdate]
  simp only [bind_tc_ok, Std.lift, slotCast, firstSlotUpdate]
  simp only [bind_tc_ok, uniqueLengthSucc, slotSucc]

theorem aggregationExistingStep
    (basis : Array RawQM31 16#usize) (chunk : Slice Std.U8)
    (uniqueGroups : Array Std.U8 16#usize)
    (coefficients coefficientsOut : Array RawQM31 16#usize)
    (counts countsOut : Array Std.U8 16#usize)
    (firstSlots : Array Std.U8 16#usize)
    (uniqueLength position slot slotOut : Std.Usize)
    (group count countOut : Std.U8)
    (coefficient basisValue coefficientOut : RawQM31)
    (slotActive : slot < 16#usize)
    (groupRun : Slice.index_usize chunk slot = ok group)
    (searchRun : sumcheck.fold_grouped_rows_twice_loop0_loop0_loop0
      uniqueGroups uniqueLength group 0#usize = ok position)
    (positionExisting : position ≠ uniqueLength)
    (coefficientRead : Array.index_usize coefficients position =
      ok coefficient)
    (basisRun : Array.index_usize basis slot = ok basisValue)
    (addRun : field.QM31.add coefficient basisValue = ok coefficientOut)
    (coefficientUpdate : Array.update coefficients position coefficientOut =
      ok coefficientsOut)
    (countRead : Array.index_usize counts position = ok count)
    (countSucc : Std.U8.wrapping_add count 1#u8 = countOut)
    (countUpdate : Array.update counts position countOut = ok countsOut)
    (slotSucc : Std.Usize.wrapping_add slot 1#usize = slotOut) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk uniqueGroups
      coefficients counts firstSlots uniqueLength slot =
    ok (cont (uniqueGroups, coefficientsOut, countsOut, firstSlots,
      uniqueLength, slotOut)) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0.body
  rw [if_pos slotActive, groupRun]
  simp only [bind_tc_ok]
  rw [searchRun]
  simp only [bind_tc_ok, if_neg positionExisting]
  rw [coefficientRead, basisRun]
  simp only [bind_tc_ok]
  rw [addRun]
  simp only [bind_tc_ok]
  rw [coefficientUpdate]
  simp only [bind_tc_ok]
  rw [countRead]
  simp only [bind_tc_ok, Std.lift, countSucc, countUpdate]
  simp only [bind_tc_ok, slotSucc]

theorem aggregationDone
    (basis : Array RawQM31 16#usize) (chunk : Slice Std.U8)
    (uniqueGroups : Array Std.U8 16#usize)
    (coefficients : Array RawQM31 16#usize)
    (counts firstSlots : Array Std.U8 16#usize)
    (uniqueLength : Std.Usize) :
    sumcheck.fold_grouped_rows_twice_loop0_loop0.body basis chunk uniqueGroups
      coefficients counts firstSlots uniqueLength 16#usize =
    ok (done (uniqueGroups, coefficients, counts, firstSlots,
      uniqueLength)) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0_loop0.body
  rw [if_neg (by decide)]

#print axioms searchAt4
#print axioms searchNew4
#print axioms aggregationNewStep
#print axioms aggregationExistingStep

end V7CallerCurrentReleaseR26GroupedRowsTwiceAggregationStep
