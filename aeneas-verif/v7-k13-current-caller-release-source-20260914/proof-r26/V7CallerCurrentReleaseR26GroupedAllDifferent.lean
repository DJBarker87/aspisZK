import V7CallerCurrentReleaseR26GroupedFirstPair

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26HalfBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26GroupedAllSame
open V7CallerCurrentReleaseR26GroupedPairPair
open V7CallerCurrentReleaseR26GroupedTripleFirst
open V7CallerCurrentReleaseR26GroupedOneThree
open V7CallerCurrentReleaseR26GroupedThreeAround
open V7CallerCurrentReleaseR26GroupedLastPair

namespace V7CallerCurrentReleaseR26GroupedAllDifferent

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def groupsAllDifferent
    (group0 group1 group2 group3 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group2, group3]

private def allDifferentCoefficients
    (alpha alpha2 alpha3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    field.QM31.ONE, alpha3, alpha2, alpha]

private def allDifferentCounts : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 1#u8, 1#u8]

private def allDifferentFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 2#u8, 3#u8]

private theorem allDifferentFindFourthStep0
    (group0 group1 group2 group3 : Std.U8) (different03 : group0 ≠ group3) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (lastPairUnique3 group0 group1 group2) 3#usize group3 0#usize =
      ok (cont 1#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 0#usize =
        ok group0 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index0 group0 group1 group2 0#u8)
  have differentVal : group0.val ≠ group3.val := by
    intro same
    apply different03
    apply UScalar.val_eq_imp
    exact same
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun, differentVal, usizeZeroSucc, Std.lift]

private theorem allDifferentFindFourthStep1
    (group0 group1 group2 group3 : Std.U8) (different13 : group1 ≠ group3) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (lastPairUnique3 group0 group1 group2) 3#usize group3 1#usize =
      ok (cont 2#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index1 group0 group1 group2 0#u8)
  have differentVal : group1.val ≠ group3.val := by
    intro same
    apply different13
    apply UScalar.val_eq_imp
    exact same
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun, differentVal, usizeOneSucc, Std.lift]

private theorem allDifferentFindFourthStep2
    (group0 group1 group2 group3 : Std.U8) (different23 : group2 ≠ group3) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (lastPairUnique3 group0 group1 group2) 3#usize group3 2#usize =
      ok (cont 3#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index2 group0 group1 group2 0#u8)
  have differentVal : group2.val ≠ group3.val := by
    intro same
    apply different23
    apply UScalar.val_eq_imp
    exact same
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun, differentVal, usizeTwoSucc, Std.lift]

private theorem allDifferentFindFourthDone
    (group0 group1 group2 group3 : Std.U8) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (lastPairUnique3 group0 group1 group2) 3#usize group3 3#usize =
      ok (done 3#usize) := by
  simp [sumcheck.fold_group_tuple_loop0_loop0.body]

private theorem allDifferentFindFourth
    (group0 group1 group2 group3 : Std.U8)
    (different03 : group0 ≠ group3) (different13 : group1 ≠ group3)
    (different23 : group2 ≠ group3) :
    sumcheck.fold_group_tuple_loop0_loop0
        (lastPairUnique3 group0 group1 group2) 3#usize group3 0#usize =
      ok 3#usize := by
  unfold
    sumcheck.fold_group_tuple_loop0_loop0
  rw [loop.eq_1]
  rw [allDifferentFindFourthStep0 group0 group1 group2 group3 different03]
  simp only
  rw [loop.eq_1]
  rw [allDifferentFindFourthStep1 group0 group1 group2 group3 different13]
  simp only
  rw [loop.eq_1]
  rw [allDifferentFindFourthStep2 group0 group1 group2 group3 different23]
  simp only
  rw [loop.eq_1]
  rw [allDifferentFindFourthDone]

private theorem usizeThreeSucc :
    Std.Usize.wrapping_add 3#usize 1#usize = 4#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#usize).hSize; scalar_tac)]
  norm_num

private theorem allDifferentOuterStep0
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllDifferent group0 group1 group2 group3)
        (powers alpha alpha2 alpha3) (rangeFrom 0#usize) unique0 coefficients0
        unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  apply phaseFirstStep
  simpa [groupsAllDifferent] using
    arrayMake4Index0 group0 group1 group2 group3

private theorem allDifferentOuterStep1
    (group0 group1 group2 group3 : Std.U8) (different01 : group0 ≠ group1)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllDifferent group0 group1 group2 group3)
        (powers alpha alpha2 alpha3) (rangeFrom 1#usize) (unique1 group0)
        coefficients1 (countsAt 1#u8) slots0 1#usize =
      ok (cont (rangeFrom 2#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficients11 alpha3, oneThreeCounts11,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          1#usize = ok group1 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index1 group0 group1 group2 group3)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 1#usize =
      ok alpha3 := by
    simpa [powers] using
      (arrayMake4Index1
        field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun,
    oneThreeFindNew group0 group1 different01, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, countsAt, slots0, oneThreeUnique2,
    threeAroundCoefficients11, oneThreeCounts11, oneThreeFirstSlots,
    Array.update, Std.lift, castUsizeOneU8, usizeOneSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem allDifferentOuterStep2
    (group0 group1 group2 group3 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllDifferent group0 group1 group2 group3)
        (powers alpha alpha2 alpha3) (rangeFrom 2#usize)
        (oneThreeUnique2 group0 group1) (threeAroundCoefficients11 alpha3)
        oneThreeCounts11 oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 3#usize, lastPairUnique3 group0 group1 group2,
        lastPairCoefficients111 alpha3 alpha2, lastPairCounts111,
        lastPairFirstSlots, 3#usize)) := by
  have groupRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          2#usize = ok group2 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index2 group0 group1 group2 group3)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun,
    lastPairFindNew group0 group1 group2 different02 different12, powerRun]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficients11, oneThreeCounts11,
    oneThreeFirstSlots, lastPairUnique3, lastPairCoefficients111,
    lastPairCounts111, lastPairFirstSlots, Array.update, Std.lift,
    castUsizeTwoU8, usizeTwoSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem allDifferentOuterStep3
    (group0 group1 group2 group3 : Std.U8)
    (different03 : group0 ≠ group3) (different13 : group1 ≠ group3)
    (different23 : group2 ≠ group3) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllDifferent group0 group1 group2 group3)
        (powers alpha alpha2 alpha3) (rangeFrom 3#usize)
        (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficients111 alpha3 alpha2) lastPairCounts111
        lastPairFirstSlots 3#usize =
      ok (cont (rangeFrom 4#usize,
        groupsAllDifferent group0 group1 group2 group3,
        allDifferentCoefficients alpha alpha2 alpha3, allDifferentCounts,
        allDifferentFirstSlots, 4#usize)) := by
  have groupRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          3#usize = ok group3 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index3 group0 group1 group2 group3)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    allDifferentFindFourth group0 group1 group2 group3 different03 different13
      different23,
    powerRun]
  simp (config := { maxSteps := 100000 })
    [lastPairUnique3, lastPairCoefficients111, lastPairCounts111,
    lastPairFirstSlots, groupsAllDifferent, allDifferentCoefficients,
    allDifferentCounts, allDifferentFirstSlots, Array.update, Std.lift,
    castUsizeThreeU8, usizeThreeSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem allDifferentInnerStep0
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (sum0Run :
      field.QM31.add
          field.QM31.ZERO value0 =
        ok sum0) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 0#usize, «end» := 4#usize }
        field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 4#usize }, sum0)) := by
  have uniqueRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          0#usize = ok group0 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index0 group0 group1 group2 group3)
  have firstSlotRun :
      Array.index_usize allDifferentFirstSlots 0#usize = ok 0#u8 := by
    simpa [allDifferentFirstSlots] using
      (arrayMake4Index0 0#u8 1#u8 2#u8 3#u8)
  have countRun : Array.index_usize allDifferentCounts 0#usize = ok 1#u8 := by
    simpa [allDifferentCounts] using
      (arrayMake4Index0 1#u8 1#u8 1#u8 1#u8)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext0, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, sum0Run, Std.lift]

private theorem allDifferentInnerStep1
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum1Run :
      field.QM31.add sum0 contribution1 =
        ok sum1) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 1#usize, «end» := 4#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 4#usize }, sum1)) := by
  have uniqueRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          1#usize = ok group1 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index1 group0 group1 group2 group3)
  have firstSlotRun :
      Array.index_usize allDifferentFirstSlots 1#usize = ok 1#u8 := by
    simpa [allDifferentFirstSlots] using
      (arrayMake4Index1 0#u8 1#u8 2#u8 3#u8)
  have coefficientRun :
      Array.index_usize (allDifferentCoefficients alpha alpha2 alpha3)
          1#usize = ok alpha3 := by
    simpa [allDifferentCoefficients] using
      (arrayMake4Index1
        field.QM31.ONE alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext1, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem allDifferentInnerStep2
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value2 contribution2 sum1 sum2 : RawQM31)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution2Run :
      field.QM31.mul
          value2 alpha2 = ok contribution2)
    (sum2Run :
      field.QM31.add sum1 contribution2 =
        ok sum2) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 2#usize, «end» := 4#usize } sum1 =
      ok (cont ({ start := 3#usize, «end» := 4#usize }, sum2)) := by
  have uniqueRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          2#usize = ok group2 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index2 group0 group1 group2 group3)
  have firstSlotRun :
      Array.index_usize allDifferentFirstSlots 2#usize = ok 2#u8 := by
    simpa [allDifferentFirstSlots] using
      (arrayMake4Index2 0#u8 1#u8 2#u8 3#u8)
  have coefficientRun :
      Array.index_usize (allDifferentCoefficients alpha alpha2 alpha3)
          2#usize = ok alpha2 := by
    simpa [allDifferentCoefficients] using
      (arrayMake4Index2
        field.QM31.ONE alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext2, uniqueRun, fromU8ToUsizeExact, value2Run, firstSlotRun,
    coefficientRun, contribution2Run, sum2Run, Std.lift]

private theorem allDifferentInnerStep3
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value3 contribution3 sum2 sum3 : RawQM31)
    (value3Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (contribution3Run :
      field.QM31.mul
          value3 alpha = ok contribution3)
    (sum3Run :
      field.QM31.add sum2 contribution3 =
        ok sum3) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 3#usize, «end» := 4#usize } sum2 =
      ok (cont ({ start := 4#usize, «end» := 4#usize }, sum3)) := by
  have uniqueRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          3#usize = ok group3 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index3 group0 group1 group2 group3)
  have firstSlotRun :
      Array.index_usize allDifferentFirstSlots 3#usize = ok 3#u8 := by
    simpa [allDifferentFirstSlots] using
      (arrayMake4Index3 0#u8 1#u8 2#u8 3#u8)
  have coefficientRun :
      Array.index_usize (allDifferentCoefficients alpha alpha2 alpha3)
          3#usize = ok alpha := by
    simpa [allDifferentCoefficients] using
      (arrayMake4Index3
        field.QM31.ONE alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext3, uniqueRun, fromU8ToUsizeExact, value3Run, firstSlotRun,
    coefficientRun, contribution3Run, sum3Run, Std.lift]

private theorem allDifferentInnerDone
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 sum3 : RawQM31) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 4#usize, «end» := 4#usize } sum3 =
      ok (done sum3) := by
  simp [sumcheck.fold_group_tuple_loop1.body,
    rangeDone4]

private theorem allDifferentInnerExact
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value0 value1 value2 value3 contribution1
      contribution2 contribution3 sum0 sum1 sum2 sum3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value3Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (contribution1Run :
      field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      field.QM31.mul
          value2 alpha2 = ok contribution2)
    (contribution3Run :
      field.QM31.mul
          value3 alpha = ok contribution3)
    (sum0Run :
      field.QM31.add
          field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      field.QM31.add sum1 contribution2 =
        ok sum2)
    (sum3Run :
      field.QM31.add sum2 contribution3 =
        ok sum3) :
    sumcheck.fold_group_tuple_loop1
        { start := 0#usize, «end» := 4#usize } groupValues
        (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots field.QM31.ZERO =
      ok sum3 := by
  have step0 := allDifferentInnerStep0 group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 value0 sum0 value0Run sum0Run
  have step1 := allDifferentInnerStep1 group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 value1 contribution1 sum0 sum1 value1Run
    contribution1Run sum1Run
  have step2 := allDifferentInnerStep2 group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 value2 contribution2 sum1 sum2 value2Run
    contribution2Run sum2Run
  have step3 := allDifferentInnerStep3 group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 value3 contribution3 sum2 sum3 value3Run
    contribution3Run sum3Run
  have done := allDifferentInnerDone group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 sum3
  unfold
    sumcheck.fold_group_tuple_loop1
  rw [loop.eq_1]
  dsimp only
  rw [step0]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step1]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step3]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [done]

private theorem allDifferentPhaseExact
    (group0 group1 group2 group3 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (different03 : group0 ≠ group3)
    (different13 : group1 ≠ group3) (different23 : group2 ≠ group3)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0 (rangeFrom 0#usize)
        (groupsAllDifferent group0 group1 group2 group3)
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0 slots0 0#usize =
      ok (groupsAllDifferent group0 group1 group2 group3,
        allDifferentCoefficients alpha alpha2 alpha3, allDifferentCounts,
        allDifferentFirstSlots, 4#usize) := by
  have step0 := allDifferentOuterStep0 group0 group1 group2 group3 groupValues alpha alpha2 alpha3
  have step1 := allDifferentOuterStep1 group0 group1 group2 group3 different01 groupValues alpha alpha2 alpha3
  have step2 := allDifferentOuterStep2 group0 group1 group2 group3 different02 different12 groupValues alpha alpha2 alpha3
  have step3 := allDifferentOuterStep3 group0 group1 group2 group3 different03 different13 different23 groupValues alpha alpha2 alpha3
  unfold sumcheck.fold_group_tuple_loop0
  rw [loop.eq_1]; dsimp only; rw [step0]; simp only
  rw [loop.eq_1]; dsimp only; rw [step1]; simp only
  rw [loop.eq_1]; dsimp only; rw [step2]; simp only
  rw [loop.eq_1]; dsimp only; rw [step3]; simp only
  rw [loop.eq_1]; dsimp only
  unfold sumcheck.fold_group_tuple_loop0.body
  simp only [rangeFrom]
  rw [rangeDone4]
  rfl

theorem allDifferentSourceExact
    (group0 group1 group2 group3 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (different03 : group0 ≠ group3)
    (different13 : group1 ≠ group3) (different23 : group2 ≠ group3)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value0 value1 value2 value3 contribution1
      contribution2 contribution3 sum0 sum1 sum2 sum3 half1 out : RawQM31)
    (value0Run : Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run : Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run : Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value3Run : Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (contribution1Run : field.QM31.mul value1 alpha3 = ok contribution1)
    (contribution2Run : field.QM31.mul value2 alpha2 = ok contribution2)
    (contribution3Run : field.QM31.mul value3 alpha = ok contribution3)
    (sum0Run : field.QM31.add field.QM31.ZERO value0 = ok sum0)
    (sum1Run : field.QM31.add sum0 contribution1 = ok sum1)
    (sum2Run : field.QM31.add sum1 contribution2 = ok sum2)
    (sum3Run : field.QM31.add sum2 contribution3 = ok sum3)
    (half1Run : field.QM31.half sum3 = ok half1)
    (outRun : field.QM31.half half1 = ok out) :
    sumcheck.fold_group_tuple (groupsAllDifferent group0 group1 group2 group3) groupValues alpha alpha2 alpha3 = ok out := by
  have phaseRun := allDifferentPhaseExact group0 group1 group2 group3 different01 different02 different12 different03 different13 different23 groupValues alpha alpha2 alpha3
  have phaseRunExpanded :
      sumcheck.fold_group_tuple_loop0 { start := 0#usize, «end» := 4#usize }
        (groupsAllDifferent group0 group1 group2 group3)
        (Array.make 4#usize [field.QM31.ONE, alpha3, alpha2, alpha])
        (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize field.QM31.ZERO)
        (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize 0#u8) 0#usize =
      ok (groupsAllDifferent group0 group1 group2 group3,
        allDifferentCoefficients alpha alpha2 alpha3, allDifferentCounts,
        allDifferentFirstSlots, 4#usize) := by
    simpa only [rangeFrom, powers, unique0, coefficients0, slots0] using phaseRun
  have contributionRun := allDifferentInnerExact group0 group1 group2 group3 groupValues alpha alpha2 alpha3
    value0 value1 value2 value3 contribution1 contribution2 contribution3 sum0 sum1 sum2 sum3
    value0Run value1Run value2Run value3Run contribution1Run contribution2Run contribution3Run
    sum0Run sum1Run sum2Run sum3Run
  unfold sumcheck.fold_group_tuple
  dsimp only
  rw [phaseRunExpanded]
  simp only [bind_tc_ok]
  rw [contributionRun]
  simp only [bind_tc_ok]
  rw [half1Run]
  simp only [bind_tc_ok]
  exact outRun

theorem allDifferentSourceCorresponds
    (group0 group1 group2 group3 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (different03 : group0 ≠ group3)
    (different13 : group1 ≠ group3) (different23 : group2 ≠ group3)
    (groupValues : Slice RawQM31)
    (value0 value1 value2 value3 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value3Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (value0Canonical : GeneratedCanonicalQM31 value0)
    (value1Canonical : GeneratedCanonicalQM31 value1)
    (value2Canonical : GeneratedCanonicalQM31 value2)
    (value3Canonical : GeneratedCanonicalQM31 value3)
    (alphaCanonical : GeneratedCanonicalQM31 alpha)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2)
    (alpha3Canonical : GeneratedCanonicalQM31 alpha3)
    (alpha2Exact : exactRaw alpha2 = exactRaw alpha ^ 2)
    (alpha3Exact : exactRaw alpha3 = exactRaw alpha ^ 3) :
    ∃ out,
      sumcheck.fold_group_tuple
          (groupsAllDifferent group0 group1 group2 group3) groupValues alpha
          alpha2 alpha3 = ok out ∧
      GeneratedCanonicalQM31 out ∧
      exactRaw out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (exactRaw alpha)
          (fun index => ![exactRaw value0, exactRaw value1,
            exactRaw value2, exactRaw value3] index) := by
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha3 value1Canonical
      alpha3Canonical
  obtain ⟨contribution2, contribution2Run, contribution2Canonical,
      contribution2Exact⟩ :=
    generated_qm31_mul_corresponds value2 alpha2 value2Canonical
      alpha2Canonical
  obtain ⟨contribution3, contribution3Run, contribution3Canonical,
      contribution3Exact⟩ :=
    generated_qm31_mul_corresponds value3 alpha value3Canonical alphaCanonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      field.QM31.ZERO value0
      zeroCanonical value0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨sum2, sum2Run, sum2Canonical, sum2Exact⟩ :=
    generated_qm31_add_corresponds sum1 contribution2 sum1Canonical
      contribution2Canonical
  obtain ⟨sum3, sum3Run, sum3Canonical, sum3Exact⟩ :=
    generated_qm31_add_corresponds sum2 contribution3 sum2Canonical
      contribution3Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum3 sum3Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := allDifferentSourceExact group0 group1 group2 group3
    different01 different02 different12 different03 different13 different23
    groupValues alpha alpha2 alpha3 value0 value1 value2 value3 contribution1
    contribution2 contribution3 sum0 sum1 sum2 sum3 half1 out value0Run
    value1Run value2Run value3Run contribution1Run contribution2Run
    contribution3Run sum0Run sum1Run sum2Run sum3Run half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have contribution1ExactM := congrArg sourceQm31ToModel contribution1Exact
  have contribution2ExactM := congrArg sourceQm31ToModel contribution2Exact
  have contribution3ExactM := congrArg sourceQm31ToModel contribution3Exact
  have sum0ExactM := congrArg sourceQm31ToModel sum0Exact
  have sum1ExactM := congrArg sourceQm31ToModel sum1Exact
  have sum2ExactM := congrArg sourceQm31ToModel sum2Exact
  have sum3ExactM := congrArg sourceQm31ToModel sum3Exact
  have half1ExactM := congrArg sourceQm31ToModel half1Exact
  have outExactM := congrArg sourceQm31ToModel outExact
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution2ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution3ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum2ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum3ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at half1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at outExactM
  have zeroExact :
      exactRaw
          field.QM31.ZERO = 0 := by
    rw [field.QM31.ZERO]
    rfl
  have fourNonzero : (4 : ExactQM31) ≠ 0 := by decide
  apply (eq_div_iff fourNonzero).2
  simp
  calc
    exactRaw out * 4 =
        (exactRaw out + exactRaw out) +
          (exactRaw out + exactRaw out) := by ring
    _ = exactRaw half1 + exactRaw half1 := by
      rw [outExactM]
    _ = exactRaw sum3 := half1ExactM
    _ = exactRaw sum2 + exactRaw contribution3 := sum3ExactM
    _ = (exactRaw sum1 + exactRaw contribution2) +
        exactRaw contribution3 := by rw [sum2ExactM]
    _ = ((exactRaw sum0 + exactRaw contribution1) +
        exactRaw contribution2) + exactRaw contribution3 := by
      rw [sum1ExactM]
    _ = (((exactRaw
          field.QM31.ZERO +
          exactRaw value0) + exactRaw contribution1) +
        exactRaw contribution2) + exactRaw contribution3 := by
      rw [sum0ExactM]
    _ = exactRaw value0 +
        exactRaw value1 * exactRaw alpha3 +
        exactRaw value2 * exactRaw alpha2 +
        exactRaw value3 * exactRaw alpha := by
      rw [zeroExact, contribution1ExactM, contribution2ExactM,
        contribution3ExactM]
      ring
    _ = exactRaw value0 +
        exactRaw value1 * exactRaw alpha ^ 3 +
        exactRaw value2 * exactRaw alpha ^ 2 +
        exactRaw value3 * exactRaw alpha := by
      rw [alpha2Exact, alpha3Exact]
    _ = exactRaw value0 +
        exactRaw alpha ^ 3 * exactRaw value1 +
        exactRaw alpha ^ 2 * exactRaw value2 +
        exactRaw alpha * exactRaw value3 := by ring


#print axioms allDifferentPhaseExact
#print axioms allDifferentSourceExact
#print axioms allDifferentSourceCorresponds
end V7CallerCurrentReleaseR26GroupedAllDifferent
