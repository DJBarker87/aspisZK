import V7CallerCurrentReleaseR26GroupedThreeAround

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
open V7CallerCurrentReleaseR26GroupedOneThree
open V7CallerCurrentReleaseR26GroupedThreeAround

namespace V7CallerCurrentReleaseR26GroupedLastPair

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def groupsLastPair
    (group0 group1 group2 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group2, group2]

def lastPairUnique3
    (group0 group1 group2 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group2, 0#u8]

private def lastPairCoefficients111
    (alpha3 alpha2 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    field.QM31.ONE, alpha3, alpha2,
    field.QM31.ZERO]

private def lastPairCoefficientsFinal
    (alpha3 coefficient2 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    field.QM31.ONE, alpha3, coefficient2,
    field.QM31.ZERO]

private def lastPairCounts111 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 1#u8, 0#u8]

private def lastPairCounts112 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 2#u8, 0#u8]

private def lastPairFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 2#u8, 0#u8]

private theorem lastPairFindNewStep0
    (group0 group1 group2 : Std.U8) (different02 : group0 ≠ group2) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (oneThreeUnique2 group0 group1) 2#usize group2 0#usize =
      ok (cont 1#usize) := by
  have indexRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 0#usize =
        ok group0 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index0 group0 group1 0#u8 0#u8)
  have differentVal : group0.val ≠ group2.val := by
    intro same
    apply different02
    apply UScalar.val_eq_imp
    exact same
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun, differentVal, usizeZeroSucc, Std.lift]

private theorem lastPairFindNewStep1
    (group0 group1 group2 : Std.U8) (different12 : group1 ≠ group2) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (oneThreeUnique2 group0 group1) 2#usize group2 1#usize =
      ok (cont 2#usize) := by
  have indexRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 1#usize =
        ok group1 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index1 group0 group1 0#u8 0#u8)
  have differentVal : group1.val ≠ group2.val := by
    intro same
    apply different12
    apply UScalar.val_eq_imp
    exact same
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun, differentVal, usizeOneSucc, Std.lift]

private theorem lastPairFindNewDone
    (group0 group1 group2 : Std.U8) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (oneThreeUnique2 group0 group1) 2#usize group2 2#usize =
      ok (done 2#usize) := by
  simp [sumcheck.fold_group_tuple_loop0_loop0.body]

theorem lastPairFindNew
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2) :
    sumcheck.fold_group_tuple_loop0_loop0
        (oneThreeUnique2 group0 group1) 2#usize group2 0#usize =
      ok 2#usize := by
  unfold
    sumcheck.fold_group_tuple_loop0_loop0
  rw [loop.eq_1]
  rw [lastPairFindNewStep0 group0 group1 group2 different02]
  simp only
  rw [loop.eq_1]
  rw [lastPairFindNewStep1 group0 group1 group2 different12]
  simp only
  rw [loop.eq_1]
  rw [lastPairFindNewDone]

private theorem lastPairFindExistingStep0
    (group0 group1 group2 : Std.U8) (different02 : group0 ≠ group2) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (lastPairUnique3 group0 group1 group2) 3#usize group2 0#usize =
      ok (cont 1#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 0#usize =
        ok group0 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index0 group0 group1 group2 0#u8)
  have differentVal : group0.val ≠ group2.val := by
    intro same
    apply different02
    apply UScalar.val_eq_imp
    exact same
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun, differentVal, usizeZeroSucc, Std.lift]

private theorem lastPairFindExistingStep1
    (group0 group1 group2 : Std.U8) (different12 : group1 ≠ group2) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (lastPairUnique3 group0 group1 group2) 3#usize group2 1#usize =
      ok (cont 2#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index1 group0 group1 group2 0#u8)
  have differentVal : group1.val ≠ group2.val := by
    intro same
    apply different12
    apply UScalar.val_eq_imp
    exact same
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun, differentVal, usizeOneSucc, Std.lift]

private theorem lastPairFindExistingDone
    (group0 group1 group2 : Std.U8) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (lastPairUnique3 group0 group1 group2) 3#usize group2 2#usize =
      ok (done 2#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index2 group0 group1 group2 0#u8)
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun]

private theorem lastPairFindExisting
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2) :
    sumcheck.fold_group_tuple_loop0_loop0
        (lastPairUnique3 group0 group1 group2) 3#usize group2 0#usize =
      ok 2#usize := by
  unfold
    sumcheck.fold_group_tuple_loop0_loop0
  rw [loop.eq_1]
  rw [lastPairFindExistingStep0 group0 group1 group2 different02]
  simp only
  rw [loop.eq_1]
  rw [lastPairFindExistingStep1 group0 group1 group2 different12]
  simp only
  rw [loop.eq_1]
  rw [lastPairFindExistingDone]

private theorem lastPairOuterStep0
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsLastPair group0 group1 group2)
        (powers alpha alpha2 alpha3) (rangeFrom 0#usize) unique0 coefficients0
        unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  apply phaseFirstStep
  simpa [groupsLastPair] using
    arrayMake4Index0 group0 group1 group2 group2

private theorem lastPairOuterStep1
    (group0 group1 group2 : Std.U8) (different01 : group0 ≠ group1)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsLastPair group0 group1 group2)
        (powers alpha alpha2 alpha3) (rangeFrom 1#usize) (unique1 group0)
        coefficients1 (countsAt 1#u8) slots0 1#usize =
      ok (cont (rangeFrom 2#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficients11 alpha3, oneThreeCounts11,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsLastPair group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [groupsLastPair] using
      (arrayMake4Index1 group0 group1 group2 group2)
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

private theorem lastPairOuterStep2
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsLastPair group0 group1 group2)
        (powers alpha alpha2 alpha3) (rangeFrom 2#usize)
        (oneThreeUnique2 group0 group1) (threeAroundCoefficients11 alpha3)
        oneThreeCounts11 oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 3#usize, lastPairUnique3 group0 group1 group2,
        lastPairCoefficients111 alpha3 alpha2, lastPairCounts111,
        lastPairFirstSlots, 3#usize)) := by
  have groupRun :
      Array.index_usize (groupsLastPair group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [groupsLastPair] using
      (arrayMake4Index2 group0 group1 group2 group2)
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

private theorem lastPairOuterStep3
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient2 : RawQM31)
    (coefficient2Run :
      field.QM31.add alpha2 alpha =
        ok coefficient2) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsLastPair group0 group1 group2)
        (powers alpha alpha2 alpha3) (rangeFrom 3#usize)
        (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficients111 alpha3 alpha2) lastPairCounts111
        lastPairFirstSlots 3#usize =
      ok (cont (rangeFrom 4#usize, lastPairUnique3 group0 group1 group2,
        lastPairCoefficientsFinal alpha3 coefficient2, lastPairCounts112,
        lastPairFirstSlots, 3#usize)) := by
  have groupRun :
      Array.index_usize (groupsLastPair group0 group1 group2) 3#usize =
        ok group2 := by
    simpa [groupsLastPair] using
      (arrayMake4Index3 group0 group1 group2 group2)
  have coefficientRun :
      Array.index_usize (lastPairCoefficients111 alpha3 alpha2) 2#usize =
        ok alpha2 := by
    simpa [lastPairCoefficients111] using
      (arrayMake4Index2
        field.QM31.ONE alpha3 alpha2
        field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize lastPairCounts111 2#usize = ok 1#u8 := by
    simpa [lastPairCounts111] using
      (arrayMake4Index2 1#u8 1#u8 1#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    lastPairFindExisting group0 group1 group2 different02 different12,
    coefficientRun, powerRun, coefficient2Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [lastPairUnique3, lastPairCoefficients111, lastPairCoefficientsFinal,
    lastPairCounts111, lastPairCounts112, lastPairFirstSlots, Array.update,
    Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem rangeNext0End3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 3#usize } =
      ok (some 0#usize, { start := 1#usize, «end» := 3#usize }) := by
  have hmax : 0 < UScalar.max .Usize := by
    have h := (1#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext1End3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 3#usize } =
      ok (some 1#usize, { start := 2#usize, «end» := 3#usize }) := by
  have hmax : 1 < UScalar.max .Usize := by
    have h := (2#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext2End3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := 3#usize } =
      ok (some 2#usize, { start := 3#usize, «end» := 3#usize }) := by
  have hmax : 2 < UScalar.max .Usize := by
    have h := (3#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeDone3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 3#usize, «end» := 3#usize } =
      ok (none, { start := 3#usize, «end» := 3#usize }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

private theorem lastPairInnerStep0
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 value0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (sum0Run :
      field.QM31.add
          field.QM31.ZERO value0 =
        ok sum0) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots { start := 0#usize, «end» := 3#usize }
        field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 3#usize }, sum0)) := by
  have uniqueRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 0#usize =
        ok group0 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index0 group0 group1 group2 0#u8)
  have firstSlotRun :
      Array.index_usize lastPairFirstSlots 0#usize = ok 0#u8 := by
    simpa [lastPairFirstSlots] using
      (arrayMake4Index0 0#u8 1#u8 2#u8 0#u8)
  have countRun : Array.index_usize lastPairCounts112 0#usize = ok 1#u8 := by
    simpa [lastPairCounts112] using
      (arrayMake4Index0 1#u8 1#u8 2#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext0End3, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, sum0Run, Std.lift]

private theorem lastPairInnerStep1
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum1Run :
      field.QM31.add sum0 contribution1 =
        ok sum1) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots { start := 1#usize, «end» := 3#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 3#usize }, sum1)) := by
  have uniqueRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index1 group0 group1 group2 0#u8)
  have firstSlotRun :
      Array.index_usize lastPairFirstSlots 1#usize = ok 1#u8 := by
    simpa [lastPairFirstSlots] using
      (arrayMake4Index1 0#u8 1#u8 2#u8 0#u8)
  have coefficientRun :
      Array.index_usize (lastPairCoefficientsFinal alpha3 coefficient2)
          1#usize = ok alpha3 := by
    simpa [lastPairCoefficientsFinal] using
      (arrayMake4Index1
        field.QM31.ONE alpha3 coefficient2
        field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext1End3, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem lastPairInnerStep2
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 value2 contribution2 sum1 sum2 : RawQM31)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution2Run :
      field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sum2Run :
      field.QM31.add sum1 contribution2 =
        ok sum2) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots { start := 2#usize, «end» := 3#usize } sum1 =
      ok (cont ({ start := 3#usize, «end» := 3#usize }, sum2)) := by
  have uniqueRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index2 group0 group1 group2 0#u8)
  have firstSlotRun :
      Array.index_usize lastPairFirstSlots 2#usize = ok 2#u8 := by
    simpa [lastPairFirstSlots] using
      (arrayMake4Index2 0#u8 1#u8 2#u8 0#u8)
  have coefficientRun :
      Array.index_usize (lastPairCoefficientsFinal alpha3 coefficient2)
          2#usize = ok coefficient2 := by
    simpa [lastPairCoefficientsFinal] using
      (arrayMake4Index2
        field.QM31.ONE alpha3 coefficient2
        field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext2End3, uniqueRun, fromU8ToUsizeExact, value2Run, firstSlotRun,
    coefficientRun, contribution2Run, sum2Run, Std.lift]

private theorem lastPairInnerDone
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 sum2 : RawQM31) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots { start := 3#usize, «end» := 3#usize } sum2 =
      ok (done sum2) := by
  simp [sumcheck.fold_group_tuple_loop1.body,
    rangeDone3]

private theorem lastPairInnerExact
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 value0 value1 value2 contribution1 contribution2
      sum0 sum1 sum2 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution1Run :
      field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sum0Run :
      field.QM31.add
          field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      field.QM31.add sum1 contribution2 =
        ok sum2) :
    sumcheck.fold_group_tuple_loop1
        { start := 0#usize, «end» := 3#usize } groupValues
        (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots field.QM31.ZERO =
      ok sum2 := by
  have step0 := lastPairInnerStep0 group0 group1 group2 groupValues alpha3
    coefficient2 value0 sum0 value0Run sum0Run
  have step1 := lastPairInnerStep1 group0 group1 group2 groupValues alpha3
    coefficient2 value1 contribution1 sum0 sum1 value1Run contribution1Run
    sum1Run
  have step2 := lastPairInnerStep2 group0 group1 group2 groupValues alpha3
    coefficient2 value2 contribution2 sum1 sum2 value2Run contribution2Run
    sum2Run
  have done := lastPairInnerDone group0 group1 group2 groupValues alpha3
    coefficient2 sum2
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
  rw [done]

private theorem lastPairPhaseExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient2 : RawQM31)
    (coefficient2Run : field.QM31.add alpha2 alpha = ok coefficient2) :
    sumcheck.fold_group_tuple_loop0 (rangeFrom 0#usize)
        (groupsLastPair group0 group1 group2) (powers alpha alpha2 alpha3)
        unique0 coefficients0 unique0 slots0 0#usize =
      ok (lastPairUnique3 group0 group1 group2,
        lastPairCoefficientsFinal alpha3 coefficient2, lastPairCounts112,
        lastPairFirstSlots, 3#usize) := by
  have step0 := lastPairOuterStep0 group0 group1 group2 groupValues alpha alpha2 alpha3
  have step1 := lastPairOuterStep1 group0 group1 group2 different01 groupValues alpha alpha2 alpha3
  have step2 := lastPairOuterStep2 group0 group1 group2 different02 different12 groupValues alpha alpha2 alpha3
  have step3 := lastPairOuterStep3 group0 group1 group2 different02 different12 groupValues alpha alpha2 alpha3 coefficient2 coefficient2Run
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

theorem lastPairSourceExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient2 value0 value1 value2 contribution1
      contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (coefficient2Run : field.QM31.add alpha2 alpha = ok coefficient2)
    (value0Run : Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run : Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run : Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution1Run : field.QM31.mul value1 alpha3 = ok contribution1)
    (contribution2Run : field.QM31.mul value2 coefficient2 = ok contribution2)
    (sum0Run : field.QM31.add field.QM31.ZERO value0 = ok sum0)
    (sum1Run : field.QM31.add sum0 contribution1 = ok sum1)
    (sum2Run : field.QM31.add sum1 contribution2 = ok sum2)
    (half1Run : field.QM31.half sum2 = ok half1)
    (outRun : field.QM31.half half1 = ok out) :
    sumcheck.fold_group_tuple (groupsLastPair group0 group1 group2) groupValues alpha alpha2 alpha3 = ok out := by
  have phaseRun := lastPairPhaseExact group0 group1 group2 different01 different02 different12 groupValues alpha alpha2 alpha3 coefficient2 coefficient2Run
  have phaseRunExpanded :
      sumcheck.fold_group_tuple_loop0 { start := 0#usize, «end» := 4#usize }
        (groupsLastPair group0 group1 group2)
        (Array.make 4#usize [field.QM31.ONE, alpha3, alpha2, alpha])
        (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize field.QM31.ZERO)
        (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize 0#u8) 0#usize =
      ok (lastPairUnique3 group0 group1 group2,
        lastPairCoefficientsFinal alpha3 coefficient2, lastPairCounts112,
        lastPairFirstSlots, 3#usize) := by
    simpa only [rangeFrom, powers, unique0, coefficients0, slots0] using phaseRun
  have contributionRun := lastPairInnerExact group0 group1 group2 groupValues alpha3 coefficient2
    value0 value1 value2 contribution1 contribution2 sum0 sum1 sum2 value0Run
    value1Run value2Run contribution1Run contribution2Run sum0Run sum1Run sum2Run
  unfold sumcheck.fold_group_tuple
  dsimp only
  rw [phaseRunExpanded]
  simp only [bind_tc_ok]
  rw [contributionRun]
  simp only [bind_tc_ok]
  rw [half1Run]
  simp only [bind_tc_ok]
  exact outRun

theorem lastPairSourceCorresponds
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (value0 value1 value2 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value0Canonical : GeneratedCanonicalQM31 value0)
    (value1Canonical : GeneratedCanonicalQM31 value1)
    (value2Canonical : GeneratedCanonicalQM31 value2)
    (alphaCanonical : GeneratedCanonicalQM31 alpha)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2)
    (alpha3Canonical : GeneratedCanonicalQM31 alpha3)
    (alpha2Exact : exactRaw alpha2 = exactRaw alpha ^ 2)
    (alpha3Exact : exactRaw alpha3 = exactRaw alpha ^ 3) :
    ∃ out,
      sumcheck.fold_group_tuple
          (groupsLastPair group0 group1 group2) groupValues alpha alpha2 alpha3 =
        ok out ∧
      GeneratedCanonicalQM31 out ∧
      exactRaw out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (exactRaw alpha)
          (fun index => ![exactRaw value0, exactRaw value1,
            exactRaw value2, exactRaw value2] index) := by
  obtain ⟨coefficient2, coefficient2Run, coefficient2Canonical,
      coefficient2Exact⟩ :=
    generated_qm31_add_corresponds alpha2 alpha alpha2Canonical alphaCanonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha3 value1Canonical
      alpha3Canonical
  obtain ⟨contribution2, contribution2Run, contribution2Canonical,
      contribution2Exact⟩ :=
    generated_qm31_mul_corresponds value2 coefficient2 value2Canonical
      coefficient2Canonical
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
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum2 sum2Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := lastPairSourceExact group0 group1 group2 different01
    different02 different12 groupValues alpha alpha2 alpha3 coefficient2
    value0 value1 value2 contribution1 contribution2 sum0 sum1 sum2 half1 out
    coefficient2Run value0Run value1Run value2Run contribution1Run
    contribution2Run sum0Run sum1Run sum2Run half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient2ExactM := congrArg sourceQm31ToModel coefficient2Exact
  have contribution1ExactM := congrArg sourceQm31ToModel contribution1Exact
  have contribution2ExactM := congrArg sourceQm31ToModel contribution2Exact
  have sum0ExactM := congrArg sourceQm31ToModel sum0Exact
  have sum1ExactM := congrArg sourceQm31ToModel sum1Exact
  have sum2ExactM := congrArg sourceQm31ToModel sum2Exact
  have half1ExactM := congrArg sourceQm31ToModel half1Exact
  have outExactM := congrArg sourceQm31ToModel outExact
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at coefficient2ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution2ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum2ExactM
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
    _ = exactRaw sum2 := half1ExactM
    _ = exactRaw sum1 + exactRaw contribution2 := sum2ExactM
    _ = (exactRaw sum0 + exactRaw contribution1) +
        exactRaw contribution2 := by rw [sum1ExactM]
    _ = ((exactRaw
          field.QM31.ZERO +
          exactRaw value0) + exactRaw contribution1) +
        exactRaw contribution2 := by rw [sum0ExactM]
    _ = exactRaw value0 +
        exactRaw value1 * exactRaw alpha3 +
        exactRaw value2 * exactRaw coefficient2 := by
      rw [zeroExact, contribution1ExactM, contribution2ExactM]
      ring
    _ = exactRaw value0 +
        exactRaw value1 * exactRaw alpha ^ 3 +
        exactRaw value2 *
          (exactRaw alpha ^ 2 + exactRaw alpha) := by
      rw [coefficient2ExactM, alpha2Exact, alpha3Exact]
    _ = exactRaw value0 +
        exactRaw alpha ^ 3 * exactRaw value1 +
        exactRaw alpha ^ 2 * exactRaw value2 +
        exactRaw alpha * exactRaw value2 := by ring

/-! ## Shared three-value inner fold where every contribution is multiplied -/

private theorem threeMultiplyInnerStep0
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize)
    (group0 firstSlot0 count0 : Std.U8)
    (coefficient0 value0 contribution0 sum0 : RawQM31)
    (uniqueRun : Array.index_usize uniqueGroups 0#usize = ok group0)
    (firstSlotRun : Array.index_usize firstSlots 0#usize = ok firstSlot0)
    (countRun : Array.index_usize counts 0#usize = ok count0)
    (firstSlotZero : firstSlot0 = 0#u8)
    (countNotOne : count0 ≠ 1#u8)
    (coefficientRun :
      Array.index_usize coefficients 0#usize = ok coefficient0)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (contributionRun :
      field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (sumRun :
      field.QM31.add
          field.QM31.ZERO contribution0 =
        ok sum0) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues uniqueGroups coefficients counts firstSlots
        { start := 0#usize, «end» := 3#usize }
        field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 3#usize }, sum0)) := by
  subst firstSlot0
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext0End3, uniqueRun, fromU8ToUsizeExact, valueRun, firstSlotRun,
    countRun, countNotOne, coefficientRun, contributionRun, sumRun, Std.lift]

private theorem threeMultiplyInnerStep1
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize)
    (group1 firstSlot1 : Std.U8)
    (coefficient1 value1 contribution1 sum0 sum1 : RawQM31)
    (uniqueRun : Array.index_usize uniqueGroups 1#usize = ok group1)
    (firstSlotRun : Array.index_usize firstSlots 1#usize = ok firstSlot1)
    (firstSlotNotZero : firstSlot1 ≠ 0#u8)
    (coefficientRun :
      Array.index_usize coefficients 1#usize = ok coefficient1)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contributionRun :
      field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sumRun :
      field.QM31.add sum0 contribution1 =
        ok sum1) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues uniqueGroups coefficients counts firstSlots
        { start := 1#usize, «end» := 3#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 3#usize }, sum1)) := by
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext1End3, uniqueRun, fromU8ToUsizeExact, valueRun, firstSlotRun,
    firstSlotNotZero, coefficientRun, contributionRun, sumRun, Std.lift]

private theorem threeMultiplyInnerStep2
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize)
    (group2 firstSlot2 : Std.U8)
    (coefficient2 value2 contribution2 sum1 sum2 : RawQM31)
    (uniqueRun : Array.index_usize uniqueGroups 2#usize = ok group2)
    (firstSlotRun : Array.index_usize firstSlots 2#usize = ok firstSlot2)
    (firstSlotNotZero : firstSlot2 ≠ 0#u8)
    (coefficientRun :
      Array.index_usize coefficients 2#usize = ok coefficient2)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contributionRun :
      field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sumRun :
      field.QM31.add sum1 contribution2 =
        ok sum2) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues uniqueGroups coefficients counts firstSlots
        { start := 2#usize, «end» := 3#usize } sum1 =
      ok (cont ({ start := 3#usize, «end» := 3#usize }, sum2)) := by
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext2End3, uniqueRun, fromU8ToUsizeExact, valueRun, firstSlotRun,
    firstSlotNotZero, coefficientRun, contributionRun, sumRun, Std.lift]

private theorem threeMultiplyInnerDone
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize) (sum2 : RawQM31) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues uniqueGroups coefficients counts firstSlots
        { start := 3#usize, «end» := 3#usize } sum2 = ok (done sum2) := by
  simp [sumcheck.fold_group_tuple_loop1.body,
    rangeDone3]

theorem threeMultiplyInnerExact
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize)
    (group0 group1 group2 firstSlot0 count0 firstSlot1 firstSlot2 : Std.U8)
    (coefficient0 coefficient1 coefficient2 value0 value1 value2
      contribution0 contribution1 contribution2 sum0 sum1 sum2 : RawQM31)
    (unique0Run : Array.index_usize uniqueGroups 0#usize = ok group0)
    (unique1Run : Array.index_usize uniqueGroups 1#usize = ok group1)
    (unique2Run : Array.index_usize uniqueGroups 2#usize = ok group2)
    (firstSlot0Run : Array.index_usize firstSlots 0#usize = ok firstSlot0)
    (firstSlot1Run : Array.index_usize firstSlots 1#usize = ok firstSlot1)
    (firstSlot2Run : Array.index_usize firstSlots 2#usize = ok firstSlot2)
    (count0Run : Array.index_usize counts 0#usize = ok count0)
    (firstSlot0Zero : firstSlot0 = 0#u8)
    (count0NotOne : count0 ≠ 1#u8)
    (firstSlot1NotZero : firstSlot1 ≠ 0#u8)
    (firstSlot2NotZero : firstSlot2 ≠ 0#u8)
    (coefficient0Run : Array.index_usize coefficients 0#usize = ok coefficient0)
    (coefficient1Run : Array.index_usize coefficients 1#usize = ok coefficient1)
    (coefficient2Run : Array.index_usize coefficients 2#usize = ok coefficient2)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (contribution2Run :
      field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sum0Run :
      field.QM31.add
          field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      field.QM31.add sum1 contribution2 =
        ok sum2) :
    sumcheck.fold_group_tuple_loop1
        { start := 0#usize, «end» := 3#usize } groupValues uniqueGroups
        coefficients counts firstSlots
        field.QM31.ZERO = ok sum2 := by
  have step0 := threeMultiplyInnerStep0 groupValues uniqueGroups coefficients
    counts firstSlots group0 firstSlot0 count0 coefficient0 value0
    contribution0 sum0 unique0Run firstSlot0Run count0Run firstSlot0Zero
    count0NotOne coefficient0Run value0Run contribution0Run sum0Run
  have step1 := threeMultiplyInnerStep1 groupValues uniqueGroups coefficients
    counts firstSlots group1 firstSlot1 coefficient1 value1 contribution1 sum0
    sum1 unique1Run firstSlot1Run firstSlot1NotZero coefficient1Run value1Run
    contribution1Run sum1Run
  have step2 := threeMultiplyInnerStep2 groupValues uniqueGroups coefficients
    counts firstSlots group2 firstSlot2 coefficient2 value2 contribution2 sum1
    sum2 unique2Run firstSlot2Run firstSlot2NotZero coefficient2Run value2Run
    contribution2Run sum2Run
  have done := threeMultiplyInnerDone groupValues uniqueGroups coefficients
    counts firstSlots sum2
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
  rw [done]

#print axioms lastPairPhaseExact
#print axioms lastPairSourceExact
#print axioms lastPairSourceCorresponds
#print axioms threeMultiplyInnerExact
end V7CallerCurrentReleaseR26GroupedLastPair
