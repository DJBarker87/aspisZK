import V7CallerCurrentReleaseR26GroupedAllSame

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

namespace V7CallerCurrentReleaseR26GroupedPairPair

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def groupsPairPair : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 0#u8, 1#u8, 1#u8]

private def pairUnique2 : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 0#u8, 0#u8]

private def pairCoefficients2
    (coefficient0 alpha2 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0, alpha2,
    field.QM31.ZERO,
    field.QM31.ZERO]

private def pairCoefficientsFinal
    (coefficient0 coefficient1 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0, coefficient1,
    field.QM31.ZERO,
    field.QM31.ZERO]

private def pairCounts21 : Array Std.U8 4#usize :=
  Array.make 4#usize [2#u8, 1#u8, 0#u8, 0#u8]

private def pairCounts22 : Array Std.U8 4#usize :=
  Array.make 4#usize [2#u8, 2#u8, 0#u8, 0#u8]

private def pairFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 2#u8, 0#u8, 0#u8]

theorem rangeNext0End2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 2#usize } =
      ok (some 0#usize, { start := 1#usize, «end» := 2#usize }) := by
  have hmax : 0 < UScalar.max .Usize := by
    have h := (1#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

theorem rangeNext1End2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 2#usize } =
      ok (some 1#usize, { start := 2#usize, «end» := 2#usize }) := by
  have hmax : 1 < UScalar.max .Usize := by
    have h := (2#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

theorem rangeDone2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := 2#usize } =
      ok (none, { start := 2#usize, «end» := 2#usize }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

private theorem pairFindNewStep0 :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (unique1 0#u8) 1#usize 1#u8 0#usize = ok (cont 1#usize) := by
  have indexRun : Array.index_usize (unique1 0#u8) 0#usize = ok 0#u8 := by
    simpa [unique1] using
      (arrayMake4Index0 0#u8 0#u8 0#u8 0#u8)
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun, usizeZeroSucc, Std.lift]

private theorem pairFindNewDone :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (unique1 0#u8) 1#usize 1#u8 1#usize = ok (done 1#usize) := by
  simp [sumcheck.fold_group_tuple_loop0_loop0.body]

private theorem pairFindNewGroup :
    sumcheck.fold_group_tuple_loop0_loop0
        (unique1 0#u8) 1#usize 1#u8 0#usize = ok 1#usize := by
  unfold
    sumcheck.fold_group_tuple_loop0_loop0
  rw [loop.eq_1]
  rw [pairFindNewStep0]
  simp only
  rw [loop.eq_1]
  rw [pairFindNewDone]

private theorem pairFindSecondStep0 :
    sumcheck.fold_group_tuple_loop0_loop0.body
        pairUnique2 2#usize 1#u8 0#usize = ok (cont 1#usize) := by
  have indexRun : Array.index_usize pairUnique2 0#usize = ok 0#u8 := by
    simpa [pairUnique2] using
      (arrayMake4Index0 0#u8 1#u8 0#u8 0#u8)
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun, usizeZeroSucc, Std.lift]

private theorem pairFindSecondDone :
    sumcheck.fold_group_tuple_loop0_loop0.body
        pairUnique2 2#usize 1#u8 1#usize = ok (done 1#usize) := by
  have indexRun : Array.index_usize pairUnique2 1#usize = ok 1#u8 := by
    simpa [pairUnique2] using
      (arrayMake4Index1 0#u8 1#u8 0#u8 0#u8)
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun]

private theorem pairFindSecondGroup :
    sumcheck.fold_group_tuple_loop0_loop0
        pairUnique2 2#usize 1#u8 0#usize = ok 1#usize := by
  unfold
    sumcheck.fold_group_tuple_loop0_loop0
  rw [loop.eq_1]
  rw [pairFindSecondStep0]
  simp only
  rw [loop.eq_1]
  rw [pairFindSecondDone]

theorem usizeOneSucc :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#usize).hSize; scalar_tac)]
  norm_num

theorem castUsizeTwoU8 :
    UScalar.cast .U8 2#usize = 2#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl

theorem usizeTwoSucc :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#usize).hSize; scalar_tac)]
  norm_num

theorem castUsizeOneU8 :
    UScalar.cast .U8 1#usize = 1#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl

private theorem pairOuterStep0
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        groupsPairPair (powers alpha alpha2 alpha3)
        (rangeFrom 0#usize) unique0 coefficients0 unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 0#u8, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  have groupRun : Array.index_usize groupsPairPair 0#usize = ok 0#u8 := by
    simpa [groupsPairPair] using arrayMake4Index0 0#u8 0#u8 1#u8 1#u8
  have uniqueRun : Array.update unique0 0#usize 0#u8 = ok (unique1 0#u8) := by
    have setExact : unique0.set 0#usize 0#u8 = unique1 0#u8 := by
      apply Subtype.ext
      rfl
    rw [← setExact]
    exact arrayUpdateExact unique0 0#usize (by decide) 0#u8
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 0#usize =
      ok field.QM31.ONE := by
    simpa [powers] using arrayMake4Index0 field.QM31.ONE alpha3 alpha2 alpha
  have coefficientRun : Array.update coefficients0 0#usize field.QM31.ONE =
      ok coefficients1 := by
    have setExact : coefficients0.set 0#usize field.QM31.ONE = coefficients1 := by
      apply Subtype.ext
      rfl
    rw [← setExact]
    exact arrayUpdateExact coefficients0 0#usize (by decide) field.QM31.ONE
  have countRun : Array.update unique0 0#usize 1#u8 = ok (countsAt 1#u8) := by
    have setExact : unique0.set 0#usize 1#u8 = countsAt 1#u8 := by
      apply Subtype.ext
      rfl
    rw [← setExact]
    exact arrayUpdateExact unique0 0#usize (by decide) 1#u8
  have slotRun : Array.update slots0 0#usize (UScalar.cast .U8 0#usize) =
      ok slots0 := by
    rw [castUsizeZeroU8]
    have setExact : slots0.set 0#usize 0#u8 = slots0 := by
      apply Subtype.ext
      rfl
    rw [← setExact]
    exact arrayUpdateExact slots0 0#usize (by decide) 0#u8
  unfold sumcheck.fold_group_tuple_loop0.body
  simp only [rangeFrom]
  rw [rangeNext0]
  simp only [bind_tc_ok]
  rw [groupRun]
  simp only [bind_tc_ok]
  rw [findEmpty]
  simp only [bind_tc_ok]
  rw [if_neg (by decide), uniqueRun]
  simp only [bind_tc_ok]
  rw [powerRun]
  simp only [bind_tc_ok]
  rw [coefficientRun]
  simp only [bind_tc_ok]
  rw [countRun]
  simp only [bind_tc_ok, Std.lift]
  rw [slotRun]
  simp only [bind_tc_ok, usizeZeroSucc]

private theorem pairOuterStep1
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run :
      field.QM31.add
          field.QM31.ONE alpha3 =
        ok coefficient0) :
    sumcheck.fold_group_tuple_loop0.body
        groupsPairPair (powers alpha alpha2 alpha3)
        (rangeFrom 1#usize) (unique1 0#u8) coefficients1 (countsAt 1#u8)
        slots0 1#usize =
      ok (cont (rangeFrom 2#usize, unique1 0#u8,
        coefficientsAt coefficient0, countsAt 2#u8, slots0, 1#usize)) := by
  have groupRun : Array.index_usize groupsPairPair 1#usize = ok 0#u8 := by
    simpa [groupsPairPair] using
      (arrayMake4Index1 0#u8 0#u8 1#u8 1#u8)
  have coefficientRun : Array.index_usize coefficients1 0#usize =
      ok field.QM31.ONE := by
    simpa [coefficients1] using
      (arrayMake4Index0
        field.QM31.ONE
        field.QM31.ZERO
        field.QM31.ZERO
        field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 1#usize =
      ok alpha3 := by
    simpa [powers] using
      (arrayMake4Index1
        field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize (countsAt 1#u8) 0#usize = ok 1#u8 := by
    simpa [countsAt] using (arrayMake4Index0 1#u8 0#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun, findExisting, coefficientRun,
    powerRun, coefficient0Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, coefficientsAt, countsAt, slots0,
    Array.update, Std.lift]
  constructor <;> apply Subtype.ext <;> rfl

private theorem pairOuterStep2
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        groupsPairPair (powers alpha alpha2 alpha3)
        (rangeFrom 2#usize) (unique1 0#u8) (coefficientsAt coefficient0)
        (countsAt 2#u8) slots0 1#usize =
      ok (cont (rangeFrom 3#usize, pairUnique2,
        pairCoefficients2 coefficient0 alpha2, pairCounts21, pairFirstSlots,
        2#usize)) := by
  have groupRun : Array.index_usize groupsPairPair 2#usize = ok 1#u8 := by
    simpa [groupsPairPair] using
      (arrayMake4Index2 0#u8 0#u8 1#u8 1#u8)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun, pairFindNewGroup, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficientsAt, countsAt, slots0, pairUnique2,
    pairCoefficients2, pairCounts21, pairFirstSlots, Array.update,
    Std.lift, castUsizeTwoU8, usizeOneSucc]
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

private theorem pairOuterStep3
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 : RawQM31)
    (coefficient1Run :
      field.QM31.add alpha2 alpha =
        ok coefficient1) :
    sumcheck.fold_group_tuple_loop0.body
        groupsPairPair (powers alpha alpha2 alpha3)
        (rangeFrom 3#usize) pairUnique2
        (pairCoefficients2 coefficient0 alpha2) pairCounts21 pairFirstSlots
        2#usize =
      ok (cont (rangeFrom 4#usize, pairUnique2,
        pairCoefficientsFinal coefficient0 coefficient1, pairCounts22,
        pairFirstSlots, 2#usize)) := by
  have groupRun : Array.index_usize groupsPairPair 3#usize = ok 1#u8 := by
    simpa [groupsPairPair] using
      (arrayMake4Index3 0#u8 0#u8 1#u8 1#u8)
  have coefficientRun :
      Array.index_usize (pairCoefficients2 coefficient0 alpha2) 1#usize =
        ok alpha2 := by
    simpa [pairCoefficients2] using
      (arrayMake4Index1 coefficient0 alpha2
        field.QM31.ZERO
        field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize pairCounts21 1#usize = ok 1#u8 := by
    simpa [pairCounts21] using
      (arrayMake4Index1 2#u8 1#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun, pairFindSecondGroup, coefficientRun,
    powerRun, coefficient1Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [pairUnique2, pairCoefficients2, pairCoefficientsFinal, pairCounts21,
    pairCounts22, pairFirstSlots, Array.update, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem pairInnerStep0
    (groupValues : Slice RawQM31)
    (coefficient0 coefficient1 value0 contribution0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (contribution0Run :
      field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (sum0Run :
      field.QM31.add
          field.QM31.ZERO contribution0 =
        ok sum0) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues pairUnique2
        (pairCoefficientsFinal coefficient0 coefficient1) pairCounts22
        pairFirstSlots { start := 0#usize, «end» := 2#usize }
        field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 2#usize }, sum0)) := by
  have uniqueRun : Array.index_usize pairUnique2 0#usize = ok 0#u8 := by
    simpa [pairUnique2] using
      (arrayMake4Index0 0#u8 1#u8 0#u8 0#u8)
  have firstSlotRun : Array.index_usize pairFirstSlots 0#usize = ok 0#u8 := by
    simpa [pairFirstSlots] using
      (arrayMake4Index0 0#u8 2#u8 0#u8 0#u8)
  have countRun : Array.index_usize pairCounts22 0#usize = ok 2#u8 := by
    simpa [pairCounts22] using
      (arrayMake4Index0 2#u8 2#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (pairCoefficientsFinal coefficient0 coefficient1)
          0#usize = ok coefficient0 := by
    simpa [pairCoefficientsFinal] using
      (arrayMake4Index0 coefficient0 coefficient1
        field.QM31.ZERO
        field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext0End2, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, coefficientRun, contribution0Run, sum0Run, Std.lift]

private theorem pairInnerStep1
    (groupValues : Slice RawQM31)
    (coefficient0 coefficient1 value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (contribution1Run :
      field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sum1Run :
      field.QM31.add sum0 contribution1 =
        ok sum1) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues pairUnique2
        (pairCoefficientsFinal coefficient0 coefficient1) pairCounts22
        pairFirstSlots { start := 1#usize, «end» := 2#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 2#usize }, sum1)) := by
  have uniqueRun : Array.index_usize pairUnique2 1#usize = ok 1#u8 := by
    simpa [pairUnique2] using
      (arrayMake4Index1 0#u8 1#u8 0#u8 0#u8)
  have firstSlotRun : Array.index_usize pairFirstSlots 1#usize = ok 2#u8 := by
    simpa [pairFirstSlots] using
      (arrayMake4Index1 0#u8 2#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (pairCoefficientsFinal coefficient0 coefficient1)
          1#usize = ok coefficient1 := by
    simpa [pairCoefficientsFinal] using
      (arrayMake4Index1 coefficient0 coefficient1
        field.QM31.ZERO
        field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext1End2, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem pairInnerDone
    (groupValues : Slice RawQM31)
    (coefficient0 coefficient1 sum1 : RawQM31) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues pairUnique2
        (pairCoefficientsFinal coefficient0 coefficient1) pairCounts22
        pairFirstSlots { start := 2#usize, «end» := 2#usize } sum1 =
      ok (done sum1) := by
  simp [sumcheck.fold_group_tuple_loop1.body,
    rangeDone2]

private theorem pairInnerExact
    (groupValues : Slice RawQM31)
    (coefficient0 coefficient1 value0 value1 contribution0 contribution1
      sum0 sum1 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (contribution0Run :
      field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sum0Run :
      field.QM31.add
          field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      field.QM31.add sum0 contribution1 =
        ok sum1) :
    sumcheck.fold_group_tuple_loop1
        { start := 0#usize, «end» := 2#usize } groupValues pairUnique2
        (pairCoefficientsFinal coefficient0 coefficient1) pairCounts22
        pairFirstSlots field.QM31.ZERO =
      ok sum1 := by
  have step0 := pairInnerStep0 groupValues coefficient0 coefficient1 value0
    contribution0 sum0 value0Run contribution0Run sum0Run
  have step1 := pairInnerStep1 groupValues coefficient0 coefficient1 value1
    contribution1 sum0 sum1 value1Run contribution1Run sum1Run
  have done := pairInnerDone groupValues coefficient0 coefficient1 sum1
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
  rw [done]

private theorem pairPhaseExact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 : RawQM31)
    (coefficient0Run : field.QM31.add field.QM31.ONE alpha3 = ok coefficient0)
    (coefficient1Run : field.QM31.add alpha2 alpha = ok coefficient1) :
    sumcheck.fold_group_tuple_loop0 (rangeFrom 0#usize) groupsPairPair
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0 slots0
        0#usize = ok (pairUnique2, pairCoefficientsFinal coefficient0 coefficient1,
          pairCounts22, pairFirstSlots, 2#usize) := by
  have step0 := pairOuterStep0 groupValues alpha alpha2 alpha3
  have step1 := pairOuterStep1 groupValues alpha alpha2 alpha3 coefficient0
    coefficient0Run
  have step2 := pairOuterStep2 groupValues alpha alpha2 alpha3 coefficient0
  have step3 := pairOuterStep3 groupValues alpha alpha2 alpha3 coefficient0
    coefficient1 coefficient1Run
  unfold sumcheck.fold_group_tuple_loop0
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
  unfold sumcheck.fold_group_tuple_loop0.body
  simp only [rangeFrom]
  rw [rangeDone4]
  rfl

theorem pairPairSourceExact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1
      contribution0 contribution1 sum0 sum1 half1 out : RawQM31)
    (coefficient0Run : field.QM31.add field.QM31.ONE alpha3 = ok coefficient0)
    (coefficient1Run : field.QM31.add alpha2 alpha = ok coefficient1)
    (value0Run : Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (value1Run : Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (contribution0Run : field.QM31.mul value0 coefficient0 = ok contribution0)
    (contribution1Run : field.QM31.mul value1 coefficient1 = ok contribution1)
    (sum0Run : field.QM31.add field.QM31.ZERO contribution0 = ok sum0)
    (sum1Run : field.QM31.add sum0 contribution1 = ok sum1)
    (half1Run : field.QM31.half sum1 = ok half1)
    (outRun : field.QM31.half half1 = ok out) :
    sumcheck.fold_group_tuple groupsPairPair groupValues alpha alpha2 alpha3 = ok out := by
  have phaseRun := pairPhaseExact groupValues alpha alpha2 alpha3 coefficient0
    coefficient1 coefficient0Run coefficient1Run
  have phaseRunExpanded :
      sumcheck.fold_group_tuple_loop0
          { start := 0#usize, «end» := 4#usize } groupsPairPair
          (Array.make 4#usize [field.QM31.ONE, alpha3, alpha2, alpha])
          (Array.repeat 4#usize 0#u8)
          (Array.repeat 4#usize field.QM31.ZERO)
          (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize 0#u8) 0#usize =
        ok (pairUnique2, pairCoefficientsFinal coefficient0 coefficient1,
          pairCounts22, pairFirstSlots, 2#usize) := by
    simpa only [rangeFrom, powers, unique0, coefficients0, slots0] using
      phaseRun
  have contributionRun := pairInnerExact groupValues coefficient0 coefficient1
    value0 value1 contribution0 contribution1 sum0 sum1 value0Run value1Run
    contribution0Run contribution1Run sum0Run sum1Run
  unfold sumcheck.fold_group_tuple
  dsimp only
  rw [phaseRunExpanded]
  simp only [bind_tc_ok]
  rw [contributionRun]
  simp only [bind_tc_ok]
  rw [half1Run]
  simp only [bind_tc_ok]
  exact outRun

theorem pairPairSourceCorresponds
    (groupValues : Slice RawQM31)
    (value0 value1 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (value0Canonical : GeneratedCanonicalQM31 value0)
    (value1Canonical : GeneratedCanonicalQM31 value1)
    (alphaCanonical : GeneratedCanonicalQM31 alpha)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2)
    (alpha3Canonical : GeneratedCanonicalQM31 alpha3)
    (alpha2Exact : exactRaw alpha2 = exactRaw alpha ^ 2)
    (alpha3Exact : exactRaw alpha3 = exactRaw alpha ^ 3) :
    ∃ out,
      sumcheck.fold_group_tuple
          groupsPairPair groupValues alpha alpha2 alpha3 = ok out ∧
      GeneratedCanonicalQM31 out ∧
      exactRaw out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (exactRaw alpha)
          (fun index => ![exactRaw value0, exactRaw value0,
            exactRaw value1, exactRaw value1] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    generated_qm31_add_corresponds
      field.QM31.ONE alpha3
      oneCanonical alpha3Canonical
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical,
      coefficient1Exact⟩ :=
    generated_qm31_add_corresponds alpha2 alpha alpha2Canonical alphaCanonical
  obtain ⟨contribution0, contribution0Run, contribution0Canonical,
      contribution0Exact⟩ :=
    generated_qm31_mul_corresponds value0 coefficient0 value0Canonical
      coefficient0Canonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 coefficient1 value1Canonical
      coefficient1Canonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      field.QM31.ZERO contribution0
      zeroCanonical contribution0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum1 sum1Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := pairPairSourceExact groupValues alpha alpha2 alpha3
    coefficient0 coefficient1 value0 value1 contribution0 contribution1
    sum0 sum1 half1 out coefficient0Run coefficient1Run value0Run value1Run
    contribution0Run contribution1Run sum0Run sum1Run half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient0ExactM := congrArg sourceQm31ToModel coefficient0Exact
  have coefficient1ExactM := congrArg sourceQm31ToModel coefficient1Exact
  have contribution0ExactM := congrArg sourceQm31ToModel contribution0Exact
  have contribution1ExactM := congrArg sourceQm31ToModel contribution1Exact
  have sum0ExactM := congrArg sourceQm31ToModel sum0Exact
  have sum1ExactM := congrArg sourceQm31ToModel sum1Exact
  have half1ExactM := congrArg sourceQm31ToModel half1Exact
  have outExactM := congrArg sourceQm31ToModel outExact
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at coefficient0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at coefficient1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at half1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at outExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution1ExactM
  have oneExact :
      exactRaw
          field.QM31.ONE = 1 := by
    rw [field.QM31.ONE]
    rfl
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
    _ = exactRaw sum1 := half1ExactM
    _ = exactRaw sum0 + exactRaw contribution1 := sum1ExactM
    _ = (exactRaw
          field.QM31.ZERO +
          exactRaw contribution0) +
        exactRaw contribution1 := by rw [sum0ExactM]
    _ = exactRaw value0 * exactRaw coefficient0 +
        exactRaw value1 * exactRaw coefficient1 := by
      rw [zeroExact, contribution0ExactM, contribution1ExactM]
      ring
    _ = exactRaw value0 *
          ((1 : ExactQM31) + exactRaw alpha ^ 3) +
        exactRaw value1 *
          (exactRaw alpha ^ 2 + exactRaw alpha) := by
      rw [coefficient0ExactM, coefficient1ExactM, oneExact, alpha2Exact,
        alpha3Exact]
    _ = exactRaw value0 +
        exactRaw alpha ^ 3 * exactRaw value0 +
        exactRaw alpha ^ 2 * exactRaw value1 +
        exactRaw alpha * exactRaw value1 := by ring

/-! ## The released `[1, 1, 1, 2]` tuple -/


#print axioms pairPhaseExact
#print axioms pairPairSourceExact
#print axioms pairPairSourceCorresponds
end V7CallerCurrentReleaseR26GroupedPairPair
