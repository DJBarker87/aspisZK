import V7CallerCurrentReleaseR26GroupedOneThree

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

namespace V7CallerCurrentReleaseR26GroupedThreeAround

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def groupsThreeAround (group0 group1 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group0, group0]

def threeAroundCoefficients11
    (alpha3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    field.QM31.ONE, alpha3,
    field.QM31.ZERO,
    field.QM31.ZERO]

def threeAroundCoefficientsAt
    (coefficient alpha3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient, alpha3,
    field.QM31.ZERO,
    field.QM31.ZERO]

def threeAroundCounts21 : Array Std.U8 4#usize :=
  Array.make 4#usize [2#u8, 1#u8, 0#u8, 0#u8]

private def threeAroundCounts31 : Array Std.U8 4#usize :=
  Array.make 4#usize [3#u8, 1#u8, 0#u8, 0#u8]

private theorem threeAroundFindFirstDone
    (group0 group1 : Std.U8) :
    sumcheck.fold_group_tuple_loop0_loop0.body
        (oneThreeUnique2 group0 group1) 2#usize group0 0#usize =
      ok (done 0#usize) := by
  have indexRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 0#usize =
        ok group0 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index0 group0 group1 0#u8 0#u8)
  simp [sumcheck.fold_group_tuple_loop0_loop0.body,
    indexRun]

theorem threeAroundFindFirst
    (group0 group1 : Std.U8) :
    sumcheck.fold_group_tuple_loop0_loop0
        (oneThreeUnique2 group0 group1) 2#usize group0 0#usize =
      ok 0#usize := by
  unfold
    sumcheck.fold_group_tuple_loop0_loop0
  rw [loop.eq_1]
  rw [threeAroundFindFirstDone]

private theorem threeAroundOuterStep0
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsThreeAround group0 group1)
        (powers alpha alpha2 alpha3) (rangeFrom 0#usize) unique0 coefficients0
        unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  apply phaseFirstStep
  simpa [groupsThreeAround] using
    arrayMake4Index0 group0 group1 group0 group0

private theorem threeAroundOuterStep1
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsThreeAround group0 group1)
        (powers alpha alpha2 alpha3) (rangeFrom 1#usize) (unique1 group0)
        coefficients1 (countsAt 1#u8) slots0 1#usize =
      ok (cont (rangeFrom 2#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficients11 alpha3, oneThreeCounts11,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsThreeAround group0 group1) 1#usize =
        ok group1 := by
    simpa [groupsThreeAround] using
      (arrayMake4Index1 group0 group1 group0 group0)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 1#usize =
      ok alpha3 := by
    simpa [powers] using
      (arrayMake4Index1
        field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun,
    oneThreeFindNew group0 group1 different, powerRun]
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

private theorem threeAroundOuterStep2
    (group0 group1 : Std.U8)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run :
      field.QM31.add
          field.QM31.ONE alpha2 =
        ok coefficient0) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsThreeAround group0 group1)
        (powers alpha alpha2 alpha3) (rangeFrom 2#usize)
        (oneThreeUnique2 group0 group1) (threeAroundCoefficients11 alpha3)
        oneThreeCounts11 oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 3#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficientsAt coefficient0 alpha3, threeAroundCounts21,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsThreeAround group0 group1) 2#usize =
        ok group0 := by
    simpa [groupsThreeAround] using
      (arrayMake4Index2 group0 group1 group0 group0)
  have coefficientRun :
      Array.index_usize (threeAroundCoefficients11 alpha3) 0#usize =
        ok field.QM31.ONE := by
    simpa [threeAroundCoefficients11] using
      (arrayMake4Index0
        field.QM31.ONE alpha3
        field.QM31.ZERO
        field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize oneThreeCounts11 0#usize = ok 1#u8 := by
    simpa [oneThreeCounts11] using
      (arrayMake4Index0 1#u8 1#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun,
    threeAroundFindFirst group0 group1, coefficientRun, powerRun,
    coefficient0Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficients11,
    threeAroundCoefficientsAt, oneThreeCounts11, threeAroundCounts21,
    oneThreeFirstSlots, Array.update, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem threeAroundOuterStep3
    (group0 group1 : Std.U8)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 : RawQM31)
    (coefficient1Run :
      field.QM31.add coefficient0 alpha =
        ok coefficient1) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsThreeAround group0 group1)
        (powers alpha alpha2 alpha3) (rangeFrom 3#usize)
        (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts21
        oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 4#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficientsAt coefficient1 alpha3, threeAroundCounts31,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsThreeAround group0 group1) 3#usize =
        ok group0 := by
    simpa [groupsThreeAround] using
      (arrayMake4Index3 group0 group1 group0 group0)
  have coefficientRun :
      Array.index_usize (threeAroundCoefficientsAt coefficient0 alpha3)
          0#usize = ok coefficient0 := by
    simpa [threeAroundCoefficientsAt] using
      (arrayMake4Index0 coefficient0 alpha3
        field.QM31.ZERO
        field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize threeAroundCounts21 0#usize = ok 2#u8 := by
    simpa [threeAroundCounts21] using
      (arrayMake4Index0 2#u8 1#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    threeAroundFindFirst group0 group1, coefficientRun, powerRun,
    coefficient1Run, countRun, u8TwoSucc]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficientsAt, threeAroundCounts21,
    threeAroundCounts31, oneThreeFirstSlots, Array.update, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem threeAroundInnerStep0
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 value0 contribution0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (contribution0Run :
      field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (sum0Run :
      field.QM31.add
          field.QM31.ZERO contribution0 =
        ok sum0) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts31
        oneThreeFirstSlots { start := 0#usize, «end» := 2#usize }
        field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 2#usize }, sum0)) := by
  have uniqueRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 0#usize =
        ok group0 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index0 group0 group1 0#u8 0#u8)
  have firstSlotRun :
      Array.index_usize oneThreeFirstSlots 0#usize = ok 0#u8 := by
    simpa [oneThreeFirstSlots] using
      (arrayMake4Index0 0#u8 1#u8 0#u8 0#u8)
  have countRun : Array.index_usize threeAroundCounts31 0#usize = ok 3#u8 := by
    simpa [threeAroundCounts31] using
      (arrayMake4Index0 3#u8 1#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (threeAroundCoefficientsAt coefficient0 alpha3)
          0#usize = ok coefficient0 := by
    simpa [threeAroundCoefficientsAt] using
      (arrayMake4Index0 coefficient0 alpha3
        field.QM31.ZERO
        field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext0End2, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, coefficientRun, contribution0Run, sum0Run, Std.lift]

private theorem threeAroundInnerStep1
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum1Run :
      field.QM31.add sum0 contribution1 =
        ok sum1) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts31
        oneThreeFirstSlots { start := 1#usize, «end» := 2#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 2#usize }, sum1)) := by
  have uniqueRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 1#usize =
        ok group1 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index1 group0 group1 0#u8 0#u8)
  have firstSlotRun :
      Array.index_usize oneThreeFirstSlots 1#usize = ok 1#u8 := by
    simpa [oneThreeFirstSlots] using
      (arrayMake4Index1 0#u8 1#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (threeAroundCoefficientsAt coefficient0 alpha3)
          1#usize = ok alpha3 := by
    simpa [threeAroundCoefficientsAt] using
      (arrayMake4Index1 coefficient0 alpha3
        field.QM31.ZERO
        field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop1.body,
    rangeNext1End2, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem threeAroundInnerDone
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 sum1 : RawQM31) :
    sumcheck.fold_group_tuple_loop1.body
        groupValues (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts31
        oneThreeFirstSlots { start := 2#usize, «end» := 2#usize } sum1 =
      ok (done sum1) := by
  simp [sumcheck.fold_group_tuple_loop1.body,
    rangeDone2]

private theorem threeAroundInnerExact
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 value0 value1 contribution0 contribution1 sum0 sum1 :
      RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution0Run :
      field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum0Run :
      field.QM31.add
          field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      field.QM31.add sum0 contribution1 =
        ok sum1) :
    sumcheck.fold_group_tuple_loop1
        { start := 0#usize, «end» := 2#usize } groupValues
        (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts31
        oneThreeFirstSlots field.QM31.ZERO =
      ok sum1 := by
  have step0 := threeAroundInnerStep0 group0 group1 groupValues coefficient0
    alpha3 value0 contribution0 sum0 value0Run contribution0Run sum0Run
  have step1 := threeAroundInnerStep1 group0 group1 groupValues coefficient0
    alpha3 value1 contribution1 sum0 sum1 value1Run contribution1Run sum1Run
  have done := threeAroundInnerDone group0 group1 groupValues coefficient0
    alpha3 sum1
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

private theorem threeAroundPhaseExact
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 : RawQM31)
    (coefficient0Run : field.QM31.add field.QM31.ONE alpha2 = ok coefficient0)
    (coefficient1Run : field.QM31.add coefficient0 alpha = ok coefficient1) :
    sumcheck.fold_group_tuple_loop0 (rangeFrom 0#usize)
        (groupsThreeAround group0 group1) (powers alpha alpha2 alpha3) unique0
        coefficients0 unique0 slots0 0#usize =
      ok (oneThreeUnique2 group0 group1,
        threeAroundCoefficientsAt coefficient1 alpha3, threeAroundCounts31,
        oneThreeFirstSlots, 2#usize) := by
  have step0 := threeAroundOuterStep0 group0 group1 groupValues alpha alpha2 alpha3
  have step1 := threeAroundOuterStep1 group0 group1 different groupValues alpha alpha2 alpha3
  have step2 := threeAroundOuterStep2 group0 group1 groupValues alpha alpha2 alpha3 coefficient0 coefficient0Run
  have step3 := threeAroundOuterStep3 group0 group1 groupValues alpha alpha2 alpha3 coefficient0 coefficient1 coefficient1Run
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

theorem threeAroundSourceExact
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1
      contribution0 contribution1 sum0 sum1 half1 out : RawQM31)
    (coefficient0Run : field.QM31.add field.QM31.ONE alpha2 = ok coefficient0)
    (coefficient1Run : field.QM31.add coefficient0 alpha = ok coefficient1)
    (value0Run : Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run : Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution0Run : field.QM31.mul value0 coefficient1 = ok contribution0)
    (contribution1Run : field.QM31.mul value1 alpha3 = ok contribution1)
    (sum0Run : field.QM31.add field.QM31.ZERO contribution0 = ok sum0)
    (sum1Run : field.QM31.add sum0 contribution1 = ok sum1)
    (half1Run : field.QM31.half sum1 = ok half1)
    (outRun : field.QM31.half half1 = ok out) :
    sumcheck.fold_group_tuple (groupsThreeAround group0 group1) groupValues alpha alpha2 alpha3 = ok out := by
  have phaseRun := threeAroundPhaseExact group0 group1 different groupValues alpha alpha2 alpha3 coefficient0 coefficient1 coefficient0Run coefficient1Run
  have phaseRunExpanded :
      sumcheck.fold_group_tuple_loop0 { start := 0#usize, «end» := 4#usize }
        (groupsThreeAround group0 group1)
        (Array.make 4#usize [field.QM31.ONE, alpha3, alpha2, alpha])
        (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize field.QM31.ZERO)
        (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize 0#u8) 0#usize =
      ok (oneThreeUnique2 group0 group1,
        threeAroundCoefficientsAt coefficient1 alpha3, threeAroundCounts31,
        oneThreeFirstSlots, 2#usize) := by
    simpa only [rangeFrom, powers, unique0, coefficients0, slots0] using phaseRun
  have contributionRun := threeAroundInnerExact group0 group1 groupValues coefficient1 alpha3
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

theorem threeAroundSourceCorresponds
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (value0 value1 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value0Canonical : GeneratedCanonicalQM31 value0)
    (value1Canonical : GeneratedCanonicalQM31 value1)
    (alphaCanonical : GeneratedCanonicalQM31 alpha)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2)
    (alpha3Canonical : GeneratedCanonicalQM31 alpha3)
    (alpha2Exact : exactRaw alpha2 = exactRaw alpha ^ 2)
    (alpha3Exact : exactRaw alpha3 = exactRaw alpha ^ 3) :
    ∃ out,
      sumcheck.fold_group_tuple
          (groupsThreeAround group0 group1) groupValues alpha alpha2 alpha3 =
        ok out ∧
      GeneratedCanonicalQM31 out ∧
      exactRaw out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (exactRaw alpha)
          (fun index => ![exactRaw value0, exactRaw value1,
            exactRaw value0, exactRaw value0] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    generated_qm31_add_corresponds
      field.QM31.ONE alpha2
      oneCanonical alpha2Canonical
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical,
      coefficient1Exact⟩ :=
    generated_qm31_add_corresponds coefficient0 alpha coefficient0Canonical
      alphaCanonical
  obtain ⟨contribution0, contribution0Run, contribution0Canonical,
      contribution0Exact⟩ :=
    generated_qm31_mul_corresponds value0 coefficient1 value0Canonical
      coefficient1Canonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha3 value1Canonical
      alpha3Canonical
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
  have sourceRun := threeAroundSourceExact group0 group1 different groupValues
    alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1 contribution0
    contribution1 sum0 sum1 half1 out coefficient0Run coefficient1Run
    value0Run value1Run contribution0Run contribution1Run sum0Run sum1Run
    half1Run outRun
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
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at half1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at outExactM
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
    _ = exactRaw value0 * exactRaw coefficient1 +
        exactRaw value1 * exactRaw alpha3 := by
      rw [zeroExact, contribution0ExactM, contribution1ExactM]
      ring
    _ = exactRaw value0 *
          (((1 : ExactQM31) + exactRaw alpha ^ 2) +
            exactRaw alpha) +
        exactRaw value1 * exactRaw alpha ^ 3 := by
      rw [coefficient1ExactM, coefficient0ExactM, oneExact, alpha2Exact,
        alpha3Exact]
    _ = exactRaw value0 +
        exactRaw alpha ^ 3 * exactRaw value1 +
        exactRaw alpha ^ 2 * exactRaw value0 +
        exactRaw alpha * exactRaw value0 := by ring

#print axioms threeAroundPhaseExact
#print axioms threeAroundSourceExact
#print axioms threeAroundSourceCorresponds
end V7CallerCurrentReleaseR26GroupedThreeAround
