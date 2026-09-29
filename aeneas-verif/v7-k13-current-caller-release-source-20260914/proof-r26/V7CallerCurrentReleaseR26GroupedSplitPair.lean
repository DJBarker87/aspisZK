import V7CallerCurrentReleaseR26GroupedLastPair

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

namespace V7CallerCurrentReleaseR26GroupedSplitPair

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def groupsSplitPair
    (group0 group1 group2 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group0, group2]

private def splitPairCoefficientsFinal
    (coefficient0 alpha3 alpha : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0, alpha3, alpha,
    field.QM31.ZERO]

private def splitPairCounts211 : Array Std.U8 4#usize :=
  Array.make 4#usize [2#u8, 1#u8, 1#u8, 0#u8]

private def splitPairFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 3#u8, 0#u8]

private theorem splitPairOuterStep0
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsSplitPair group0 group1 group2)
        (powers alpha alpha2 alpha3) (rangeFrom 0#usize) unique0 coefficients0
        unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  apply phaseFirstStep
  simpa [groupsSplitPair] using
    arrayMake4Index0 group0 group1 group0 group2

private theorem splitPairOuterStep1
    (group0 group1 group2 : Std.U8) (different01 : group0 ≠ group1)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsSplitPair group0 group1 group2)
        (powers alpha alpha2 alpha3) (rangeFrom 1#usize) (unique1 group0)
        coefficients1 (countsAt 1#u8) slots0 1#usize =
      ok (cont (rangeFrom 2#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficients11 alpha3, oneThreeCounts11,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsSplitPair group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [groupsSplitPair] using
      (arrayMake4Index1 group0 group1 group0 group2)
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

private theorem splitPairOuterStep2
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run :
      field.QM31.add
          field.QM31.ONE alpha2 =
        ok coefficient0) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsSplitPair group0 group1 group2)
        (powers alpha alpha2 alpha3) (rangeFrom 2#usize)
        (oneThreeUnique2 group0 group1) (threeAroundCoefficients11 alpha3)
        oneThreeCounts11 oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 3#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficientsAt coefficient0 alpha3, threeAroundCounts21,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsSplitPair group0 group1 group2) 2#usize =
        ok group0 := by
    simpa [groupsSplitPair] using
      (arrayMake4Index2 group0 group1 group0 group2)
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

private theorem splitPairOuterStep3
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsSplitPair group0 group1 group2)
        (powers alpha alpha2 alpha3) (rangeFrom 3#usize)
        (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts21
        oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 4#usize, lastPairUnique3 group0 group1 group2,
        splitPairCoefficientsFinal coefficient0 alpha3 alpha,
        splitPairCounts211, splitPairFirstSlots, 3#usize)) := by
  have groupRun :
      Array.index_usize (groupsSplitPair group0 group1 group2) 3#usize =
        ok group2 := by
    simpa [groupsSplitPair] using
      (arrayMake4Index3 group0 group1 group0 group2)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    lastPairFindNew group0 group1 group2 different02 different12, powerRun]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficientsAt, threeAroundCounts21,
    oneThreeFirstSlots, lastPairUnique3, splitPairCoefficientsFinal,
    splitPairCounts211, splitPairFirstSlots, Array.update, Std.lift,
    castUsizeThreeU8, usizeTwoSucc]
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

private theorem splitPairInnerExact
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 alpha value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 : RawQM31)
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
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      field.QM31.mul
          value2 alpha = ok contribution2)
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
        { start := 0#usize, «end» := 3#usize } groupValues
        (lastPairUnique3 group0 group1 group2)
        (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
        splitPairCounts211 splitPairFirstSlots
        field.QM31.ZERO = ok sum2 := by
  have unique0Run :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 0#usize =
        ok group0 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index0 group0 group1 group2 0#u8)
  have unique1Run :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index1 group0 group1 group2 0#u8)
  have unique2Run :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index2 group0 group1 group2 0#u8)
  have firstSlot0Run :
      Array.index_usize splitPairFirstSlots 0#usize = ok 0#u8 := by
    simpa [splitPairFirstSlots] using
      (arrayMake4Index0 0#u8 1#u8 3#u8 0#u8)
  have firstSlot1Run :
      Array.index_usize splitPairFirstSlots 1#usize = ok 1#u8 := by
    simpa [splitPairFirstSlots] using
      (arrayMake4Index1 0#u8 1#u8 3#u8 0#u8)
  have firstSlot2Run :
      Array.index_usize splitPairFirstSlots 2#usize = ok 3#u8 := by
    simpa [splitPairFirstSlots] using
      (arrayMake4Index2 0#u8 1#u8 3#u8 0#u8)
  have count0Run : Array.index_usize splitPairCounts211 0#usize = ok 2#u8 := by
    simpa [splitPairCounts211] using
      (arrayMake4Index0 2#u8 1#u8 1#u8 0#u8)
  have coefficient0Run :
      Array.index_usize (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
          0#usize = ok coefficient0 := by
    simpa [splitPairCoefficientsFinal] using
      (arrayMake4Index0 coefficient0 alpha3 alpha
        field.QM31.ZERO)
  have coefficient1Run :
      Array.index_usize (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
          1#usize = ok alpha3 := by
    simpa [splitPairCoefficientsFinal] using
      (arrayMake4Index1 coefficient0 alpha3 alpha
        field.QM31.ZERO)
  have coefficient2Run :
      Array.index_usize (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
          2#usize = ok alpha := by
    simpa [splitPairCoefficientsFinal] using
      (arrayMake4Index2 coefficient0 alpha3 alpha
        field.QM31.ZERO)
  exact threeMultiplyInnerExact groupValues
    (lastPairUnique3 group0 group1 group2)
    (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
    splitPairCounts211 splitPairFirstSlots group0 group1 group2 0#u8 2#u8
    1#u8 3#u8 coefficient0 alpha3 alpha value0 value1 value2 contribution0
    contribution1 contribution2 sum0 sum1 sum2 unique0Run unique1Run
    unique2Run firstSlot0Run firstSlot1Run firstSlot2Run count0Run rfl
    (by decide) (by decide) (by decide) coefficient0Run coefficient1Run
    coefficient2Run value0Run value1Run value2Run contribution0Run
    contribution1Run contribution2Run sum0Run sum1Run sum2Run

private theorem splitPairPhaseExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run : field.QM31.add field.QM31.ONE alpha2 = ok coefficient0) :
    sumcheck.fold_group_tuple_loop0 (rangeFrom 0#usize)
        (groupsSplitPair group0 group1 group2) (powers alpha alpha2 alpha3)
        unique0 coefficients0 unique0 slots0 0#usize =
      ok (lastPairUnique3 group0 group1 group2,
        splitPairCoefficientsFinal coefficient0 alpha3 alpha, splitPairCounts211,
        splitPairFirstSlots, 3#usize) := by
  have step0 := splitPairOuterStep0 group0 group1 group2 groupValues alpha alpha2 alpha3
  have step1 := splitPairOuterStep1 group0 group1 group2 different01 groupValues alpha alpha2 alpha3
  have step2 := splitPairOuterStep2 group0 group1 group2 groupValues alpha alpha2 alpha3 coefficient0 coefficient0Run
  have step3 := splitPairOuterStep3 group0 group1 group2 different02 different12 groupValues alpha alpha2 alpha3 coefficient0
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

theorem splitPairSourceExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (coefficient0Run : field.QM31.add field.QM31.ONE alpha2 = ok coefficient0)
    (value0Run : Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run : Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run : Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run : field.QM31.mul value0 coefficient0 = ok contribution0)
    (contribution1Run : field.QM31.mul value1 alpha3 = ok contribution1)
    (contribution2Run : field.QM31.mul value2 alpha = ok contribution2)
    (sum0Run : field.QM31.add field.QM31.ZERO contribution0 = ok sum0)
    (sum1Run : field.QM31.add sum0 contribution1 = ok sum1)
    (sum2Run : field.QM31.add sum1 contribution2 = ok sum2)
    (half1Run : field.QM31.half sum2 = ok half1)
    (outRun : field.QM31.half half1 = ok out) :
    sumcheck.fold_group_tuple (groupsSplitPair group0 group1 group2) groupValues alpha alpha2 alpha3 = ok out := by
  have phaseRun := splitPairPhaseExact group0 group1 group2 different01 different02 different12 groupValues alpha alpha2 alpha3 coefficient0 coefficient0Run
  have phaseRunExpanded :
      sumcheck.fold_group_tuple_loop0 { start := 0#usize, «end» := 4#usize }
        (groupsSplitPair group0 group1 group2)
        (Array.make 4#usize [field.QM31.ONE, alpha3, alpha2, alpha])
        (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize field.QM31.ZERO)
        (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize 0#u8) 0#usize =
      ok (lastPairUnique3 group0 group1 group2,
        splitPairCoefficientsFinal coefficient0 alpha3 alpha, splitPairCounts211,
        splitPairFirstSlots, 3#usize) := by
    simpa only [rangeFrom, powers, unique0, coefficients0, slots0] using phaseRun
  have contributionRun := splitPairInnerExact group0 group1 group2 groupValues coefficient0 alpha3 alpha
    value0 value1 value2 contribution0 contribution1 contribution2 sum0 sum1 sum2
    value0Run value1Run value2Run contribution0Run contribution1Run contribution2Run
    sum0Run sum1Run sum2Run
  unfold sumcheck.fold_group_tuple
  dsimp only
  rw [phaseRunExpanded]
  simp only [bind_tc_ok]
  rw [contributionRun]
  simp only [bind_tc_ok]
  rw [half1Run]
  simp only [bind_tc_ok]
  exact outRun

theorem splitPairSourceCorresponds
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
          (groupsSplitPair group0 group1 group2) groupValues alpha alpha2 alpha3 =
        ok out ∧
      GeneratedCanonicalQM31 out ∧
      exactRaw out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (exactRaw alpha)
          (fun index => ![exactRaw value0, exactRaw value1,
            exactRaw value0, exactRaw value2] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    generated_qm31_add_corresponds
      field.QM31.ONE alpha2
      oneCanonical alpha2Canonical
  obtain ⟨contribution0, contribution0Run, contribution0Canonical,
      contribution0Exact⟩ :=
    generated_qm31_mul_corresponds value0 coefficient0 value0Canonical
      coefficient0Canonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha3 value1Canonical
      alpha3Canonical
  obtain ⟨contribution2, contribution2Run, contribution2Canonical,
      contribution2Exact⟩ :=
    generated_qm31_mul_corresponds value2 alpha value2Canonical alphaCanonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      field.QM31.ZERO contribution0
      zeroCanonical contribution0Canonical
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
  have sourceRun := splitPairSourceExact group0 group1 group2 different01
    different02 different12 groupValues alpha alpha2 alpha3 coefficient0
    value0 value1 value2 contribution0 contribution1 contribution2 sum0 sum1
    sum2 half1 out coefficient0Run value0Run value1Run value2Run
    contribution0Run contribution1Run contribution2Run sum0Run sum1Run sum2Run
    half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient0ExactM := congrArg sourceQm31ToModel coefficient0Exact
  have contribution0ExactM := congrArg sourceQm31ToModel contribution0Exact
  have contribution1ExactM := congrArg sourceQm31ToModel contribution1Exact
  have contribution2ExactM := congrArg sourceQm31ToModel contribution2Exact
  have sum0ExactM := congrArg sourceQm31ToModel sum0Exact
  have sum1ExactM := congrArg sourceQm31ToModel sum1Exact
  have sum2ExactM := congrArg sourceQm31ToModel sum2Exact
  have half1ExactM := congrArg sourceQm31ToModel half1Exact
  have outExactM := congrArg sourceQm31ToModel outExact
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at coefficient0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_mul] at contribution2ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum0ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum1ExactM
  simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add] at sum2ExactM
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
    _ = exactRaw sum2 := half1ExactM
    _ = exactRaw sum1 + exactRaw contribution2 := sum2ExactM
    _ = (exactRaw sum0 + exactRaw contribution1) +
        exactRaw contribution2 := by rw [sum1ExactM]
    _ = ((exactRaw
          field.QM31.ZERO +
          exactRaw contribution0) + exactRaw contribution1) +
        exactRaw contribution2 := by rw [sum0ExactM]
    _ = exactRaw value0 * exactRaw coefficient0 +
        exactRaw value1 * exactRaw alpha3 +
        exactRaw value2 * exactRaw alpha := by
      rw [zeroExact, contribution0ExactM, contribution1ExactM,
        contribution2ExactM]
      ring
    _ = exactRaw value0 *
          ((1 : ExactQM31) + exactRaw alpha ^ 2) +
        exactRaw value1 * exactRaw alpha ^ 3 +
        exactRaw value2 * exactRaw alpha := by
      rw [coefficient0ExactM, oneExact, alpha2Exact, alpha3Exact]
    _ = exactRaw value0 +
        exactRaw alpha ^ 3 * exactRaw value1 +
        exactRaw alpha ^ 2 * exactRaw value0 +
        exactRaw alpha * exactRaw value2 := by ring

#print axioms splitPairPhaseExact
#print axioms splitPairSourceExact
#print axioms splitPairSourceCorresponds
end V7CallerCurrentReleaseR26GroupedSplitPair
