import V7CallerCurrentReleaseR26GroupedRowsTwiceFourOutputs
import V7CallerCurrentReleaseR26GroupedMaskFormulas

/-! # K1 semantics of the optimized two-round grouped fold -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsStaged
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26GroupedFoldDenominator
open V7CallerCurrentReleaseR26GroupedMaskFormulas
open V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalOps
open V7CallerCurrentReleaseR26GroupedRowsTwiceFourOutputs
open V7CallerCurrentReleaseR26GroupedRowsTwiceTrace

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

@[simp] private theorem sourceMapPow
    (value : ExactQM31) (power : Nat) :
    sourceQm31ToModel (value ^ power) =
      sourceQm31ToModel value ^ power := by
  change sourceQm31ToModelHom (value ^ power) =
    sourceQm31ToModelHom value ^ power
  exact map_pow sourceQm31ToModelHom value power

@[simp] private theorem sourceMapSixteen :
    sourceQm31ToModel (16 : ExactQM31) =
      (16 : AspisV5ComponentCQM31TowerExact.QM31Exact) := by
  change sourceQm31ToModelHom 16 = 16
  exact map_ofNat sourceQm31ToModelHom 16

@[simp] private theorem sourceMapGenerated (value : RawQM31) :
    sourceQm31ToModel (generatedQm31ToExact value) = exactRaw value := rfl

@[simp] private theorem sourceMapExact (value : CanonicalRaw) :
    sourceQm31ToModel (exact value) = exactRaw value.raw := rfl

private theorem inverseFourSquareTimesSixteen :
    (4 : ModelQM31)⁻¹ ^ 2 * 16 = 1 := by
  have hfour : (4 : ModelQM31) ≠ 0 :=
    V7CallerCurrentReleaseR26GroupedMaskFormulas.four_ne_zero
  rw [inv_pow, mul_comm]
  change 16 / (4 : ModelQM31) ^ 2 = 1
  rw [div_eq_iff (pow_ne_zero 2 hfour)]
  norm_num

@[simp] private theorem mulInverseFourSquareTimesSixteen (value : ModelQM31) :
    value * (4 : ModelQM31)⁻¹ ^ 2 * 16 = value := by
  rw [mul_assoc, inverseFourSquareTimesSixteen, mul_one]

private theorem four_outputs_have_k1_meaning
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31)
    (alpha1 alpha2 : RawQM31)
    (foldedGroups : alloc.vec.Vec Std.U8)
    (foldedValues : alloc.vec.Vec RawQM31)
    (source : GroupedRowsTwiceSourceTrace
      (alloc.vec.Vec.deref releasedRowGroups64)
      (alloc.vec.Vec.deref
        (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))
      alpha1 alpha2 foldedGroups foldedValues)
    (outputs : FourOutputs value0 value1 value2 value3 value4 value5 value6
      alpha1 alpha2 foldedGroups foldedValues source) :
    representedGroupedWeights releasedRowGroups4
        (releasedFourValues outputs.out0.raw outputs.out1.raw
          outputs.out2.raw outputs.out3.raw) =
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
        (exactRaw alpha2)
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (exactRaw alpha1)
          (representedGroupedWeights releasedRowGroups64
            (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))) := by
  have mapEquation (left right : ExactQM31) (equation : left = right) :
      sourceQm31ToModel left = sourceQm31ToModel right :=
    congrArg sourceQm31ToModel equation
  have b0Exact : exactRaw outputs.basis.b0.raw = 1 := by
    have h := mapEquation _ _ outputs.basis.b0Exact
    change exactRaw outputs.basis.b0.raw = sourceQm31ToModel (1 : ExactQM31) at h
    simpa only [sourceQm31ToModel_one] using h
  have b1Exact : exactRaw outputs.basis.b1.raw = exactRaw alpha1 ^ 3 := by
    have h := mapEquation _ _ outputs.basis.b1Exact
    change exactRaw outputs.basis.b1.raw =
      sourceQm31ToModel (generatedQm31ToExact alpha1 ^ 3) at h
    simpa only [sourceMapPow, sourceMapGenerated] using h
  have b2Exact : exactRaw outputs.basis.b2.raw = exactRaw alpha1 ^ 2 := by
    have h := mapEquation _ _ outputs.basis.b2Exact
    change exactRaw outputs.basis.b2.raw =
      sourceQm31ToModel (generatedQm31ToExact alpha1 ^ 2) at h
    simpa only [sourceMapPow, sourceMapGenerated] using h
  have b3Exact : exactRaw outputs.basis.b3.raw = exactRaw alpha1 := by
    exact mapEquation _ _ outputs.basis.b3Exact
  have b4Exact : exactRaw outputs.basis.b4.raw = exactRaw alpha2 ^ 3 := by
    have h := mapEquation _ _ outputs.basis.b4Exact
    change exactRaw outputs.basis.b4.raw =
      sourceQm31ToModel (generatedQm31ToExact alpha2 ^ 3) at h
    simpa only [sourceMapPow, sourceMapGenerated] using h
  have b5Exact : exactRaw outputs.basis.b5.raw =
      exactRaw alpha2 ^ 3 * exactRaw alpha1 ^ 3 := by
    have h := mapEquation _ _ outputs.basis.b5Exact
    change exactRaw outputs.basis.b5.raw = sourceQm31ToModel
      (generatedQm31ToExact alpha2 ^ 3 * generatedQm31ToExact alpha1 ^ 3) at h
    simpa only [sourceQm31ToModel_mul, sourceMapPow,
      sourceMapGenerated] using h
  have b6Exact : exactRaw outputs.basis.b6.raw =
      exactRaw alpha2 ^ 3 * exactRaw alpha1 ^ 2 := by
    have h := mapEquation _ _ outputs.basis.b6Exact
    change exactRaw outputs.basis.b6.raw = sourceQm31ToModel
      (generatedQm31ToExact alpha2 ^ 3 * generatedQm31ToExact alpha1 ^ 2) at h
    simpa only [sourceQm31ToModel_mul, sourceMapPow,
      sourceMapGenerated] using h
  have b7Exact : exactRaw outputs.basis.b7.raw =
      exactRaw alpha2 ^ 3 * exactRaw alpha1 := by
    have h := mapEquation _ _ outputs.basis.b7Exact
    change exactRaw outputs.basis.b7.raw = sourceQm31ToModel
      (generatedQm31ToExact alpha2 ^ 3 * generatedQm31ToExact alpha1) at h
    simpa only [sourceQm31ToModel_mul, sourceMapPow,
      sourceMapGenerated] using h
  have b8Exact : exactRaw outputs.basis.b8.raw = exactRaw alpha2 ^ 2 := by
    have h := mapEquation _ _ outputs.basis.b8Exact
    change exactRaw outputs.basis.b8.raw =
      sourceQm31ToModel (generatedQm31ToExact alpha2 ^ 2) at h
    simpa only [sourceMapPow, sourceMapGenerated] using h
  have b9Exact : exactRaw outputs.basis.b9.raw =
      exactRaw alpha2 ^ 2 * exactRaw alpha1 ^ 3 := by
    have h := mapEquation _ _ outputs.basis.b9Exact
    change exactRaw outputs.basis.b9.raw = sourceQm31ToModel
      (generatedQm31ToExact alpha2 ^ 2 * generatedQm31ToExact alpha1 ^ 3) at h
    simpa only [sourceQm31ToModel_mul, sourceMapPow,
      sourceMapGenerated] using h
  have b10Exact : exactRaw outputs.basis.b10.raw =
      exactRaw alpha2 ^ 2 * exactRaw alpha1 ^ 2 := by
    have h := mapEquation _ _ outputs.basis.b10Exact
    change exactRaw outputs.basis.b10.raw = sourceQm31ToModel
      (generatedQm31ToExact alpha2 ^ 2 * generatedQm31ToExact alpha1 ^ 2) at h
    simpa only [sourceQm31ToModel_mul, sourceMapPow,
      sourceMapGenerated] using h
  have b11Exact : exactRaw outputs.basis.b11.raw =
      exactRaw alpha2 ^ 2 * exactRaw alpha1 := by
    have h := mapEquation _ _ outputs.basis.b11Exact
    change exactRaw outputs.basis.b11.raw = sourceQm31ToModel
      (generatedQm31ToExact alpha2 ^ 2 * generatedQm31ToExact alpha1) at h
    simpa only [sourceQm31ToModel_mul, sourceMapPow,
      sourceMapGenerated] using h
  have b12Exact : exactRaw outputs.basis.b12.raw = exactRaw alpha2 := by
    exact mapEquation _ _ outputs.basis.b12Exact
  have b13Exact : exactRaw outputs.basis.b13.raw =
      exactRaw alpha2 * exactRaw alpha1 ^ 3 := by
    have h := mapEquation _ _ outputs.basis.b13Exact
    change exactRaw outputs.basis.b13.raw = sourceQm31ToModel
      (generatedQm31ToExact alpha2 * generatedQm31ToExact alpha1 ^ 3) at h
    simpa only [sourceQm31ToModel_mul, sourceMapPow,
      sourceMapGenerated] using h
  have b14Exact : exactRaw outputs.basis.b14.raw =
      exactRaw alpha2 * exactRaw alpha1 ^ 2 := by
    have h := mapEquation _ _ outputs.basis.b14Exact
    change exactRaw outputs.basis.b14.raw = sourceQm31ToModel
      (generatedQm31ToExact alpha2 * generatedQm31ToExact alpha1 ^ 2) at h
    simpa only [sourceQm31ToModel_mul, sourceMapPow,
      sourceMapGenerated] using h
  have b15Exact : exactRaw outputs.basis.b15.raw =
      exactRaw alpha2 * exactRaw alpha1 := by
    have h := mapEquation _ _ outputs.basis.b15Exact
    change exactRaw outputs.basis.b15.raw = sourceQm31ToModel
      (generatedQm31ToExact alpha2 * generatedQm31ToExact alpha1) at h
    simpa only [sourceQm31ToModel_mul, sourceMapGenerated] using h
  have out0Exact := mapEquation _ _ outputs.out0Exact
  have out1Exact := mapEquation _ _ outputs.out1Exact
  have out2Exact := mapEquation _ _ outputs.out2Exact
  have out3Exact := mapEquation _ _ outputs.out3Exact
  simp only [sourceQm31ToModel_mul, sourceQm31ToModel_add,
    sourceMapSixteen, sourceMapGenerated, sourceMapExact] at out0Exact
  simp only [sourceQm31ToModel_mul, sourceQm31ToModel_add,
    sourceMapSixteen, sourceMapGenerated, sourceMapExact] at out1Exact
  simp only [sourceQm31ToModel_mul, sourceQm31ToModel_add,
    sourceMapSixteen, sourceMapGenerated, sourceMapExact] at out2Exact
  simp only [sourceQm31ToModel_mul, sourceQm31ToModel_add,
    sourceMapSixteen, sourceMapGenerated, sourceMapExact] at out3Exact
  funext index
  fin_cases index <;> apply mul_left_cancel₀ sixteen_ne_zero
  · change 16 * exactRaw outputs.out0.raw = _
    rw [out0Exact]
    simp [representedGroupedWeights, releasedRowGroups4, releasedRowGroups64,
      releasedFourValues, releasedSevenValues, releasedSevenValuesStaged,
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer,
      AspisV5FriRelationCandidateBridge.dualWeightFoldValue,
      AspisV5ComponentCConcreteFoldLinearity.childIndex,
      b0Exact, b1Exact, b2Exact, b3Exact, b4Exact, b5Exact, b6Exact,
      b7Exact, b8Exact, b9Exact, b10Exact, b11Exact, b12Exact, b13Exact,
      b14Exact, b15Exact,
      V7CallerCurrentReleaseR26GroupedMaskFormulas.four_ne_zero,
      inverseFourSquareTimesSixteen, mulInverseFourSquareTimesSixteen]
    field_simp [V7CallerCurrentReleaseR26GroupedMaskFormulas.four_ne_zero] <;>
      ring
  · change 16 * exactRaw outputs.out1.raw = _
    rw [out1Exact]
    simp [representedGroupedWeights, releasedRowGroups4, releasedRowGroups64,
      releasedFourValues, releasedSevenValues, releasedSevenValuesStaged,
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer,
      AspisV5FriRelationCandidateBridge.dualWeightFoldValue,
      AspisV5ComponentCConcreteFoldLinearity.childIndex,
      b0Exact, b1Exact, b2Exact, b3Exact, b4Exact, b5Exact, b6Exact,
      b7Exact, b8Exact, b9Exact, b10Exact, b11Exact, b12Exact, b13Exact,
      b14Exact, b15Exact,
      V7CallerCurrentReleaseR26GroupedMaskFormulas.four_ne_zero,
      inverseFourSquareTimesSixteen, mulInverseFourSquareTimesSixteen]
    field_simp [V7CallerCurrentReleaseR26GroupedMaskFormulas.four_ne_zero] <;>
      ring
  · change 16 * exactRaw outputs.out2.raw = _
    rw [out2Exact]
    simp [representedGroupedWeights, releasedRowGroups4, releasedRowGroups64,
      releasedFourValues, releasedSevenValues, releasedSevenValuesStaged,
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer,
      AspisV5FriRelationCandidateBridge.dualWeightFoldValue,
      AspisV5ComponentCConcreteFoldLinearity.childIndex,
      b0Exact, b1Exact, b2Exact, b3Exact, b4Exact, b5Exact, b6Exact,
      b7Exact, b8Exact, b9Exact, b10Exact, b11Exact, b12Exact, b13Exact,
      b14Exact, b15Exact,
      V7CallerCurrentReleaseR26GroupedMaskFormulas.four_ne_zero,
      inverseFourSquareTimesSixteen, mulInverseFourSquareTimesSixteen]
    field_simp [V7CallerCurrentReleaseR26GroupedMaskFormulas.four_ne_zero] <;>
      ring
  · change 16 * exactRaw outputs.out3.raw = _
    rw [out3Exact]
    simp [representedGroupedWeights, releasedRowGroups4, releasedRowGroups64,
      releasedFourValues, releasedSevenValues, releasedSevenValuesStaged,
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer,
      AspisV5FriRelationCandidateBridge.dualWeightFoldValue,
      AspisV5ComponentCConcreteFoldLinearity.childIndex,
      b0Exact, b1Exact, b2Exact, b3Exact, b4Exact, b5Exact, b6Exact,
      b7Exact, b8Exact, b9Exact, b10Exact, b11Exact, b12Exact, b13Exact,
      b14Exact, b15Exact,
      V7CallerCurrentReleaseR26GroupedMaskFormulas.four_ne_zero,
      inverseFourSquareTimesSixteen, mulInverseFourSquareTimesSixteen]
    field_simp [V7CallerCurrentReleaseR26GroupedMaskFormulas.four_ne_zero] <;>
      ring

/-- The actual optimized source helper implements the same two K1 fold layers
as the sequential specification, for the fixed released grouped table. -/
theorem released_grouped_rows_twice_corresponds
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31)
    (alpha1 alpha2 : RawQM31)
    (foldedGroups : alloc.vec.Vec Std.U8)
    (foldedValues : alloc.vec.Vec RawQM31)
    (valuesCanonical : CanonicalSeven value0 value1 value2 value3 value4 value5 value6)
    (alpha1Canonical : GeneratedCanonicalQM31 alpha1)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2)
    (run : sumcheck.fold_grouped_rows_twice
      (alloc.vec.Vec.deref releasedRowGroups64)
      (alloc.vec.Vec.deref
        (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))
      alpha1 alpha2 = ok (foldedGroups, foldedValues)) :
    ∃ out0 out1 out2 out3,
      foldedGroups = releasedRowGroups4 ∧
      foldedValues = releasedFourValues out0 out1 out2 out3 ∧
      CanonicalFour out0 out1 out2 out3 ∧
      representedGroupedWeights foldedGroups foldedValues =
        AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
          (exactRaw alpha2)
          (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
            (exactRaw alpha1)
            (representedGroupedWeights releasedRowGroups64
              (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))) := by
  obtain ⟨source⟩ := grouped_rows_twice_exposes_trace
    (alloc.vec.Vec.deref releasedRowGroups64)
    (alloc.vec.Vec.deref
      (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))
    alpha1 alpha2 foldedGroups foldedValues run
  obtain ⟨outputs⟩ := source_exposes_four_outputs value0 value1 value2 value3
    value4 value5 value6 alpha1 alpha2 foldedGroups foldedValues
    valuesCanonical alpha1Canonical alpha2Canonical source
  have valuesExact : foldedValues = releasedFourValues outputs.out0.raw
      outputs.out1.raw outputs.out2.raw outputs.out3.raw := by
    apply Subtype.ext
    simpa [releasedFourValues] using outputs.valuesExact
  refine ⟨outputs.out0.raw, outputs.out1.raw, outputs.out2.raw,
    outputs.out3.raw, source.groupsExact, valuesExact,
    ⟨outputs.out0.canonical, outputs.out1.canonical, outputs.out2.canonical,
      outputs.out3.canonical⟩, ?_⟩
  rw [source.groupsExact, valuesExact]
  exact four_outputs_have_k1_meaning value0 value1 value2 value3 value4
    value5 value6 alpha1 alpha2 foldedGroups foldedValues source outputs

#print axioms released_grouped_rows_twice_corresponds

end V7CallerCurrentReleaseR26GroupedRowsTwiceSemantics
