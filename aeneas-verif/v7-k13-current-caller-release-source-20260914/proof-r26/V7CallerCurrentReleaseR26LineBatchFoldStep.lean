import V7CallerCurrentReleaseR26Qm31M31SumProducts3Semantics

/-!
# One exact current line-batch fold step

This isolates the arithmetic performed for one line in the generated batch
loop.  Array traversal and mutation are handled separately.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26LineBatchFoldStep

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31M31SumProducts3Semantics

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawM31 := ⟨0#u32⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def embedM31 (value : RawM31) : ExactQM31 :=
  generatedM31ScalarToExactQM31 value

def exactEmbedM31 (value : ExactM31) : ExactQM31 := ⟨⟨value, 0⟩, 0⟩

@[simp] theorem embedM31_eq_exactEmbedM31 (value : RawM31) :
    embedM31 value = exactEmbedM31 (generatedM31ToExact value) := rfl

def doubledM31 (value : ExactM31) : ExactM31 := 2 * value ^ 2 - 1

def lineBatchFoldNumerator
    (alpha : ExactQM31) (x : ExactM31) : ExactQM31 :=
  1 + alpha ^ 3 * exactEmbedM31 x +
    alpha ^ 2 * exactEmbedM31 (doubledM31 x) +
    alpha * exactEmbedM31 (doubledM31 x * x)

private theorem oneCanonical : GeneratedCanonicalQM31 field.QM31.ONE := by
  simp only [GeneratedCanonicalQM31, GeneratedCanonicalCM31, field.QM31.ONE]
  repeat' constructor <;> norm_num

private theorem oneExact : generatedQm31ToExact field.QM31.ONE = 1 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      norm_num [generatedQm31ToExact, generatedCm31ToExact,
        field.QM31.ONE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply QuadraticAlgebra.ext <;>
      norm_num [generatedQm31ToExact, generatedCm31ToExact,
        field.QM31.ONE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- One successful active body edge has exactly the expected scale and line
coordinate update. -/
theorem active_line_batch_fold_step_exact
    (scales : Slice RawQM31) (xs : Slice RawM31) (index : Std.Usize)
    (scale : RawQM31) (x : RawM31)
    (alpha alpha2 alpha3 : RawQM31)
    (active : index < Slice.len scales)
    (xBound : index.val < xs.val.length)
    (hscale : GeneratedCanonicalQM31 scale)
    (hx : GeneratedCanonicalM31 x)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (scaleRead : Slice.index_usize scales index = ok scale)
    (xRead : Slice.index_usize xs index = ok x) :
    ∃ scalesOut xsOut scaleOut xOut,
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop.body
          alpha alpha2 alpha3 scales xs index =
        ok (cont (scalesOut, xsOut,
          Std.Usize.wrapping_add index 1#usize)) ∧
      GeneratedCanonicalM31 xOut ∧
      GeneratedCanonicalQM31 scaleOut ∧
      generatedM31ToExact xOut =
        doubledM31 (doubledM31 (generatedM31ToExact x)) ∧
      generatedQm31ToExact scaleOut =
        generatedQm31ToExact scale *
          lineBatchFoldNumerator (generatedQm31ToExact alpha)
            (generatedM31ToExact x) := by
  obtain ⟨high, highRun, highCanonical, highExact⟩ :=
    generated_double_x_m31_corresponds x hx
  obtain ⟨cross, crossRun, crossCanonical, crossExact⟩ :=
    generated_m31_mul_corresponds high x highCanonical hx
  let left : Array RawQM31 3#usize :=
    Array.make 3#usize [alpha3, alpha2, alpha]
  let right : Array RawM31 3#usize :=
    Array.make 3#usize [x, high, cross]
  have leftCanonical : CanonicalQM31Array3 left := by
    intro position bound
    have cases : position = 0 ∨ position = 1 ∨ position = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · exact halpha3
    · exact halpha2
    · exact halpha
  have rightCanonical : CanonicalM31Array3 right := by
    intro position bound
    have cases : position = 0 ∨ position = 1 ∨ position = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · exact hx
    · exact highCanonical
    · exact crossCanonical
  obtain ⟨mixed, mixedRun, mixedCanonical, mixedExact⟩ :=
    generated_qm31_m31_sum_products3_corresponds left right
      leftCanonical rightCanonical
  obtain ⟨numerator, numeratorRun, numeratorCanonical, numeratorExact⟩ :=
    generated_qm31_add_corresponds field.QM31.ONE mixed oneCanonical
      mixedCanonical
  obtain ⟨expectedScale, expectedScaleRun, expectedScaleCanonical,
      expectedScaleExact⟩ :=
    generated_qm31_mul_corresponds scale numerator hscale numeratorCanonical
  obtain ⟨expectedX, expectedXRun, expectedXCanonical, expectedXExact⟩ :=
    generated_double_x_m31_corresponds high highCanonical
  have scaleBound : index.val < scales.val.length := by
    simpa [Slice.len_val] using active
  obtain ⟨scalesOut, scaleUpdate, _scalesOutExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Slice.update_spec scales index expectedScale scaleBound)
  obtain ⟨xsOut, xUpdate, _xsOutExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Slice.update_spec xs index expectedX xBound)
  refine ⟨scalesOut, xsOut, expectedScale, expectedX, ?_,
    expectedXCanonical, expectedScaleCanonical, ?_, ?_⟩
  · unfold
      sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4_loop.body
    rw [if_pos active, xRead]
    simp only [bind_tc_ok]
    rw [highRun]
    simp only [bind_tc_ok]
    rw [crossRun]
    simp only [bind_tc_ok]
    change (do
      let mixed1 ← field.qm31_m31_sum_products3 left right
      let q ← Slice.index_usize scales index
      let q1 ← field.QM31.add field.QM31.ONE mixed1
      let q2 ← field.QM31.mul q q1
      let s ← Slice.update scales index q2
      let m ← sumcheck.WeightAccumulator.impl.double_x_m31 high
      let s1 ← Slice.update xs index m
      ok (cont (s, s1, Std.Usize.wrapping_add index 1#usize))) = _
    rw [mixedRun]
    simp only [bind_tc_ok]
    rw [scaleRead]
    simp only [bind_tc_ok]
    rw [numeratorRun]
    simp only [bind_tc_ok]
    rw [expectedScaleRun]
    simp only [bind_tc_ok]
    rw [scaleUpdate]
    simp only [bind_tc_ok]
    rw [expectedXRun]
    simp only [bind_tc_ok]
    rw [xUpdate]
    rfl
  · rw [expectedXExact, highExact]
    rfl
  · rw [expectedScaleExact, numeratorExact, oneExact, mixedExact]
    have mixedFormula : exactQm31M31Dot3 left right =
        generatedQm31ToExact alpha3 * embedM31 x +
          generatedQm31ToExact alpha2 * embedM31 high +
          generatedQm31ToExact alpha * embedM31 cross := by
      have leftVal : left.val = [alpha3, alpha2, alpha] := by rfl
      have rightVal : right.val = [x, high, cross] := by rfl
      simp [exactQm31M31Dot3, leftVal, rightVal, embedM31,
        Finset.sum_range_succ]
    have crossExact' : generatedM31ToExact cross =
        generatedM31ToExact high * generatedM31ToExact x := by
      simpa [generatedM31ToExact] using crossExact
    rw [mixedFormula, halpha2Exact, halpha3Exact,
      embedM31_eq_exactEmbedM31, embedM31_eq_exactEmbedM31,
      embedM31_eq_exactEmbedM31, highExact, crossExact', highExact]
    unfold lineBatchFoldNumerator doubledM31
    ring_nf

#print axioms active_line_batch_fold_step_exact

end V7CallerCurrentReleaseR26LineBatchFoldStep
