import V7ProductionCallbacksR30FieldCanonical
import V7CallerCurrentReleaseR26HalfBridge

/-!
# Canonicality of the production callback's secure-field primitives

The callback carries the same concrete field representation as the R26 model,
but its generated checked-arithmetic code is separate.  This module composes
the audited callback base and complex operations for the QM31 operations used
by the query callback.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26FieldBridge

namespace V7ProductionCallbacksR30Qm31Canonical

open V7ProductionCallbacksR30FieldCanonical

abbrev CallbackM31 := V7ProductionCallbacksR29.aspis_core.field.M31
abbrev CallbackCM31 := V7ProductionCallbacksR29.aspis_core.field.CM31
abbrev CallbackQM31 := V7ProductionCallbacksR29.aspis_core.field.QM31
abbrev CallbackPreparedQM31 :=
  V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier

theorem callback_cm31_add_canonical
    (left right : CallbackCM31)
    (hleft : GeneratedCanonicalCM31 left)
    (hright : GeneratedCanonicalCM31 right) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.CM31.add left right = ok output ∧
      GeneratedCanonicalCM31 output := by
  obtain ⟨real, hreal, hrealCanonical⟩ :=
    callback_m31_add_canonical left.a right.a hleft.1 hright.1
  obtain ⟨imag, himag, himagCanonical⟩ :=
    callback_m31_add_canonical left.b right.b hleft.2 hright.2
  let output : CallbackCM31 := ⟨real, imag⟩
  refine ⟨output, ?_, ⟨hrealCanonical, himagCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.CM31.add,
    hreal, himag, output]

theorem callback_cm31_sub_canonical
    (left right : CallbackCM31)
    (hleft : GeneratedCanonicalCM31 left)
    (hright : GeneratedCanonicalCM31 right) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.CM31.sub left right = ok output ∧
      GeneratedCanonicalCM31 output := by
  obtain ⟨real, hreal, hrealCanonical⟩ :=
    callback_m31_sub_canonical left.a right.a hleft.1 hright.1
  obtain ⟨imag, himag, himagCanonical⟩ :=
    callback_m31_sub_canonical left.b right.b hleft.2 hright.2
  let output : CallbackCM31 := ⟨real, imag⟩
  refine ⟨output, ?_, ⟨hrealCanonical, himagCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.CM31.sub,
    hreal, himag, output]

theorem callback_mul_by_r_canonical
    (value : CallbackCM31)
    (canonical : GeneratedCanonicalCM31 value) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.mul_by_r value = ok output ∧
      GeneratedCanonicalCM31 output := by
  obtain ⟨twiceReal, htwiceReal, twiceRealCanonical⟩ :=
    callback_m31_double_canonical value.a canonical.1
  obtain ⟨real, hreal, realCanonical⟩ :=
    callback_m31_sub_canonical twiceReal value.b twiceRealCanonical canonical.2
  obtain ⟨twiceImag, htwiceImag, twiceImagCanonical⟩ :=
    callback_m31_double_canonical value.b canonical.2
  obtain ⟨imag, himag, imagCanonical⟩ :=
    callback_m31_add_canonical value.a twiceImag canonical.1 twiceImagCanonical
  let output : CallbackCM31 := ⟨real, imag⟩
  refine ⟨output, ?_, ⟨realCanonical, imagCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.mul_by_r,
    htwiceReal, hreal, htwiceImag, himag, output]

theorem callback_cm31_square_canonical
    (value : CallbackCM31)
    (canonical : GeneratedCanonicalCM31 value) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.CM31.square value = ok output ∧
      GeneratedCanonicalCM31 output := by
  let wideA : Std.U64 := UScalar.cast .U64 value.a
  let wideB : Std.U64 := UScalar.cast .U64 value.b
  let wideP : Std.U64 := UScalar.cast .U64 V7CallerCurrentReleaseR26.field.P
  let wideSum : Std.U64 := Std.U64.wrapping_add wideA wideB
  let wideDiff : Std.U64 := Std.U64.wrapping_sub
    (Std.U64.wrapping_add wideA wideP) wideB
  let wideProduct : Std.U64 := Std.U64.wrapping_mul wideSum wideDiff
  have hWideA : wideA.val = value.a.val := by
    simp [wideA, Std.U32.cast_U64_val_eq]
  have hWideB : wideB.val = value.b.val := by
    simp [wideB, Std.U32.cast_U64_val_eq]
  have hWideP : wideP.val = 2147483647 := by
    simp [wideP, Std.U32.cast_U64_val_eq,
      V7CallerCurrentReleaseR26.field.P]
  have hSumBound : value.a.val + value.b.val < 2 ^ 64 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at canonical
    norm_num at canonical ⊢
    omega
  have hSumBound64 : value.a.val + value.b.val < 18446744073709551616 := by
    norm_num at hSumBound ⊢
    exact hSumBound
  have hWideSum : wideSum.val = value.a.val + value.b.val := by
    simp only [wideSum, Std.U64.wrapping_add_val_eq,
      UScalar.size_UScalarTyU64, u64_size_eq, hWideA, hWideB,
      Nat.mod_eq_of_lt hSumBound64]
  have hAddPBound : value.a.val + 2147483647 < 2 ^ 64 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at canonical
    norm_num at canonical ⊢
    omega
  have hAddPBound64 :
      value.a.val + 2147483647 < 18446744073709551616 := by
    norm_num at hAddPBound ⊢
    exact hAddPBound
  have hAddP : (Std.U64.wrapping_add wideA wideP).val =
      value.a.val + 2147483647 := by
    rw [Std.U64.wrapping_add_val_eq,
      UScalar.size_UScalarTyU64, u64_size_eq, hWideA, hWideP,
      Nat.mod_eq_of_lt hAddPBound64]
  have hbLe : value.b.val ≤ value.a.val + 2147483647 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at canonical
    norm_num at canonical ⊢
    omega
  have hDiffBound : value.a.val + 2147483647 - value.b.val < 2 ^ 64 := by
    omega
  have hWideDiff : wideDiff.val = value.a.val + 2147483647 - value.b.val := by
    simp only [wideDiff, Std.U64.wrapping_sub_val_eq,
      UScalar.size_UScalarTyU64, u64_size_eq, hAddP, hWideB]
    have hrewrite :
        value.a.val + 2147483647 + (2 ^ 64 - value.b.val) =
          (value.a.val + 2147483647 - value.b.val) + 2 ^ 64 := by
      have hb64 : value.b.val ≤ 2 ^ 64 := by
        unfold GeneratedCanonicalCM31
          AspisAeneasCM31Multiplicative.CanonicalRawM31 at canonical
        norm_num at canonical ⊢
        omega
      omega
    change (value.a.val + 2147483647 + (2 ^ 64 - value.b.val)) % (2 ^ 64) = _
    rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hDiffBound]
  have hSum32 : value.a.val + value.b.val < 2 ^ 32 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at canonical
    norm_num at canonical ⊢
    omega
  have hDiff32 : value.a.val + 2147483647 - value.b.val < 2 ^ 32 := by
    unfold GeneratedCanonicalCM31
      AspisAeneasCM31Multiplicative.CanonicalRawM31 at canonical
    norm_num at canonical ⊢
    omega
  have hProductBound :
      (value.a.val + value.b.val) *
        (value.a.val + 2147483647 - value.b.val) < 2 ^ 64 := by
    by_cases hz : value.a.val + 2147483647 - value.b.val = 0
    · simp [hz]
    · have h1 := Nat.mul_lt_mul_of_pos_right hSum32 (Nat.pos_of_ne_zero hz)
      have h2 := Nat.mul_lt_mul_of_pos_left hDiff32 (by norm_num : 0 < 2 ^ 32)
      norm_num at h1 h2 ⊢
      exact lt_trans h1 h2
  have hProductRun : wideSum * wideDiff = ok wideProduct := by
    rw [checked_mul_eq_wrapping]
    · rw [generic_wrapping_mul_eq_u64_wrapping_mul]
    · rw [UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
      rw [hWideSum, hWideDiff]
      norm_num at hProductBound ⊢
      omega
  have hSumRun : wideA + wideB = ok wideSum := by
    rw [checked_add_eq_wrapping]
    · rw [generic_wrapping_add_eq_u64_wrapping_add]
    · rw [UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
      rw [hWideA, hWideB]
      norm_num at hSumBound ⊢
      omega
  have hAddPRun : wideA + wideP =
      ok (Std.U64.wrapping_add wideA wideP) := by
    rw [checked_add_eq_wrapping]
    · rw [generic_wrapping_add_eq_u64_wrapping_add]
    · rw [UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
      rw [hWideA, hWideP]
      norm_num at hAddPBound ⊢
      omega
  have hDiffRun : (Std.U64.wrapping_add wideA wideP) - wideB = ok wideDiff := by
    rw [checked_sub_eq_wrapping]
    · rw [generic_wrapping_sub_eq_u64_wrapping_sub]
    · rw [hAddP, hWideB]
      exact hbLe
  obtain ⟨real, hrealCurrent, realCanonical, _⟩ :=
    generated_m31_reduce_u64_corresponds wideProduct
  have hWideProductBound : wideProduct.val ≤ 18446744073709551615 := by
    have hlt := wideProduct.hBounds
    norm_num [Std.U64.numBits] at hlt
    omega
  have hreal :
      V7ProductionCallbacksR29.aspis_core.field.M31.reduce_u64 wideProduct =
        ok real := by
    calc
      V7ProductionCallbacksR29.aspis_core.field.M31.reduce_u64 wideProduct =
          V7CallerCurrentReleaseR26.field.M31.reduce_u64 wideProduct := by
        unfold V7ProductionCallbacksR29.aspis_core.field.M31.reduce_u64
          V7CallerCurrentReleaseR26.field.M31.reduce_u64
        rw [callback_reduce_u64_eq_current_reduce_u64_wide wideProduct
          hWideProductBound]
      _ = ok real := hrealCurrent
  obtain ⟨product, hproduct, productCanonical⟩ :=
    callback_m31_mul_canonical value.a value.b canonical.1 canonical.2
  obtain ⟨imaginary, himaginary, imaginaryCanonical⟩ :=
    callback_m31_double_canonical product productCanonical
  let output : CallbackCM31 := ⟨real, imaginary⟩
  refine ⟨output, ?_, ⟨realCanonical, imaginaryCanonical⟩⟩
  unfold V7ProductionCallbacksR29.aspis_core.field.CM31.square
  simp only [Std.lift, bind_tc_ok]
  simp only [from_u64_u32_eq_cast]
  rw [show (UScalar.cast .U64 value.a : Std.U64) = wideA by rfl]
  rw [show (UScalar.cast .U64 value.b : Std.U64) = wideB by rfl]
  rw [hSumRun]
  simp only [bind_tc_ok]
  rw [p_eq]
  rw [show (UScalar.cast .U64 V7CallerCurrentReleaseR26.field.P : Std.U64) = wideP by rfl]
  rw [hAddPRun]
  simp only [bind_tc_ok]
  rw [hDiffRun]
  simp only [bind_tc_ok]
  rw [hProductRun]
  simp only [bind_tc_ok, hreal, hproduct, himaginary]
  rfl

theorem callback_cm31_double_canonical
    (value : CallbackCM31)
    (canonical : GeneratedCanonicalCM31 value) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.CM31.double value = ok output ∧
      GeneratedCanonicalCM31 output := by
  obtain ⟨output, houtput, outputCanonical⟩ :=
    callback_cm31_add_canonical value value canonical canonical
  refine ⟨output, ?_, outputCanonical⟩
  unfold V7ProductionCallbacksR29.aspis_core.field.CM31.double
  exact houtput

theorem callback_cm31_mul_m31_canonical
    (value : CallbackCM31) (scalar : CallbackM31)
    (valueCanonical : GeneratedCanonicalCM31 value)
    (scalarCanonical : GeneratedCanonicalM31 scalar) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.CM31.mul_m31 value scalar =
        ok output ∧
      GeneratedCanonicalCM31 output := by
  obtain ⟨real, hreal, realCanonical⟩ :=
    callback_m31_mul_canonical value.a scalar valueCanonical.1 scalarCanonical
  obtain ⟨imaginary, himaginary, imaginaryCanonical⟩ :=
    callback_m31_mul_canonical value.b scalar valueCanonical.2 scalarCanonical
  let output : CallbackCM31 := ⟨real, imaginary⟩
  refine ⟨output, ?_, ⟨realCanonical, imaginaryCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.CM31.mul_m31,
    hreal, himaginary, output]

theorem callback_qm31_mul_m31_canonical
    (value : CallbackQM31) (scalar : CallbackM31)
    (valueCanonical : GeneratedCanonicalQM31 value)
    (scalarCanonical : GeneratedCanonicalM31 scalar) :
    ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.QM31.mul_m31 value scalar =
        ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨low, hlow, lowCanonical⟩ :=
    callback_cm31_mul_m31_canonical value.c0 scalar valueCanonical.1 scalarCanonical
  obtain ⟨high, hhigh, highCanonical⟩ :=
    callback_cm31_mul_m31_canonical value.c1 scalar valueCanonical.2 scalarCanonical
  let output : CallbackQM31 := ⟨low, high⟩
  refine ⟨output, ?_, ⟨lowCanonical, highCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.QM31.mul_m31,
    hlow, hhigh, output]

theorem callback_prepared_cm31_mul_canonical
    (left right : CallbackCM31) (leftSum : CallbackM31)
    (leftCanonical : GeneratedCanonicalCM31 left)
    (rightCanonical : GeneratedCanonicalCM31 right)
    (leftSumCanonical : GeneratedCanonicalM31 leftSum) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
          () (Array.make 3#usize [left.a, left.b, leftSum], right) = ok output ∧
      GeneratedCanonicalCM31 output := by
  obtain ⟨m0, hm0, m0Canonical⟩ :=
    callback_m31_mul_canonical left.a right.a leftCanonical.1 rightCanonical.1
  obtain ⟨m1, hm1, m1Canonical⟩ :=
    callback_m31_mul_canonical left.b right.b leftCanonical.2 rightCanonical.2
  obtain ⟨rightSum, hrightSum, rightSumCanonical⟩ :=
    callback_m31_add_canonical right.a right.b rightCanonical.1 rightCanonical.2
  obtain ⟨m2, hm2, m2Canonical⟩ :=
    callback_m31_mul_canonical leftSum rightSum leftSumCanonical rightSumCanonical
  obtain ⟨real, hreal, realCanonical⟩ :=
    callback_m31_sub_canonical m0 m1 m0Canonical m1Canonical
  obtain ⟨cross, hcross, crossCanonical⟩ :=
    callback_m31_sub_canonical m2 m0 m2Canonical m0Canonical
  obtain ⟨imaginary, himaginary, imaginaryCanonical⟩ :=
    callback_m31_sub_canonical cross m1 crossCanonical m1Canonical
  have hindex0 :
      Array.index_usize (Array.make 3#usize [left.a, left.b, leftSum])
        0#usize = ok left.a := by
    rfl
  have hindex1 :
      Array.index_usize (Array.make 3#usize [left.a, left.b, leftSum])
        1#usize = ok left.b := by
    rfl
  have hindex2 :
      Array.index_usize (Array.make 3#usize [left.a, left.b, leftSum])
        2#usize = ok leftSum := by
    rfl
  let output : CallbackCM31 := ⟨real, imaginary⟩
  refine ⟨output, ?_, ⟨realCanonical, imaginaryCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
    hindex0, hm0, hindex1, hm1, hindex2, hrightSum, hm2, hreal, hcross,
    himaginary, output]

theorem callback_prepared_qm31_mul_canonical
    (left right : CallbackQM31)
    (leftCanonical : GeneratedCanonicalQM31 left)
    (rightCanonical : GeneratedCanonicalQM31 right) :
    ∃ prepared : CallbackPreparedQM31, ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.new left =
        ok prepared ∧
      V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.mul
          prepared right = ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨leftSum, hleftSum, leftSumCanonical⟩ :=
    callback_cm31_add_canonical left.c0 left.c1 leftCanonical.1 leftCanonical.2
  obtain ⟨left0Sum, hleft0Sum, left0SumCanonical⟩ :=
    callback_m31_add_canonical left.c0.a left.c0.b leftCanonical.1.1 leftCanonical.1.2
  obtain ⟨left1Sum, hleft1Sum, left1SumCanonical⟩ :=
    callback_m31_add_canonical left.c1.a left.c1.b leftCanonical.2.1 leftCanonical.2.2
  obtain ⟨leftSumSum, hleftSumSum, leftSumSumCanonical⟩ :=
    callback_m31_add_canonical leftSum.a leftSum.b leftSumCanonical.1 leftSumCanonical.2
  let left0Components : Array CallbackM31 3#usize :=
    Array.make 3#usize [left.c0.a, left.c0.b, left0Sum]
  let left1Components : Array CallbackM31 3#usize :=
    Array.make 3#usize [left.c1.a, left.c1.b, left1Sum]
  let leftSumComponents : Array CallbackM31 3#usize :=
    Array.make 3#usize [leftSum.a, leftSum.b, leftSumSum]
  let prepared : CallbackPreparedQM31 :=
    { components := Array.make 3#usize [left0Components, left1Components,
      leftSumComponents] }
  have hnew :
      V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.new left =
        ok prepared := by
    simp [V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.new,
      V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
      hleft0Sum, hleft1Sum, hleftSum, hleftSumSum, left0Components,
      left1Components, leftSumComponents, prepared]
  obtain ⟨m0, hm0, m0Canonical⟩ :=
    callback_prepared_cm31_mul_canonical left.c0 right.c0 left0Sum
      leftCanonical.1 rightCanonical.1 left0SumCanonical
  obtain ⟨m1, hm1, m1Canonical⟩ :=
    callback_prepared_cm31_mul_canonical left.c1 right.c1 left1Sum
      leftCanonical.2 rightCanonical.2 left1SumCanonical
  obtain ⟨rightSum, hrightSum, rightSumCanonical⟩ :=
    callback_cm31_add_canonical right.c0 right.c1 rightCanonical.1 rightCanonical.2
  obtain ⟨m2, hm2, m2Canonical⟩ :=
    callback_prepared_cm31_mul_canonical leftSum rightSum leftSumSum
      leftSumCanonical rightSumCanonical leftSumSumCanonical
  obtain ⟨rM1, hrM1, rM1Canonical⟩ :=
    callback_mul_by_r_canonical m1 m1Canonical
  obtain ⟨low, hlow, lowCanonical⟩ :=
    callback_cm31_add_canonical m0 rM1 m0Canonical rM1Canonical
  obtain ⟨cross, hcross, crossCanonical⟩ :=
    callback_cm31_sub_canonical m2 m0 m2Canonical m0Canonical
  obtain ⟨high, hhigh, highCanonical⟩ :=
    callback_cm31_sub_canonical cross m1 crossCanonical m1Canonical
  have hindex0 : Array.index_usize prepared.components 0#usize = ok left0Components := by
    rfl
  have hindex1 : Array.index_usize prepared.components 1#usize = ok left1Components := by
    rfl
  have hindex2 : Array.index_usize prepared.components 2#usize = ok leftSumComponents := by
    rfl
  have hcomponent0 :
      V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (left0Components, right.c0) = ok m0 := by
    simpa [left0Components] using hm0
  have hcomponent1 :
      V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (left1Components, right.c1) = ok m1 := by
    simpa [left1Components] using hm1
  have hcomponent2 :
      V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (leftSumComponents, rightSum) = ok m2 := by
    simpa [leftSumComponents] using hm2
  let output : CallbackQM31 := ⟨low, high⟩
  refine ⟨prepared, output, hnew, ?_, ⟨lowCanonical, highCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.PreparedQm31Multiplier.mul,
    hindex0, hcomponent0, hindex1, hcomponent1, hindex2, hrightSum,
    hcomponent2, hrM1, hlow, hcross, hhigh, prepared, output]

theorem callback_m31_half_eq_current_half (value : CallbackM31) :
    V7ProductionCallbacksR29.aspis_core.field.M31.half value =
      V7CallerCurrentReleaseR26.field.M31.half value := rfl

theorem callback_qm31_half_canonical
    (value : CallbackQM31) (canonical : GeneratedCanonicalQM31 value) :
    ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.QM31.half value = ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨output, currentRun, outputCanonical, _⟩ :=
    V7CallerCurrentReleaseR26HalfBridge.generated_qm31_half_corresponds value canonical
  refine ⟨output, ?_, outputCanonical⟩
  simp only [V7ProductionCallbacksR29.aspis_core.field.QM31.half,
    V7ProductionCallbacksR29.aspis_core.field.CM31.half,
    callback_m31_half_eq_current_half]
  exact currentRun

theorem callback_qm31_add_canonical
    (left right : CallbackQM31)
    (hleft : GeneratedCanonicalQM31 left)
    (hright : GeneratedCanonicalQM31 right) :
    ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.QM31.add left right = ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨low, hlow, lowCanonical⟩ :=
    callback_cm31_add_canonical left.c0 right.c0 hleft.1 hright.1
  obtain ⟨high, hhigh, highCanonical⟩ :=
    callback_cm31_add_canonical left.c1 right.c1 hleft.2 hright.2
  let output : CallbackQM31 := ⟨low, high⟩
  refine ⟨output, ?_, ⟨lowCanonical, highCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.QM31.add,
    hlow, hhigh, output]

theorem callback_qm31_sub_canonical
    (left right : CallbackQM31)
    (hleft : GeneratedCanonicalQM31 left)
    (hright : GeneratedCanonicalQM31 right) :
    ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.QM31.sub left right = ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨low, hlow, lowCanonical⟩ :=
    callback_cm31_sub_canonical left.c0 right.c0 hleft.1 hright.1
  obtain ⟨high, hhigh, highCanonical⟩ :=
    callback_cm31_sub_canonical left.c1 right.c1 hleft.2 hright.2
  let output : CallbackQM31 := ⟨low, high⟩
  refine ⟨output, ?_, ⟨lowCanonical, highCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.QM31.sub,
    hlow, hhigh, output]

theorem callback_qm31_mul_canonical
    (left right : CallbackQM31)
    (hleft : GeneratedCanonicalQM31 left)
    (hright : GeneratedCanonicalQM31 right) :
    ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.QM31.mul left right = ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨m0, hm0, m0Canonical⟩ :=
    callback_cm31_mul_canonical left.c0 right.c0 hleft.1 hright.1
  obtain ⟨m1, hm1, m1Canonical⟩ :=
    callback_cm31_mul_canonical left.c1 right.c1 hleft.2 hright.2
  obtain ⟨leftSum, hleftSum, leftSumCanonical⟩ :=
    callback_cm31_add_canonical left.c0 left.c1 hleft.1 hleft.2
  obtain ⟨rightSum, hrightSum, rightSumCanonical⟩ :=
    callback_cm31_add_canonical right.c0 right.c1 hright.1 hright.2
  obtain ⟨m2, hm2, m2Canonical⟩ :=
    callback_cm31_mul_canonical leftSum rightSum leftSumCanonical rightSumCanonical
  obtain ⟨rM1, hrM1, rM1Canonical⟩ :=
    callback_mul_by_r_canonical m1 m1Canonical
  obtain ⟨low, hlow, lowCanonical⟩ :=
    callback_cm31_add_canonical m0 rM1 m0Canonical rM1Canonical
  obtain ⟨imagPart, himagPart, imagPartCanonical⟩ :=
    callback_cm31_sub_canonical m2 m0 m2Canonical m0Canonical
  obtain ⟨high, hhigh, highCanonical⟩ :=
    callback_cm31_sub_canonical imagPart m1 imagPartCanonical m1Canonical
  let output : CallbackQM31 := ⟨low, high⟩
  refine ⟨output, ?_, ⟨lowCanonical, highCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.QM31.mul,
    hm0, hm1, hleftSum, hrightSum, hm2, hrM1, hlow, himagPart,
    hhigh, output]

theorem callback_qm31_square_canonical
    (value : CallbackQM31)
    (canonical : GeneratedCanonicalQM31 value) :
    ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.QM31.square value = ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨lowSquare, hlowSquare, lowSquareCanonical⟩ :=
    callback_cm31_square_canonical value.c0 canonical.1
  obtain ⟨highSquare, hhighSquare, highSquareCanonical⟩ :=
    callback_cm31_square_canonical value.c1 canonical.2
  obtain ⟨rHighSquare, hrHighSquare, rHighSquareCanonical⟩ :=
    callback_mul_by_r_canonical highSquare highSquareCanonical
  obtain ⟨low, hlow, lowCanonical⟩ :=
    callback_cm31_add_canonical lowSquare rHighSquare
      lowSquareCanonical rHighSquareCanonical
  obtain ⟨cross, hcross, crossCanonical⟩ :=
    callback_cm31_mul_canonical value.c0 value.c1 canonical.1 canonical.2
  obtain ⟨high, hhigh, highCanonical⟩ :=
    callback_cm31_double_canonical cross crossCanonical
  let output : CallbackQM31 := ⟨low, high⟩
  refine ⟨output, ?_, ⟨lowCanonical, highCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.QM31.square,
    hlowSquare, hhighSquare, hrHighSquare, hlow, hcross, hhigh, output]

#print axioms callback_cm31_add_canonical
#print axioms callback_cm31_sub_canonical
#print axioms callback_mul_by_r_canonical
#print axioms callback_cm31_square_canonical
#print axioms callback_cm31_double_canonical
#print axioms callback_cm31_mul_m31_canonical
#print axioms callback_qm31_mul_m31_canonical
#print axioms callback_prepared_cm31_mul_canonical
#print axioms callback_prepared_qm31_mul_canonical
#print axioms callback_qm31_half_canonical
#print axioms callback_qm31_add_canonical
#print axioms callback_qm31_sub_canonical
#print axioms callback_qm31_mul_canonical
#print axioms callback_qm31_square_canonical

end V7ProductionCallbacksR30Qm31Canonical
