import Aeneas.Std.RangeIter
import S3VariantRowAeneasCut
import S3VariantRowLoopSteps
import S3VariantRowBodyProbe
import Mathlib.Data.Nat.Bitwise

open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1.S3VariantRowAeneasCut

private theorem tau_lookup_bounded_value (d : Std.Usize) (hd : d.val < 5) :
    ∃ t, Array.index_usize tau d = .ok t ∧ t.val ≤ 4 := by
  have hzero : (0#usize).val = 0 := by scalar_tac
  have hone : (1#usize).val = 1 := by scalar_tac
  have htwo : (2#usize).val = 2 := by scalar_tac
  have hthree : (3#usize).val = 3 := by scalar_tac
  have hfour : (4#usize).val = 4 := by scalar_tac
  by_cases h0 : d.val = 0
  · have hdEq : d = 0#usize := UScalar.eq_of_val_eq (by rw [h0, hzero])
    subst d
    exact ⟨3#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩
  · by_cases h1 : d.val = 1
    · have hdEq : d = 1#usize := UScalar.eq_of_val_eq (by rw [h1, hone])
      subst d
      exact ⟨4#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩
    · by_cases h2 : d.val = 2
      · have hdEq : d = 2#usize := UScalar.eq_of_val_eq (by rw [h2, htwo])
        subst d
        exact ⟨2#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩
      · by_cases h3 : d.val = 3
        · have hdEq : d = 3#usize := UScalar.eq_of_val_eq (by rw [h3, hthree])
          subst d
          exact ⟨0#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩
        · have h4 : d.val = 4 := by omega
          have hdEq : d = 4#usize := UScalar.eq_of_val_eq (by rw [h4, hfour])
          subst d
          exact ⟨1#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩

theorem row_loop_continue_value (j d : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (hd : d.val < 5) :
    ∃ t result,
      Array.index_usize tau d = .ok t ∧
      row_loop_continue j d iter out = .ok (.cont (iter, result)) ∧
      result.val = out.val ||| (((j.val >>> (2 * d.val)) &&& 3) * 2 ^ (2 * t.val)) := by
  obtain ⟨t, hindex, ht⟩ := tau_lookup_bounded_value d hd
  have htwo : (2#usize).val = 2 := by scalar_tac
  have hthree : (3#usize).val = 3 := by scalar_tac
  have hmul1max : (2#usize).val * d.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  obtain ⟨i, hmul1, hi⟩ := WP.spec_imp_exists (UScalar.mul_spec hmul1max)
  have hiVal : i.val = 2 * d.val := by rw [htwo] at hi; exact hi
  have hbits8 : 8 < System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  have hiBits : i.val < UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq, hiVal]
    have hd8 : 2 * d.val ≤ 8 := by omega
    omega
  obtain ⟨i1, hshift, hshiftSpec⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec j i hiBits)
  have hi1Val : i1.val = j.val >>> i.val := hshiftSpec.1
  have hmaskVal : (i1 &&& 3#usize).val = i1.val &&& 3 := by
    rw [UScalar.val_and, hthree]
  have hmul2max : (2#usize).val * t.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  obtain ⟨i4, hmul2, hi4⟩ := WP.spec_imp_exists (UScalar.mul_spec hmul2max)
  have hi4Val : i4.val = 2 * t.val := by rw [htwo] at hi4; exact hi4
  have hi4Bits : i4.val < UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq, hi4Val]
    have ht8 : 2 * t.val ≤ 8 := by omega
    omega
  have hpow : 2 ^ i4.val ≤ 2 ^ 8 := by
    apply Nat.pow_le_pow_right (by decide)
    rw [hi4Val]
    omega
  have hmaskBound : (i1 &&& 3#usize).val ≤ 3 := by
    rw [hmaskVal]
    exact Nat.and_le_right
  have htermBound : (i1 &&& 3#usize).val * 2 ^ i4.val ≤ 3 * 2 ^ 8 :=
    Nat.mul_le_mul hmaskBound hpow
  have htermSmall : 3 * 2 ^ 8 < 2 ^ UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
  obtain ⟨i5, hleft, hleftSpec⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_spec (i1 &&& 3#usize) i4 (UScalar.size UScalarTy.Usize)
      hi4Bits rfl)
  have hi5Val : i5.val = (i1 &&& 3#usize).val * 2 ^ i4.val := by
    have hvalue := hleftSpec.1
    rw [Nat.shiftLeft_eq] at hvalue
    change i5.val = ((i1 &&& 3#usize).val * 2 ^ i4.val) %
      UScalar.size UScalarTy.Usize at hvalue
    have htermSmall' : (i1 &&& 3#usize).val * 2 ^ i4.val <
        UScalar.size UScalarTy.Usize := by
      have h := lt_of_le_of_lt htermBound htermSmall
      rw [UScalar.size, UScalarTy.Usize_numBits_eq]
      exact h
    rw [Nat.mod_eq_of_lt htermSmall'] at hvalue
    exact hvalue
  let result := out ||| i5
  have hrun := continue_step_of_results j d iter out i i1 t i4 i5
    hmul1 hshift hindex hmul2 hleft
  have hrun : row_loop_continue j d iter out = .ok (.cont (iter, result)) := by
    simpa only [result] using hrun
  refine ⟨t, result, hindex, hrun, ?_⟩
  have hvalue : result.val = out.val ||| i5.val := by
    simp [result, UScalar.val_or]
  rw [hvalue, hi5Val, hmaskVal, hi1Val, hiVal, hi4Val]

end AspisR1.S3VariantRowAeneasCut
#print axioms AspisR1.S3VariantRowAeneasCut.row_loop_continue_value
