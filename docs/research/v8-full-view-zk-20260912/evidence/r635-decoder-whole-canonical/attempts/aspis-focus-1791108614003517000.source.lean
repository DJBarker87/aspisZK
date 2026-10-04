import AspisV8R19.R623PackedDecoderExecution

set_option autoImplicit false

namespace AspisV8R19.R636DecoderAcceptedHeader

open Aeneas Aeneas.Std Result
open Aeneas.Std.WP
open AspisV8R19.R623PackedDecoderExecution

/-- A successful actual selected packed decoder call passes the outer header
checks.  This records only the accepted header consequences; the loop body is
reused through `decoder_complete`. -/
theorem accepted_header {N : Usize} (hN : N.val ≤ 104) (bytes : Slice U8)
    (out out1 : Array U32 N)
    (h : AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into bytes out =
      .ok (core.result.Result.Ok (), out1)) :
    0 < N.val ∧ N.val % 8 = 0 ∧ bytes.val.length = 31 * (N.val / 8) := by
  rw [decoder_complete] at h
  unfold packedDecoder at h
  have hNz : N ≠ 0#usize := by
    intro hz
    simp [hz] at h
  simp only [hNz, if_false] at h
  have hrem_spec := UScalar.rem_spec N (y := 8#usize) (by decide : (8#usize : Usize).val ≠ 0)
  obtain ⟨r, hrem, hrval⟩ := Aeneas.Std.WP.spec_imp_exists hrem_spec
  rw [hrem] at h
  simp only [bind_tc_ok] at h
  have hrzero : r = 0#usize := by
    by_contra hne
    simp [hne] at h
  obtain ⟨q, hdiv, hq⟩ := UScalar.div_spec N (y := 8#usize) (by decide : (8#usize : Usize).val ≠ 0)
  rw [hdiv] at h
  simp only [bind_tc_ok] at h
  simp [hrzero, lift] at h
  split at h <;> rename_i hcheck
  · have hLen : bytes.val.length = (Std.Usize.wrapping_mul q 31#usize).val := by
      simpa [UScalar.wrapping_mul_val_eq] using hcheck
    have hqle : q.val ≤ 13 := by
      change q.val = N.val / 8 at hq
      rw [hq]
      omega
    have hmax : 403 ≤ Usize.max := by scalar_tac
    have hprod : q.val * (31#usize : Usize).val ≤ Usize.max := by
      change q.val * 31 ≤ Usize.max
      omega
    have hmul : (q * 31#usize : Result Usize) = .ok (Std.Usize.wrapping_mul q 31#usize) :=
      AspisV8R19.R152WrappingBounds.checked_mul_eq_wrapping q 31#usize hprod
    have hmul_spec : (q * 31#usize : Result Usize) ⦃ z =>
        z.val = q.val * (31#usize : Usize).val ⦄ := by
      apply UScalar.mul_spec
      simpa only [UScalar.max_USize_eq] using hprod
    obtain ⟨z, hz, hzval⟩ := Aeneas.Std.WP.spec_imp_exists hmul_spec
    rw [hmul] at hz
    injection hz with hzw
    rw [← hzw] at hzval
    have hwval : (Std.Usize.wrapping_mul q 31#usize).val = q.val * 31 := by
      change (Std.Usize.wrapping_mul q 31#usize).val = q.val * (31#usize : Usize).val at hzval ⊢
      exact hzval
    constructor
    · have hnzval : N.val ≠ 0 := by
        intro hn
        apply hNz
        apply UScalar.eq_of_val_eq
        simpa [hn]
      omega
    constructor
    · rw [hrzero] at hrval
      simpa using hrval.symm
    · calc
        bytes.val.length = (Std.Usize.wrapping_mul q 31#usize).val := hLen
        _ = q.val * 31 := hwval
        _ = 31 * (N.val / 8) := by change q.val * 31 = 31 * (N.val / 8); rw [hq]; omega
  · simp at h

#print axioms accepted_header
end AspisV8R19.R636DecoderAcceptedHeader
