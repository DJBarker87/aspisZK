import S3VariantRowAccumulatorInvariant

open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1.S3VariantRowAeneasCut

private theorem and3_eq_mod (x : Nat) : x &&& 3 = x % 4 := by
  have h := Nat.and_two_pow_sub_one_eq_mod x 2
  norm_num at h ⊢
  exact h

def rowFormula (j : Nat) : Nat :=
  (j % 4) * 64 + ((j / 4) % 4) * 256 +
  ((j / 16) % 4) * 16 + ((j / 64) % 4) + ((j / 256) % 4) * 4

private theorem rowPrefix_ordered (j : Nat) :
    rowPrefix j 5 =
      (((j / 64) % 4) ||| (((j / 256) % 4) * 4) |||
        (((j / 16) % 4) * 16) ||| (((j % 4) * 64) ||| (((j / 4) % 4) * 256))) := by
  simp [rowPrefix, rowTerm, tauSlot, and3_eq_mod, Nat.shiftRight_eq_div_pow]
  ac_rfl

theorem rowPrefix_eq_rowFormula (j : Nat) : rowPrefix j 5 = rowFormula j := by
  have h0 : j % 4 < 4 := Nat.mod_lt _ (by omega)
  have h1 : (j / 4) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h2 : (j / 16) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h3 : (j / 64) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h4 : (j / 256) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hlo4 : (j / 64) % 4 + ((j / 256) % 4) * 4 < 16 := by omega
  have hlo6 : (j / 64) % 4 + ((j / 256) % 4) * 4 + ((j / 16) % 4) * 16 < 64 := by omega
  have hlo8 : (j / 64) % 4 + ((j / 256) % 4) * 4 +
      ((j / 16) % 4) * 16 + (j % 4) * 64 < 256 := by omega
  have hcombine1 :
      ((j / 256) % 4) * 4 + ((j / 64) % 4) =
        (((j / 256) % 4) * 4) ||| ((j / 64) % 4) := by
    have hh := Nat.two_pow_add_eq_or_of_lt (i := 2) h3 ((j / 256) % 4)
    simpa [Nat.mul_comm] using hh
  have hcombine2 :
      ((j / 16) % 4) * 16 +
        (((j / 256) % 4) * 4 + ((j / 64) % 4)) =
      (((j / 16) % 4) * 16) ||| (((j / 256) % 4) * 4 + ((j / 64) % 4)) := by
    have hh : ((j / 256) % 4) * 4 + ((j / 64) % 4) < 16 := by omega
    have hpow := Nat.two_pow_add_eq_or_of_lt (i := 4) hh ((j / 16) % 4)
    simpa [Nat.mul_comm] using hpow
  have hcombine3 :
      (j % 4) * 64 +
        (((j / 16) % 4) * 16 + (((j / 256) % 4) * 4 + ((j / 64) % 4))) =
      ((j % 4) * 64) |||
        (((j / 16) % 4) * 16 + (((j / 256) % 4) * 4 + ((j / 64) % 4))) := by
    have hh : ((j / 16) % 4) * 16 +
        (((j / 256) % 4) * 4 + ((j / 64) % 4)) < 64 := by omega
    have hpow := Nat.two_pow_add_eq_or_of_lt (i := 6) hh (j % 4)
    simpa [Nat.mul_comm] using hpow
  have hcombine4 :
      ((j / 4) % 4) * 256 +
        ((j % 4) * 64 +
          (((j / 16) % 4) * 16 + (((j / 256) % 4) * 4 + ((j / 64) % 4)))) =
      (((j / 4) % 4) * 256) |||
        ((j % 4) * 64 +
          (((j / 16) % 4) * 16 + (((j / 256) % 4) * 4 + ((j / 64) % 4)))) := by
    have hh : (j % 4) * 64 +
        (((j / 16) % 4) * 16 + (((j / 256) % 4) * 4 + ((j / 64) % 4))) < 256 := by omega
    have hpow := Nat.two_pow_add_eq_or_of_lt (i := 8) hh ((j / 4) % 4)
    simpa [Nat.mul_comm] using hpow
  rw [rowPrefix_ordered]
  unfold rowFormula
  calc
    (((j / 64) % 4) ||| (((j / 256) % 4) * 4) |||
        (((j / 16) % 4) * 16) ||| (((j % 4) * 64) ||| (((j / 4) % 4) * 256))) =
      (((j / 4) % 4) * 256) ||| (((j % 4) * 64) |||
        (((j / 16) % 4) * 16 ||| (((j / 256) % 4) * 4 ||| ((j / 64) % 4)))) := by
          ac_rfl
    _ = ((j / 4) % 4) * 256 +
        ((j % 4) * 64 + (((j / 16) % 4) * 16 + (((j / 256) % 4) * 4 + ((j / 64) % 4)))) := by
          rw [← hcombine1, ← hcombine2, ← hcombine3, ← hcombine4]
    _ = rowFormula j := by
          dsimp [rowFormula]
          omega

end AspisR1.S3VariantRowAeneasCut
#print axioms AspisR1.S3VariantRowAeneasCut.rowPrefix_ordered
#print axioms AspisR1.S3VariantRowAeneasCut.rowPrefix_eq_rowFormula

namespace AspisR1.S3S9CurrentSourceModel

/-- Exact declaration-body cut from S3S9CurrentSourceModel.s2Row. -/
def s2Row_source_cut (j : Nat) : Nat :=
  (j % 4) * 64 + ((j / 4) % 4) * 256 +
  ((j / 16) % 4) * 16 + ((j / 64) % 4) + ((j / 256) % 4) * 4

end AspisR1.S3S9CurrentSourceModel

namespace AspisR1.S3VariantRowAeneasCut

theorem rowPrefix_eq_source_s2Row (j : Nat) :
    rowPrefix j 5 = AspisR1.S3S9CurrentSourceModel.s2Row_source_cut j := by
  rw [rowPrefix_eq_rowFormula]
  rfl

theorem s2_row_result_value (j : Std.Usize) :
    ∃ out, s2_row_result j = .ok out ∧
      out.val = AspisR1.S3S9CurrentSourceModel.s2Row_source_cut j.val := by
  obtain ⟨out, hout, hvalue⟩ := s2_row_result_prefix j
  refine ⟨out, hout, ?_⟩
  rw [hvalue, rowPrefix_eq_source_s2Row]

end AspisR1.S3VariantRowAeneasCut
#print axioms AspisR1.S3VariantRowAeneasCut.s2_row_result_value
