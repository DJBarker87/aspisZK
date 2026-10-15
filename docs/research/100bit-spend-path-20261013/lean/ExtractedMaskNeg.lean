import ExtractedMaskReducerOps
import AspisR1SelectedMaskProbe.Funs

/-! Canonical-input success/value fact for the actual extracted M31.neg.
This is an operation-level helper for the current CM31 `mul_i` call graph. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskNeg

open Aeneas.Std Result Error

abbrev M31 := AspisR1SelectedMaskProbe.field.M31
abbrev P : Nat := 2147483647

theorem sourceP_value : AspisR1SelectedMaskProbe.field.P.val = P := by
  rw [AspisR1SelectedMaskProbe.field.P]
  rfl

theorem current_neg_mod (x : M31) (hx : x.val < P) :
    ∃ z : M31,
      AspisR1SelectedMaskProbe.field.M31.neg x = .ok z ∧
      z.val < P ∧ z.val = (P - x.val) % P := by
  by_cases hzero : x = (0#u32)
  · subst x
    refine ⟨0#u32, ?_, ?_, ?_⟩
    · simp [AspisR1SelectedMaskProbe.field.M31.neg]
    · norm_num [P]
    · simp [P]
  · have hx0 : x.val ≠ 0 := by
      intro hv
      apply hzero
      exact UScalar.val_eq_imp x (0#u32) (by simpa using hv)
    obtain ⟨z, hz, hvz⟩ :=
      AspisR1.ExtractedMaskReducerOps.sub_success
        AspisR1SelectedMaskProbe.field.P x
        (by rw [sourceP_value]; exact Nat.le_of_lt hx)
    refine ⟨z, ?_, ?_, ?_⟩
    · simp only [AspisR1SelectedMaskProbe.field.M31.neg, hzero, if_false]
      change (do
        let i ← UScalar.sub AspisR1SelectedMaskProbe.field.P x
        ok i) = ok z
      rw [hz]
      rfl
    · rw [hvz, sourceP_value]
      omega
    · rw [hvz, sourceP_value]
      have hlt : P - x.val < P := by omega
      exact (Nat.mod_eq_of_lt hlt).symm

#print axioms sourceP_value
#print axioms current_neg_mod

end AspisR1.ExtractedMaskNeg
