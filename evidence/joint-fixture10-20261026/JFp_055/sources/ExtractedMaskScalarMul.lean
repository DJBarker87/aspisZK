import ExtractedMaskReducer
import ExtractedMaskTowerAdd

/-! Scalar multiplication in the newly extracted current CM31/QM31 operations.
The proofs reuse the current extracted M31 reducer and preserve explicit
canonical-coordinate results. This is a word-coordinate result only. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskScalarMul

open Aeneas.Std Result

abbrev CM := AspisR1SelectedMaskProbe.field.CM31
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev M31 := AspisR1SelectedMaskProbe.field.M31
abbrev P := AspisR1.ExtractedMaskTowerAdd.P
abbrev CanonicalCM := AspisR1.ExtractedMaskTowerAdd.CanonicalCM
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

theorem current_cm_mul_m31_mod (x : CM) (s : M31) :
    ∃ z : CM,
      AspisR1SelectedMaskProbe.field.CM31.mul_m31 x s = .ok z ∧
      CanonicalCM z ∧
      z.a.val = (x.a.val * s.val) % P ∧
      z.b.val = (x.b.val * s.val) % P := by
  obtain ⟨a, ha, hva, hca⟩ :=
    AspisR1.ExtractedMaskReducer.current_mul_mod x.a s
  obtain ⟨b, hb, hvb, hcb⟩ :=
    AspisR1.ExtractedMaskReducer.current_mul_mod x.b s
  exact ⟨⟨a, b⟩,
    by simp only [AspisR1SelectedMaskProbe.field.CM31.mul_m31,
      ha, hb, bind_tc_ok],
    ⟨hca, hcb⟩, hva, hvb⟩

theorem current_qm_mul_m31_mod (x : QM) (s : M31) :
    ∃ z : QM,
      AspisR1SelectedMaskProbe.field.QM31.mul_m31 x s = .ok z ∧
      CanonicalQM z ∧
      z.c0.a.val = (x.c0.a.val * s.val) % P ∧
      z.c0.b.val = (x.c0.b.val * s.val) % P ∧
      z.c1.a.val = (x.c1.a.val * s.val) % P ∧
      z.c1.b.val = (x.c1.b.val * s.val) % P := by
  obtain ⟨a, ha, hca, hva, hvb⟩ := current_cm_mul_m31_mod x.c0 s
  obtain ⟨b, hb, hcb, hvc, hvd⟩ := current_cm_mul_m31_mod x.c1 s
  exact ⟨⟨a, b⟩,
    by simp only [AspisR1SelectedMaskProbe.field.QM31.mul_m31,
      ha, hb, bind_tc_ok],
    ⟨hca, hcb⟩, hva, hvb, hvc, hvd⟩

#print axioms current_cm_mul_m31_mod
#print axioms current_qm_mul_m31_mod

end AspisR1.ExtractedMaskScalarMul
