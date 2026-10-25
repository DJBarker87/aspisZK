import ExtractedMaskNeg
import ExtractedMaskM31AddSub
import ExtractedMaskTowerAdd
import ExtractedMaskQM31Mul
import AspisR1SelectedMaskProbe.Funs

/-! Actual extracted CM31 basis operations over the full Aeneas runtime.
Canonical input premises are explicit. These are operation-level contracts,
not verifier-caller or protocol-refinement theorems. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskBasisComponents

open Aeneas.Std Result Error

abbrev P : Nat := AspisR1.ExtractedMaskM31AddSub.P
abbrev M31 := AspisR1SelectedMaskProbe.field.M31
abbrev CM := AspisR1SelectedMaskProbe.field.CM31

theorem current_cm31_mul_i_words (x : CM)
    (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalCM x) :
    ∃ z : CM,
      AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_i x = .ok z ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalCM z ∧
      AspisR1.ExtractedMaskTowerAdd.wordsCM z =
        ((P - x.b.val) % P, x.a.val) := by
  obtain ⟨neg, hneg, hnegcanon, hnegword⟩ :=
    AspisR1.ExtractedMaskNeg.current_neg_mod x.b hx.2
  refine ⟨⟨neg, x.a⟩, ?_, ⟨hnegcanon, hx.1⟩, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_i,
      hneg, bind_tc_ok, AspisR1SelectedMaskProbe.field.CM31.new]
  · change (neg.val, x.a.val) = _
    exact Prod.ext hnegword rfl

theorem cm31_mul_r_eq_mul_by_r (x : CM) :
    AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r x =
      AspisR1SelectedMaskProbe.field.mul_by_r x := by
  simp only [AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r,
    AspisR1SelectedMaskProbe.field.mul_by_r,
    AspisR1SelectedMaskProbe.field.CM31.new]

theorem current_cm31_mul_r_words (x : CM)
    (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalCM x) :
    ∃ z : CM,
      AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r x = .ok z ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalCM z ∧
      AspisR1.ExtractedMaskTowerAdd.wordsCM z =
        AspisR1.ExtractedMaskQM31Mul.rWords
          (AspisR1.ExtractedMaskTowerAdd.wordsCM x) := by
  obtain ⟨a2, ea2, va2, ca2⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a, ea, va, ca⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2, eb2, vb2, cb2⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b, eb, vb, cb⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a b2 hx.1 cb2
  refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
  · rw [cm31_mul_r_eq_mul_by_r]
    simp only [AspisR1SelectedMaskProbe.field.mul_by_r,
      AspisR1SelectedMaskProbe.field.M31.double,
      ea2, ea, eb2, eb, bind_tc_ok]
  · change (a.val, b.val) =
      AspisR1.ExtractedMaskQM31Mul.rWords
        (AspisR1.ExtractedMaskTowerAdd.wordsCM x)
    simp only [AspisR1.ExtractedMaskQM31Mul.rWords,
      AspisR1.ExtractedMaskTowerAdd.wordsCM]
    exact Prod.ext (by simpa only [va2] using va)
      (by simpa only [vb2] using vb)

#print axioms current_cm31_mul_i_words
#print axioms cm31_mul_r_eq_mul_by_r
#print axioms current_cm31_mul_r_words

end AspisR1.ExtractedMaskBasisComponents
