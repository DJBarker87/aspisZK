import ExtractedMaskPreparedClosure
import ExtractedMaskArrayThree
import ExtractedMaskQM31Mul

/-! The actual extracted prepared CM31 fragment computes the same modular
word formula as ordinary CM31 multiplication. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskPreparedComponent
open Aeneas.Std Result
open AspisR1SelectedMaskProbe
open ExtractedMaskPreparedState ExtractedMaskTowerAdd ExtractedMaskArrayThree

theorem current_component_mul_words
    (a : Component) (x y : CM)
    (hx : CanonicalCM x) (hy : CanonicalCM y) (hp : ComponentFor a x) :
    ∃ z : CM,
      field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (a, y) = .ok z ∧ CanonicalCM z ∧
      (z.a.val, z.b.val) = ExtractedMaskQM31Mul.mulWords
        (x.a.val, x.b.val) (y.a.val, y.b.val) := by
  obtain ⟨s, rfl, hs, _⟩ := hp
  obtain ⟨t, ht, hvt, _⟩ :=
    ExtractedMaskM31AddSub.current_add_mod y.a y.b hy.1 hy.2
  obtain ⟨m0, h0, hv0, hc0⟩ := ExtractedMaskReducer.current_mul_mod x.a y.a
  obtain ⟨m1, h1, hv1, hc1⟩ := ExtractedMaskReducer.current_mul_mod x.b y.b
  obtain ⟨m2, h2, hv2, hc2⟩ := ExtractedMaskReducer.current_mul_mod s t
  have hv2' : m2.val = ((x.a.val + x.b.val) * (y.a.val + y.b.val)) %
      ExtractedMaskM31AddSub.P := by
    rw [hv2, hs, hvt]
    exact (Nat.mul_mod _ _ _).symm
  obtain ⟨low, hl, hvl, hcl⟩ :=
    ExtractedMaskM31AddSub.current_sub_mod m0 m1 hc0 hc1
  obtain ⟨high0, hh0, hvh0, hch0⟩ :=
    ExtractedMaskM31AddSub.current_sub_mod m2 m0 hc2 hc0
  obtain ⟨high, hh, hvh, hch⟩ :=
    ExtractedMaskM31AddSub.current_sub_mod high0 m1 hch0 hc1
  refine ⟨⟨low, high⟩, ?_, ⟨hcl, hch⟩, ?_⟩
  · rw [ExtractedMaskPreparedClosure.call_eq]
    simp only [index0, index1, index2, h0, h1, ht, h2, hl, hh0, hh, bind_tc_ok]
  · apply Prod.ext
    · simpa only [ExtractedMaskQM31Mul.mulWords, hv0, hv1] using hvl
    · simpa only [ExtractedMaskQM31Mul.mulWords, hvh0, hv2', hv0, hv1] using hvh

#print axioms current_component_mul_words
end AspisR1.ExtractedMaskPreparedComponent
