import ExtractedMaskQM31Exact

/-! Canonicality and exact-field interpretations of the two literal source
constants used by selected-mask initialization and its final arithmetic. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskConstants

open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe

abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

theorem zero_canonical : CanonicalQM field.QM31.ZERO := by
  simp [CanonicalQM, AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
    AspisR1.ExtractedMaskTowerAdd.CanonicalCM, field.QM31.ZERO,
    AspisR1.ExtractedMaskTowerAdd.P, AspisR1.ExtractedMaskM31AddSub.P]

theorem zero_decode :
    AspisR1.ExtractedMaskQM31Exact.decode field.QM31.ZERO = (0 : ExactQM) := by
  ext <;> simp [AspisR1.ExtractedMaskQM31Exact.decode, field.QM31.ZERO]

theorem one_canonical : CanonicalQM field.QM31.ONE := by
  norm_num [CanonicalQM, AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
    AspisR1.ExtractedMaskTowerAdd.CanonicalCM, field.QM31.ONE,
    AspisR1.ExtractedMaskTowerAdd.P, AspisR1.ExtractedMaskM31AddSub.P]

theorem one_decode :
    AspisR1.ExtractedMaskQM31Exact.decode field.QM31.ONE = (1 : ExactQM) := by
  ext <;> simp [AspisR1.ExtractedMaskQM31Exact.decode, field.QM31.ONE,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

#print axioms zero_canonical
#print axioms zero_decode
#print axioms one_canonical
#print axioms one_decode

end AspisR1.ExtractedMaskConstants
