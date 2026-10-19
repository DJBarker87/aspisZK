import RawExtractedSemanticCallOpsV20
import RawExtractedSemanticQM31Ops

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23

open Aeneas Aeneas.Std Result

abbrev GenQ := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev ProbeQ := AspisR1SelectedMaskProbe.field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev ExactQ := AspisR1.ExtractedMaskQM31Exact.QM31Exact

open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1.ExtractedMaskQM31Exact

theorem resultMap_eq_ok_inv {A B : Type} (f : A → B) (r : Result A) (z : B)
    (h : resultMap f r = .ok z) :
    ∃ w, r = .ok w ∧ f w = z := by
  cases r with
  | ok w => exact ⟨w, rfl, Result.ok.inj (by simpa [resultMap] using h)⟩
  | fail e => simp [resultMap] at h
  | div => simp [resultMap] at h

theorem generated_qm_add_exact (x y : GenQ)
    (hx : Canonical (genQToProbe x)) (hy : Canonical (genQToProbe y)) :
    ∃ z : GenQ,
      AspisR1SemanticCallExtraction.aspis_core.field.QM31.add x y = .ok z ∧
      Canonical (genQToProbe z) ∧
      decode (genQToProbe z) = decode (genQToProbe x) + decode (genQToProbe y) := by
  obtain ⟨z, hz, hcanon, hdecode⟩ :=
    current_qm_add_exact (genQToProbe x) (genQToProbe y) hx hy
  have hmapped : resultMap genQToProbe
      (AspisR1SemanticCallExtraction.aspis_core.field.QM31.add x y) = .ok z := by
    rw [generated_qm_add_eq_probe]
    exact hz
  obtain ⟨w, hrun, hmap⟩ := resultMap_eq_ok_inv genQToProbe _ z hmapped
  refine ⟨w, hrun, ?_, ?_⟩
  · rw [hmap]
    exact hcanon
  · rw [hmap]
    exact hdecode

theorem generated_qm_mul_exact (x y : GenQ)
    (hx : Canonical (genQToProbe x)) (hy : Canonical (genQToProbe y)) :
    ∃ z : GenQ,
      AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y = .ok z ∧
      Canonical (genQToProbe z) ∧
      decode (genQToProbe z) = decode (genQToProbe x) * decode (genQToProbe y) := by
  obtain ⟨z, hz, hcanon, hdecode⟩ :=
    current_qm_mul_exact (genQToProbe x) (genQToProbe y) hx hy
  have hmapped : resultMap genQToProbe
      (AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y) = .ok z := by
    rw [generated_qm_mul_eq_probe]
    exact hz
  obtain ⟨w, hrun, hmap⟩ := resultMap_eq_ok_inv genQToProbe _ z hmapped
  refine ⟨w, hrun, ?_, ?_⟩
  · rw [hmap]
    exact hcanon
  · rw [hmap]
    exact hdecode

#print axioms generated_qm_add_exact
#print axioms generated_qm_mul_exact

end AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23
