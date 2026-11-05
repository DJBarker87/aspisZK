import NGX_COMBINED_IMPORT
import ExtractedMaskQM31Mul
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHG_Product
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev Q := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev Canonical (x : Q) := AspisR1.ExtractedMaskTowerAdd.CanonicalQM (genQToProbe x)
abbrev Words := AspisR1.ExtractedMaskQM31Mul.wordsQM
abbrev NaturalProduct := AspisR1.ExtractedMaskQM31Mul.qmMulWords

/-- Exact natural modular coordinates for the emitted operation on the SAME
canonical operands. The probe equality is reused, not re-extracted or assumed. -/
theorem words (x y : Q) (hx : Canonical x) (hy : Canonical y) :
 ∃ z,AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y=ok z ∧
 Canonical z ∧ Words (genQToProbe z)=NaturalProduct (Words (genQToProbe x)) (Words (genQToProbe y)) := by
 obtain ⟨z,call,canonical,natural⟩:=AspisR1.ExtractedMaskQM31Mul.current_qm_mul_words
  (genQToProbe x) (genQToProbe y) hx hy
 have mapped : resultMap genQToProbe
  (AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y)=ok z := by
  rw [generated_qm_mul_eq_probe]
  exact call
 obtain ⟨w,run,identity⟩:=AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23.resultMap_eq_ok_inv genQToProbe _ z mapped
 refine ⟨w,run,?_,?_⟩
 · change AspisR1.ExtractedMaskTowerAdd.CanonicalQM (genQToProbe w)
   rw [identity];exact canonical
 · change Words (genQToProbe w)=_
   rw [identity];exact natural

noncomputable def reply (x y : Q) (hx : Canonical x) (hy : Canonical y) : Q :=
 Classical.choose (words x y hx hy)

theorem returns (x y : Q) (hx : Canonical x) (hy : Canonical y) :
 AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y=ok (reply x y hx hy) :=
 (Classical.choose_spec (words x y hx hy)).1

theorem canonical (x y : Q) (hx : Canonical x) (hy : Canonical y) :
 Canonical (reply x y hx hy) := (Classical.choose_spec (words x y hx hy)).2.1

theorem natural (x y : Q) (hx : Canonical x) (hy : Canonical y) :
 Words (genQToProbe (reply x y hx hy))=
 NaturalProduct (Words (genQToProbe x)) (Words (genQToProbe y)) :=
 (Classical.choose_spec (words x y hx hy)).2.2

#print axioms words
#print axioms returns
#print axioms canonical
#print axioms natural
end AspisR1.NHG_Product
