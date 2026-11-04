import NGM_ProbeTransport
import NGM_DoubleModel
import ExtractedMaskQM31Mul
set_option autoImplicit false
noncomputable section
namespace NGM_DoubleProduct
open Aeneas Aeneas.Std Result NGM_ProbeTransport
abbrev Canonical := NGM_DoubleModel.Canonical
def words (x : FQ) := AspisR1.ExtractedMaskQM31Mul.wordsQM (toQ x)
/-- Exact natural-number product and canonical returned carrier for both
SAME-input product calls. This is the paired law; no multiplication is run in Kani. -/
theorem total (x : FQ) (canonical : Canonical x) :
 ∃ product : FQ, FIn_WeightsExtract.field.QM31.mul x x=ok product ∧
 Canonical product ∧ words product=
 AspisR1.ExtractedMaskQM31Mul.qmMulWords (words x) (words x) := by
 have hx : AspisR1.ExtractedMaskTowerAdd.CanonicalQM (toQ x) :=
  ⟨⟨canonical.1,canonical.2.1⟩,⟨canonical.2.2.1,canonical.2.2.2⟩⟩
 obtain ⟨z,run,cz,value⟩ := AspisR1.ExtractedMaskQM31Mul.current_qm_mul_words (toQ x) (toQ x) hx hx
 have same := qm_mul x x
 rw [run] at same
 cases h : FIn_WeightsExtract.field.QM31.mul x x with
 | fail e => simp [h] at same
 | div => simp [h] at same
 | ok product =>
  have eq : toQ product=z := by simpa [h] using same
  have cp : AspisR1.ExtractedMaskTowerAdd.CanonicalQM (toQ product) := eq.symm ▸ cz
  exact ⟨product,h,⟨cp.1.1,cp.1.2,cp.2.1,cp.2.2⟩,by simpa only [words,eq] using value⟩

theorem cohort (x : FQ) (canonical : Canonical x) :
 ∃ product : FQ, FIn_WeightsExtract.field.QM31.mul x x=ok product ∧
 Canonical product ∧ words product=
 AspisR1.ExtractedMaskQM31Mul.qmMulWords (words x) (words x) ∧
 NGM_DoubleRef.double_observed_ref (NGM_DoubleModel.words product) (NGM_DoubleModel.words product)=
 (do let out ← FIn_WeightsExtract.double x;ok (NGM_DoubleModel.words out)) := by
 obtain ⟨product,run,cp,value⟩ := total x canonical
 exact ⟨product,run,cp,value,NGM_DoubleModel.observed x product cp run⟩
#print axioms total
#print axioms cohort
end NGM_DoubleProduct
end
