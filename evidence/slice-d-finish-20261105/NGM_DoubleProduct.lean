import NGM_ProbeTransport
import NGM_DoubleModel
set_option autoImplicit false
namespace NGM_DoubleProduct
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NGM_ProbeTransport
abbrev Canonical := NGM_DoubleModel.Canonical
/-- Exact natural QM31 multiplication law on the canonical caller domain. -/
theorem total (x : FQ) (canonical : Canonical x) :
 ∃ product : FQ,FIn_WeightsExtract.field.QM31.mul x x=ok product ∧
 Canonical product ∧ qw (toQ product)=mulQ (qw (toQ x)) (qw (toQ x)) := by
 have hx : canonQ (toQ x) := ⟨⟨canonical.1,canonical.2.1⟩,⟨canonical.2.2.1,canonical.2.2.2⟩⟩
 obtain ⟨z,run,cz,value⟩ := LPi_TowerValues.qm_mul (toQ x) (toQ x) hx hx
 have same := qm_mul x x
 rw [run] at same
 cases h : FIn_WeightsExtract.field.QM31.mul x x with
 | fail e => simp [h] at same
 | div => simp [h] at same
 | ok product =>
  have equal : toQ product=z := by simpa [h] using same
  have cp : canonQ (toQ product) := equal.symm ▸ cz
  exact ⟨product,rfl,⟨cp.1.1,cp.1.2,cp.2.1,cp.2.2⟩,equal.symm ▸ value⟩

theorem cohort (x : FQ) (canonical : Canonical x) :
 ∃ product : FQ,FIn_WeightsExtract.field.QM31.mul x x=ok product ∧
 Canonical product ∧ qw (toQ product)=mulQ (qw (toQ x)) (qw (toQ x)) ∧
 NGM_DoubleRef.double_observed_ref (NGM_DoubleModel.words product) (NGM_DoubleModel.words product)=
 (do let out ← FIn_WeightsExtract.double x;ok (NGM_DoubleModel.words out)) := by
 obtain ⟨product,run,cp,value⟩ := total x canonical
 exact ⟨product,run,cp,value,NGM_DoubleModel.observed x product cp run⟩
#print axioms total
#print axioms cohort
end NGM_DoubleProduct
