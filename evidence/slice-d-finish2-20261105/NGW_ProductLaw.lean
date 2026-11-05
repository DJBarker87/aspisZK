import NGW_ConstructorQM
import NGM_ProbeTransport
set_option autoImplicit false
namespace NGW_ProductLaw
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NGM_ProbeTransport NGW_ConstructorQM

theorem total (x y : FQ) (hx : Canon x) (hy : Canon y) :
 ∃ product : FQ,FIn_WeightsExtract.field.QM31.mul x y=ok product ∧
 Canon product ∧ qw (toQ product)=mulQ (qw (toQ x)) (qw (toQ y)) := by
 have cx : canonQ (toQ x) := hx
 have cy : canonQ (toQ y) := hy
 obtain ⟨z,run,cz,value⟩ := LPi_TowerValues.qm_mul (toQ x) (toQ y) cx cy
 have same := qm_mul x y
 rw [run] at same
 cases h : FIn_WeightsExtract.field.QM31.mul x y with
 | fail e => simp [h] at same
 | div => simp [h] at same
 | ok product =>
  have equal : toQ product=z := by simpa [h] using same
  have cp : canonQ (toQ product) := equal.symm ▸ cz
  exact ⟨product,rfl,cp,equal.symm ▸ value⟩

#print axioms total
end NGW_ProductLaw
