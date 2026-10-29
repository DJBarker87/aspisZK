import NDL_TowerTransport
import NDD_DoubleModel
set_option autoImplicit false
namespace NDL_DoubleLaw
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NDL_TowerTransport

theorem product (x : FQ) (hx : canonQ (toQ x)) :
    ∃ p,FIn_WeightsExtract.field.QM31.mul x x=ok p ∧
      NDD_DoubleModel.Canonical p ∧ qw (toQ p)=mulQ (qw (toQ x)) (qw (toQ x)) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_TowerValues.qm_mul (toQ x) (toQ x) hx hx
  have same := qm_mul x x
  rw [run] at same
  cases h : FIn_WeightsExtract.field.QM31.mul x x with
  | fail e => simp [h] at same
  | div => simp [h] at same
  | ok p =>
    have equal : toQ p=z := by simpa [h] using same
    have cp : canonQ (toQ p) := equal.symm ▸ canonical
    refine ⟨p,rfl,?_,equal.symm ▸ value⟩
    exact ⟨cp.1.1,cp.1.2,cp.2.1,cp.2.2⟩

/-- Deterministic same-input products supply the identical two native opaque
replies. No multiplication result is assumed, and no multiplication is run in Kani. -/
theorem cohort (x : FQ) (hx : canonQ (toQ x)) :
    ∃ p,FIn_WeightsExtract.field.QM31.mul x x=ok p ∧ NDD_DoubleModel.Canonical p ∧
      qw (toQ p)=mulQ (qw (toQ x)) (qw (toQ x)) ∧
      NDD_Reference.double_observed_ref (NDD_DoubleModel.words p) (NDD_DoubleModel.words p)=
        (do let q←FIn_WeightsExtract.double x;ok (NDD_DoubleModel.words q)) := by
  obtain ⟨p,run,canonical,value⟩ := product x hx
  exact ⟨p,run,canonical,value,NDD_DoubleModel.observed x p canonical run⟩
#print axioms product
#print axioms cohort
end NDL_DoubleLaw
