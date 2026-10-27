import R1Z.PV_CB_OwnedMaskLinears
import R1Z.PV_CB_MaskLinearsTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_OwnedMaskLinearsTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
abbrev Q := ProverRwFull.aspis_core.field.QM31
theorem fold_total (point : Array Q 10#usize) (fuel : Nat) (e : Usize) (s w : Q)
    (rank : e.val=fuel) (bound : fuel≤10) :
    Total (PV_CB_OwnedMask.owned.linears_fold point e s w) := by
  rw [PV_CB_OwnedMaskLinears.source point fuel e s w rank]
  exact PV_CB_MaskLinearsTotal.finite_total point fuel e s w rank bound
theorem total (point : Array Q 10#usize) : Total (PV_CB_OwnedMask.owned.linears point) := by
  unfold PV_CB_OwnedMask.owned.linears
  apply bind_total (fold_total point 10 10#usize _ _ rfl (by decide));intro pair
  apply bind_total (PV_CB_CurrentTotal.q_scale _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_scale _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_add _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_scale _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_scale _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_add _ _);intro _
  exact ok_total _
#print axioms fold_total
#print axioms total
end R1Z.PV_CB_OwnedMaskLinearsTotal
