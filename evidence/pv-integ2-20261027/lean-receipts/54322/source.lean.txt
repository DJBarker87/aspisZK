import R1Z.PV_CB_OwnedMaskHorner
import R1Z.PV_CB_MaskHornerTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_OwnedMaskHornerTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
abbrev Q := ProverRwFull.aspis_core.field.QM31
theorem total (coeff : Array Q 27#usize) (p : PV_CB_PreparedTotal.Prepared)
    (fuel : Nat) (e : Usize) (shared : Q) (rank : e.val=fuel) (bound : fuel≤27) :
    Total (PV_CB_OwnedMask.owned.horner coeff p e shared) := by
  rw [PV_CB_OwnedMaskHorner.source coeff p fuel e shared rank]
  exact PV_CB_MaskHornerTotal.finite_total coeff p fuel e shared rank bound
#print axioms total
end R1Z.PV_CB_OwnedMaskHornerTotal
