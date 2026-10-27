import R1Z.PV_CB_OwnedMaskFillTotal
import R1Z.PV_CB_OwnedMaskLinearsTotal
import R1Z.PV_CB_OwnedMaskHornerTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_OwnedMaskTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
abbrev Q := ProverRwFull.aspis_core.field.QM31
theorem total (c1 : Array Q 16#usize) (mask : Array Q 10#usize) (g : Q) (p : Array Q 10#usize) :
    Total (PV_CB_OwnedMask.owned.mask c1 mask g p) := by
  unfold PV_CB_OwnedMask.owned.mask
  apply bind_total (PV_CB_OwnedMaskLinearsTotal.total p);intro pair
  apply bind_total (PV_CB_OwnedMaskFillTotal.c1 c1 _);intro coeff
  apply bind_total (PV_CB_OwnedMaskFillTotal.mask mask coeff);intro coeff
  apply bind_total (PV_CB_PreparedTotal.new _);intro prepared
  apply bind_total (ProverRwP6ArrayRead.read coeff 26#usize (by decide));intro top
  apply bind_total (PV_CB_OwnedMaskHornerTotal.total coeff prepared 26 26#usize top rfl (by decide));intro shared
  apply bind_total (PV_CB_CurrentTotal.q_square _);intro x2
  apply bind_total (PV_CB_CurrentTotal.q_square _);intro x4
  apply bind_total (PV_CB_CurrentTotal.q_square _);intro x8
  apply bind_total (PV_CB_CurrentTotal.q_square _);intro x16
  apply bind_total (PV_CB_CurrentTotal.q_mul _ _);intro a
  apply bind_total (PV_CB_CurrentTotal.q_mul _ _);intro b
  apply bind_total (PV_CB_CurrentTotal.q_add _ _);intro d
  apply bind_total (PV_CB_CurrentTotal.q_mul _ _);intro e
  exact PV_CB_CurrentTotal.q_add _ _
#print axioms total
end R1Z.PV_CB_OwnedMaskTotal
