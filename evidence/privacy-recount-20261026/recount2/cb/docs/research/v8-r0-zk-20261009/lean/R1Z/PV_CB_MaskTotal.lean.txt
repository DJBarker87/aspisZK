import R1Z.PV_CB_MaskLinearsTotal
import R1Z.PV_CB_MaskFillTotal
import R1Z.PV_CB_MaskHornerTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_MaskTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
abbrev Q := ProverRwFull.aspis_core.field.QM31
/-- Totality of the prepared current-arithmetic control model. The retained
native correspondence obligation is not assumed or discharged here. -/
theorem total (c1 : Array Q 16#usize) (mask : Array Q 10#usize) (g : Q)
    (point : Array Q 10#usize) :
    Total (PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value c1 mask g point) := by
  unfold PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value
  apply bind_total (PV_CB_MaskLinearsTotal.linears_total point)
  intro pair
  rcases pair with ⟨linear,explicitLinear⟩
  apply bind_total (PV_CB_MaskFillTotal.c1 c1 _);intro coeff1
  apply bind_total (PV_CB_MaskFillTotal.mask mask _);intro coeff2
  apply bind_total (PV_CB_PreparedTotal.new _);intro prepared
  apply bind_total (ProverRwP6ArrayRead.read coeff2 26#usize (by decide));intro shared
  simp only [core.iter.traits.iterator.Iterator.rev.trait_default,bind_tc_ok]
  apply bind_total (PV_CB_MaskHornerTotal.loop_total coeff2 prepared shared);intro shared1
  apply bind_total (PV_CB_MaskLeaves.power explicitLinear);intro power
  apply bind_total (PV_CB_CurrentTotal.q_add _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_mul _ _);intro _
  exact PV_CB_CurrentTotal.q_add _ _
#print axioms total
end R1Z.PV_CB_MaskTotal
