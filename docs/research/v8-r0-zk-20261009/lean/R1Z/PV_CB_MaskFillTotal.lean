import R1Z.PV_CB_MaskFillLoop
import R1Z.PV_CB_ForwardTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_MaskFillTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
open PV_CB_ForwardRange PV_CB_MaskCell

theorem c1 (data : Array Q 16#usize) (coeff : Coeff) :
    Total (PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0
      (between 0#usize 16#usize) data coeff) := by
  apply (congrArg ProverRwSuccessArithmeticTotal.Total
    (PV_CB_MaskFillLoop.c1_run data (between 0#usize 16#usize) coeff)).mpr
  exact PV_CB_ForwardTotal.run_total _ 16#usize
    (fun i hi c => c1_total data i c hi) coeff
theorem mask (data : Array Q 10#usize) (coeff : Coeff) :
    Total (PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1
      (between 0#usize 10#usize) data coeff) := by
  apply (congrArg ProverRwSuccessArithmeticTotal.Total
    (PV_CB_MaskFillLoop.mask_run data (between 0#usize 10#usize) coeff)).mpr
  exact PV_CB_ForwardTotal.run_total _ 10#usize
    (fun i hi c => mask_total data i c hi) coeff
#print axioms c1
#print axioms mask
end R1Z.PV_CB_MaskFillTotal
