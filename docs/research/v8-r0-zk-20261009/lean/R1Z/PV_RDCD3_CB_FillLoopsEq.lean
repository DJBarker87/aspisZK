import R1Z.PV_RDCD3_CB_FillStepsEq
import R1Z.PV_RDCD3_CB_FiniteStepEq
import R1Z.PV_RDCD3_CB_MaskFillLoop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_FillLoopsEq
open Aeneas Aeneas.Std Result PV_RDCD3_CB_ForwardRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Coeff := Array Q 27#usize
theorem c1 (data : Array Q 16#usize) (coeff : Coeff) :
    PV_RDCD3_CB_OwnedMask.owned.fill_c1 data coeff 0#usize =
      PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0
        (between 0#usize 16#usize) data coeff := by
  rw [PV_RDCD3_CB_OwnedMaskFill.c1 data 16 0#usize coeff rfl]
  rw [PV_RDCD3_CB_MaskFillLoop.c1_finite data 16 0#usize 16#usize coeff rfl]
  exact PV_RDCD3_CB_FiniteStepEq.source _ _ 16#usize
    (fun i hi state => PV_RDCD3_CB_FillStepsEq.c1 data i state hi) 16 0#usize coeff rfl
theorem mask (data : Array Q 10#usize) (coeff : Coeff) :
    PV_RDCD3_CB_OwnedMask.owned.fill_mask data coeff 0#usize =
      PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1
        (between 0#usize 10#usize) data coeff := by
  rw [PV_RDCD3_CB_OwnedMaskFill.mask data 10 0#usize coeff rfl]
  rw [PV_RDCD3_CB_MaskFillLoop.mask_finite data 10 0#usize 10#usize coeff rfl]
  exact PV_RDCD3_CB_FiniteStepEq.source _ _ 10#usize
    (fun i hi state => PV_RDCD3_CB_FillStepsEq.mask data i state hi) 10 0#usize coeff rfl
#print axioms c1
#print axioms mask
end R1Z.PV_RDCD3_CB_FillLoopsEq
