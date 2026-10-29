import R1Z.PV_RDCD3_ForwardTotal
import R1Z.PV_RDCD3_CB_FillLoopsEq
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_V217FillTotal
open Aeneas Aeneas.Std Result PV_RDCD3_Total PV_RDCD3_CB_ForwardRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Coeff := Array Q 27#usize
namespace S
abbrev c1 := PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0
abbrev mask := PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1
end S

theorem c1 (data : Array Q 16#usize) (coeff : Coeff) :
    Total (S.c1 (between 0#usize 16#usize) data coeff) := by
  apply (congrArg Total (PV_RDCD3_CB_MaskFillLoop.c1_finite data 16 0#usize 16#usize coeff rfl)).mpr
  exact PV_RDCD3_ForwardTotal.finite_total _ 16#usize
    (fun i hi state => PV_RDCD3_CB_MaskCell.c1_total data i state hi) 16 0#usize coeff rfl

theorem mask (data : Array Q 10#usize) (coeff : Coeff) :
    Total (S.mask (between 0#usize 10#usize) data coeff) := by
  apply (congrArg Total (PV_RDCD3_CB_MaskFillLoop.mask_finite data 10 0#usize 10#usize coeff rfl)).mpr
  exact PV_RDCD3_ForwardTotal.finite_total _ 10#usize
    (fun i hi state => PV_RDCD3_CB_MaskCell.mask_total data i state hi) 10 0#usize coeff rfl
#print axioms c1
#print axioms mask
end R1Z.PV_RDCD3_V217FillTotal
