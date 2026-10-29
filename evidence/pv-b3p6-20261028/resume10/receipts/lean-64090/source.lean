import PV_B3P_MaskBodyStep10227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] Array.index_usize aspis_core.field.QM31.add

theorem mask_body_binding10_2048 (values : Array aspis_core.field.QM31 16#usize) :
    reference_copy_terminal.selector_mask_sum_16 values 2048#u16 =
      PV_B3P_Mask227.foldResult (mask_step10 values) (PV_B3P_Mask227.walk 16 2048) aspis_core.field.QM31.ZERO := by
  rw [PV_B3P_Mask227.result_2048]
  conv_rhs => simp only [mask_step10,mask_read10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok,result_right]
  all_goals rfl
#print axioms mask_body_binding10_2048
end PV_B3P_Binding10227
