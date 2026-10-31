import PV_B3P_DirectMask17227
import PV_B3P_MaskBody10_2049227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 Result
set_option autoImplicit false
attribute [local irreducible] Array.index_usize aspis_core.field.QM31.add
theorem mask_clear17_2049 : (2049#u16 &&& (U16.wrapping_sub 2049#u16 1#u16)) = 2048#u16 := by rfl
theorem mask_direct17_2049 (ones zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize)
    (count_law : ones 2049#u16 = .ok 2#u32)
    (trail_2049 : zeros 2049#u16 = .ok 0#u32)
    (trail_2048 : zeros 2048#u16 = .ok 11#u32)
    : host_copy_terminal.selector_mask_sum_16 ones zeros values 2049#u16 =
      reference_copy_terminal.selector_mask_sum_16 values 2049#u16 := by
  rw [mask_entry17 ones zeros values 2049#u16 2#u32 count_law (by scalar_tac)]
  rw [mask_body_binding10_2049,PV_B3P_Mask227.result_2049]
  have clear_2049 : (2049#u16 &&& (U16.wrapping_sub 2049#u16 1#u16)) = 2048#u16 := by rfl
  have step_2049 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 2049#u16 sum 0#u32 (by decide) trail_2049
  have clear_2048 : (2048#u16 &&& (U16.wrapping_sub 2048#u16 1#u16)) = 0#u16 := by rfl
  have step_2048 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 2048#u16 sum 11#u32 (by decide) trail_2048
  simp only [step_2049,clear_2049,step_2048,clear_2048,mask_loop_stop17]
  rfl
#print axioms mask_direct17_2049
end PV_B3P_Direct17227
