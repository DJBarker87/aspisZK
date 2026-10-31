import PV_B3P_DirectMask17227
import PV_B3P_MaskBody10_2048227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 Result
set_option autoImplicit false
attribute [local irreducible] Array.index_usize aspis_core.field.QM31.add
theorem mask_clear17_2048 : (2048#u16 &&& (U16.wrapping_sub 2048#u16 1#u16)) = 0#u16 := by rfl
theorem mask_direct17_2048 (ones zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize)
    (count_law : ones 2048#u16 = .ok 1#u32)
    (trail_2048 : zeros 2048#u16 = .ok 11#u32)
    : host_copy_terminal.selector_mask_sum_16 ones zeros values 2048#u16 =
      reference_copy_terminal.selector_mask_sum_16 values 2048#u16 := by
  rw [mask_entry17 ones zeros values 2048#u16 1#u32 count_law (by scalar_tac)]
  rw [mask_body_binding10_2048,PV_B3P_Mask227.result_2048]
  have clear_2048 : (2048#u16 &&& (U16.wrapping_sub 2048#u16 1#u16)) = 0#u16 := by rfl
  have step_2048 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 2048#u16 sum 11#u32 (by decide) trail_2048
  simp only [step_2048,clear_2048,mask_loop_stop17]
  have cast_11 : UScalar.cast .Usize 11#u32 = 11#usize := by scalar_tac
  simp only [mask_add17,mask_step10,mask_read10,cast_11]
  rfl
#print axioms mask_direct17_2048
end PV_B3P_Direct17227
