import PV_B3P_DirectMask17227
import PV_B3P_MaskBody10_4097227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 Result
set_option autoImplicit false
attribute [local irreducible] Array.index_usize aspis_core.field.QM31.add
theorem mask_clear17_4097 : (4097#u16 &&& (U16.wrapping_sub 4097#u16 1#u16)) = 4096#u16 := by rfl
theorem mask_direct17_4097 (ones zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize)
    (count_law : ones 4097#u16 = .ok 2#u32)
    (trail_4097 : zeros 4097#u16 = .ok 0#u32)
    (trail_4096 : zeros 4096#u16 = .ok 12#u32)
    : host_copy_terminal.selector_mask_sum_16 ones zeros values 4097#u16 =
      reference_copy_terminal.selector_mask_sum_16 values 4097#u16 := by
  rw [mask_entry17 ones zeros values 4097#u16 2#u32 count_law (by scalar_tac)]
  rw [mask_body_binding10_4097,PV_B3P_Mask227.result_4097]
  have clear_4097 : (4097#u16 &&& (U16.wrapping_sub 4097#u16 1#u16)) = 4096#u16 := by rfl
  have step_4097 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 4097#u16 sum 0#u32 (by decide) trail_4097
  have clear_4096 : (4096#u16 &&& (U16.wrapping_sub 4096#u16 1#u16)) = 0#u16 := by rfl
  have step_4096 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 4096#u16 sum 12#u32 (by decide) trail_4096
  simp only [step_4097,clear_4097,step_4096,clear_4096,mask_loop_stop17]
  have cast_0 : UScalar.cast .Usize 0#u32 = 0#usize := by scalar_tac
  have cast_12 : UScalar.cast .Usize 12#u32 = 12#usize := by scalar_tac
  simp only [mask_add17,mask_step10,mask_read10,cast_0,cast_12]
#print axioms mask_direct17_4097
end PV_B3P_Direct17227
