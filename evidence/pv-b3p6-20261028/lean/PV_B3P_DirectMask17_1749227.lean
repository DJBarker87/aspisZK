import PV_B3P_DirectMask17227
import PV_B3P_MaskBody10_1749227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 Result
set_option autoImplicit false
attribute [local irreducible] Array.index_usize aspis_core.field.QM31.add
theorem mask_clear17_1749 : (1749#u16 &&& (U16.wrapping_sub 1749#u16 1#u16)) = 1748#u16 := by rfl
theorem mask_direct17_1749 (ones zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize)
    (count_law : ones 1749#u16 = .ok 7#u32)
    (trail_1749 : zeros 1749#u16 = .ok 0#u32)
    (trail_1748 : zeros 1748#u16 = .ok 2#u32)
    (trail_1744 : zeros 1744#u16 = .ok 4#u32)
    (trail_1728 : zeros 1728#u16 = .ok 6#u32)
    (trail_1664 : zeros 1664#u16 = .ok 7#u32)
    (trail_1536 : zeros 1536#u16 = .ok 9#u32)
    (trail_1024 : zeros 1024#u16 = .ok 10#u32)
    : host_copy_terminal.selector_mask_sum_16 ones zeros values 1749#u16 =
      reference_copy_terminal.selector_mask_sum_16 values 1749#u16 := by
  rw [mask_entry17 ones zeros values 1749#u16 7#u32 count_law (by scalar_tac)]
  rw [mask_body_binding10_1749,PV_B3P_Mask227.result_1749]
  have clear_1749 : (1749#u16 &&& (U16.wrapping_sub 1749#u16 1#u16)) = 1748#u16 := by rfl
  have step_1749 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 1749#u16 sum 0#u32 (by decide) trail_1749
  have clear_1748 : (1748#u16 &&& (U16.wrapping_sub 1748#u16 1#u16)) = 1744#u16 := by rfl
  have step_1748 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 1748#u16 sum 2#u32 (by decide) trail_1748
  have clear_1744 : (1744#u16 &&& (U16.wrapping_sub 1744#u16 1#u16)) = 1728#u16 := by rfl
  have step_1744 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 1744#u16 sum 4#u32 (by decide) trail_1744
  have clear_1728 : (1728#u16 &&& (U16.wrapping_sub 1728#u16 1#u16)) = 1664#u16 := by rfl
  have step_1728 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 1728#u16 sum 6#u32 (by decide) trail_1728
  have clear_1664 : (1664#u16 &&& (U16.wrapping_sub 1664#u16 1#u16)) = 1536#u16 := by rfl
  have step_1664 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 1664#u16 sum 7#u32 (by decide) trail_1664
  have clear_1536 : (1536#u16 &&& (U16.wrapping_sub 1536#u16 1#u16)) = 1024#u16 := by rfl
  have step_1536 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 1536#u16 sum 9#u32 (by decide) trail_1536
  have clear_1024 : (1024#u16 &&& (U16.wrapping_sub 1024#u16 1#u16)) = 0#u16 := by rfl
  have step_1024 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 1024#u16 sum 10#u32 (by decide) trail_1024
  simp only [step_1749,clear_1749,step_1748,clear_1748,step_1744,clear_1744,step_1728,clear_1728,step_1664,clear_1664,step_1536,clear_1536,step_1024,clear_1024,mask_loop_stop17]
  rfl
#print axioms mask_direct17_1749
end PV_B3P_Direct17227
