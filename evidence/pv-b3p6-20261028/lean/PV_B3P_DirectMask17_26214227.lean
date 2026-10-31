import PV_B3P_DirectMask17227
import PV_B3P_MaskBody10_26214227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 Result
set_option autoImplicit false
attribute [local irreducible] Array.index_usize aspis_core.field.QM31.add
theorem mask_clear17_26214 : (26214#u16 &&& (U16.wrapping_sub 26214#u16 1#u16)) = 26212#u16 := by rfl
theorem mask_direct17_26214 (ones zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize)
    (count_law : ones 26214#u16 = .ok 8#u32)
    (trail_26214 : zeros 26214#u16 = .ok 1#u32)
    (trail_26212 : zeros 26212#u16 = .ok 2#u32)
    (trail_26208 : zeros 26208#u16 = .ok 5#u32)
    (trail_26176 : zeros 26176#u16 = .ok 6#u32)
    (trail_26112 : zeros 26112#u16 = .ok 9#u32)
    (trail_25600 : zeros 25600#u16 = .ok 10#u32)
    (trail_24576 : zeros 24576#u16 = .ok 13#u32)
    (trail_16384 : zeros 16384#u16 = .ok 14#u32)
    : host_copy_terminal.selector_mask_sum_16 ones zeros values 26214#u16 =
      reference_copy_terminal.selector_mask_sum_16 values 26214#u16 := by
  rw [mask_entry17 ones zeros values 26214#u16 8#u32 count_law (by scalar_tac)]
  rw [mask_body_binding10_26214,PV_B3P_Mask227.result_26214]
  have clear_26214 : (26214#u16 &&& (U16.wrapping_sub 26214#u16 1#u16)) = 26212#u16 := by rfl
  have step_26214 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 26214#u16 sum 1#u32 (by decide) trail_26214
  have clear_26212 : (26212#u16 &&& (U16.wrapping_sub 26212#u16 1#u16)) = 26208#u16 := by rfl
  have step_26212 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 26212#u16 sum 2#u32 (by decide) trail_26212
  have clear_26208 : (26208#u16 &&& (U16.wrapping_sub 26208#u16 1#u16)) = 26176#u16 := by rfl
  have step_26208 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 26208#u16 sum 5#u32 (by decide) trail_26208
  have clear_26176 : (26176#u16 &&& (U16.wrapping_sub 26176#u16 1#u16)) = 26112#u16 := by rfl
  have step_26176 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 26176#u16 sum 6#u32 (by decide) trail_26176
  have clear_26112 : (26112#u16 &&& (U16.wrapping_sub 26112#u16 1#u16)) = 25600#u16 := by rfl
  have step_26112 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 26112#u16 sum 9#u32 (by decide) trail_26112
  have clear_25600 : (25600#u16 &&& (U16.wrapping_sub 25600#u16 1#u16)) = 24576#u16 := by rfl
  have step_25600 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 25600#u16 sum 10#u32 (by decide) trail_25600
  have clear_24576 : (24576#u16 &&& (U16.wrapping_sub 24576#u16 1#u16)) = 16384#u16 := by rfl
  have step_24576 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 24576#u16 sum 13#u32 (by decide) trail_24576
  have clear_16384 : (16384#u16 &&& (U16.wrapping_sub 16384#u16 1#u16)) = 0#u16 := by rfl
  have step_16384 (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values 16384#u16 sum 14#u32 (by decide) trail_16384
  simp only [step_26214,clear_26214,step_26212,clear_26212,step_26208,clear_26208,step_26176,clear_26176,step_26112,clear_26112,step_25600,clear_25600,step_24576,clear_24576,step_16384,clear_16384,mask_loop_stop17]
  have cast_1 : UScalar.cast .Usize 1#u32 = 1#usize := by scalar_tac
  have cast_2 : UScalar.cast .Usize 2#u32 = 2#usize := by scalar_tac
  have cast_5 : UScalar.cast .Usize 5#u32 = 5#usize := by scalar_tac
  have cast_6 : UScalar.cast .Usize 6#u32 = 6#usize := by scalar_tac
  have cast_9 : UScalar.cast .Usize 9#u32 = 9#usize := by scalar_tac
  have cast_10 : UScalar.cast .Usize 10#u32 = 10#usize := by scalar_tac
  have cast_13 : UScalar.cast .Usize 13#u32 = 13#usize := by scalar_tac
  have cast_14 : UScalar.cast .Usize 14#u32 = 14#usize := by scalar_tac
  simp only [mask_add17,mask_step10,mask_read10,cast_1,cast_2,cast_5,cast_6,cast_9,cast_10,cast_13,cast_14]
  rfl
#print axioms mask_direct17_26214
end PV_B3P_Direct17227
