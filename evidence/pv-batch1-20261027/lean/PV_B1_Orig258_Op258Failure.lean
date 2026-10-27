import PV_B1_PoleOriginal
import PV_B1_MaskShift
import PV_B1_ArrayRead
import PV_B1_LoopSteps
set_option autoImplicit false
noncomputable section
namespace PV_B1_Orig258_Op258Failure
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258

theorem body
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (clear : Bool) (row : Usize) (hrow : row < Slice.len values) (hbad : 1024 ≤ row.val) :
    PV_B1_PoleOriginal.reference.all_slots_clear_loop.body values masks chi clear row =
      fail .arrayOutOfBounds := by
  have hi := PV_B1_ArrayRead.array_fail masks (Usize.wrapping_shr row 4#u32)
    (PV_B1_MaskShift.out_of_bounds row hbad)
  simp only [PV_B1_PoleOriginal.reference.all_slots_clear_loop.body,if_pos hrow,lift,bind_tc_ok,hi]
  rfl

theorem loop
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (clear : Bool) (row : Usize) (hrow : row < Slice.len values) (hbad : 1024 ≤ row.val) :
    PV_B1_PoleOriginal.reference.all_slots_clear_loop values masks chi clear row =
      fail .arrayOutOfBounds := by
  exact PV_B1_LoopSteps.fail_step _ (clear,row) _ (body values masks chi clear row hrow hbad)
#print axioms body
#print axioms loop
end PV_B1_Orig258_Op258Failure
