import R1Z.PV_CB3_Op258Ref
import R1Z.PV_CB3_MaskShift
import R1Z.PV_CB3_IndexFailure
import R1Z.PV_CB3_LoopEquations
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258Failure
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull

theorem body
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (clear : Bool) (row : Usize) (hrow : row < Slice.len values) (hbad : 1024 ≤ row.val) :
    PV_CB3_Op258Ref.reference.all_slots_clear_loop.body values masks chi clear row =
      fail .arrayOutOfBounds := by
  have hi := PV_CB3_IndexFailure.array_fail masks (Usize.wrapping_shr row 4#u32)
    (PV_CB3_MaskShift.out_of_bounds row hbad)
  simp only [PV_CB3_Op258Ref.reference.all_slots_clear_loop.body,if_pos hrow,lift,bind_tc_ok,hi]
  rfl

theorem loop
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (clear : Bool) (row : Usize) (hrow : row < Slice.len values) (hbad : 1024 ≤ row.val) :
    PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi clear row =
      fail .arrayOutOfBounds := by
  exact PV_CB3_LoopEquations.fail_step _ (clear,row) _ (body values masks chi clear row hrow hbad)
#print axioms body
#print axioms loop
end R1Z.PV_CB3_Op258Failure
