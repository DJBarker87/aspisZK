import PV_B3_MaskLoopStop
namespace PV_B3_MaskLoopDone
open Aeneas Aeneas.Std Result ControlFlow
open PV_B3_Forest_134
set_option autoImplicit false

theorem source_done (producers consumers : Array U8 1024#usize)
    (masks : Array U16 64#usize) (i : Usize) (h : 136#usize ≤ i) :
    host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop
      producers consumers masks i = ok (core.result.Result.Ok masks) := by
  unfold host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop
  rw [loop.eq_def]
  dsimp only
  rw [PV_B3_MaskLoopStop.body_done producers consumers masks i h]
  rfl
#print axioms source_done
end PV_B3_MaskLoopDone
