import PV_B3_Forest_134_Funs
namespace PV_B3_MaskLoopStop
open Aeneas Aeneas.Std Result ControlFlow
open PV_B3_Forest_134
set_option autoImplicit false

theorem body_done (producers consumers : Array U8 1024#usize)
    (masks : Array U16 64#usize) (i : Usize) (h : 136#usize ≤ i) :
    host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
      producers consumers masks i = ok (done (core.result.Result.Ok masks)) := by
  have hi : ¬ i < 136#usize := by
    intro hlt
    exact Nat.not_lt_of_ge h hlt
  simp only [host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body,
    if_neg hi]
#print axioms body_done
end PV_B3_MaskLoopStop
