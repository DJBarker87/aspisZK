import PV_B3_MaskCounter
namespace PV_B3_MaskGuard
open Aeneas Aeneas.Std Result ControlFlow
open PV_B3_Forest_134 PV_B3_Result PV_B3_MaskCounter
set_option autoImplicit false

def Guard (i : Usize) : ControlFlow State Final → Prop
  | .done _ => True
  | .cont _ => i < 136#usize

theorem body_guard (producers consumers : Array U8 1024#usize)
    (masks : Array U16 64#usize) (i : Usize) :
    Safe (Guard i)
      (host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
        producers consumers masks i) := by
  unfold host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
  split
  · rename_i hi
    intro cf hc
    cases cf with
    | done _ => trivial
    | cont _ => exact hi
  · intro cf hc
    cases hc
    trivial

theorem continued_counter (producers consumers : Array U8 1024#usize)
    (masks : Array U16 64#usize) (i : Usize) (next : State)
    (h : host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
      producers consumers masks i = ok (cont next)) :
    i < 136#usize ∧ next.2.2.2 = Usize.wrapping_add i 1#usize :=
  ⟨body_guard producers consumers masks i _ h,
    body_counter producers consumers masks i _ h⟩

#print axioms Guard
#print axioms body_guard
#print axioms continued_counter
end PV_B3_MaskGuard
