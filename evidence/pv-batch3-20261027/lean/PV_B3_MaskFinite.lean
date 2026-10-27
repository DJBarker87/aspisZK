import PV_B3_MaskRank
import PV_B3_BoundedLoop
namespace PV_B3_MaskFinite
open Aeneas Aeneas.Std Result ControlFlow
open PV_B3_Forest_134 PV_B3_MaskCounter PV_B3_MaskRank
set_option autoImplicit false

def body (s : State) : Result (ControlFlow State Final) :=
  host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
    s.1 s.2.1 s.2.2.1 s.2.2.2

theorem decreases (s t : State) (h : body s = ok (cont t)) : rank t < rank s := by
  rcases s with ⟨p,c,m,i⟩
  exact rank_decreases p c m i t h

theorem loop_source (p c : Array U8 1024#usize) (m : Array U16 64#usize) (i : Usize) :
    host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop p c m i =
      PV_B3_BoundedLoop.bounded body (136-i.val) (p,c,m,i) := by
  exact PV_B3_BoundedLoop.source_eq_bounded body rank decreases
    (136-i.val) (p,c,m,i) (Nat.le_refl _)

def reference : Result Final :=
  PV_B3_BoundedLoop.bounded body 136
    (Array.repeat 1024#usize 0#u8, Array.repeat 1024#usize 0#u8,
      Array.repeat 64#usize 0#u16, 0#usize)

-- Complete Result equality to a bounded state-machine reference. This does
-- not yet identify the row masks with the original shipped implementation.
theorem op134_bounded :
    host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 = reference := by
  unfold host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 reference
  exact loop_source _ _ _ _

#print axioms body
#print axioms decreases
#print axioms loop_source
#print axioms reference
#print axioms op134_bounded
end PV_B3_MaskFinite
