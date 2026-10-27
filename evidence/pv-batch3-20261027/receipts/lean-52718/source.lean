import PV_B3_MaskGuard
namespace PV_B3_MaskRank
open Aeneas Aeneas.Std Result ControlFlow
open PV_B3_Forest_134 PV_B3_MaskCounter PV_B3_MaskGuard
set_option autoImplicit false

theorem size_positive : 0 < Usize.size := by
  rw [Usize.size_eq]
  exact Nat.two_pow_pos _

theorem size_above_limit : 136 < Usize.size := by
  have hm : 136 % Usize.size = 136 := by
    simpa using Usize.val_mod_size_eq (136#usize)
  have hb := Nat.mod_lt 136 size_positive
  omega

theorem increment_value (i : Usize) (h : i < 136#usize) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  simp only [Usize.wrapping_add_val_eq]
  change (i.val + 1) % Usize.size = i.val + 1
  apply Nat.mod_eq_of_lt
  have hi : i.val < 136 := h
  have hm := size_above_limit
  omega

def rank (state : State) : Nat := 136 - state.2.2.2.val

theorem rank_decreases (producers consumers : Array U8 1024#usize)
    (masks : Array U16 64#usize) (i : Usize) (next : State)
    (h : host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
      producers consumers masks i = ok (cont next)) :
    rank next < rank (producers,consumers,masks,i) := by
  obtain ⟨hi,hnext⟩ := continued_counter producers consumers masks i next h
  have hv : next.2.2.2.val = i.val+1 := by rw [hnext,increment_value i hi]
  unfold rank
  dsimp only
  have hi' : i.val < 136 := hi
  omega

#print axioms size_positive
#print axioms size_above_limit
#print axioms increment_value
#print axioms rank
#print axioms rank_decreases
end PV_B3_MaskRank
