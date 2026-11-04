import NGD_SlotBoundaries
import NBE_SlotLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_SlotModel
theorem reference (slot : Usize) (bound : slot.val ≤ 6) :
    NGD_SlotRef.slot_offset slot =
      ok (AspisR1.Port4B_SlotInstall.offset slot.val bound) := by
  have cases : slot = 0#usize ∨ slot = 1#usize ∨ slot = 2#usize ∨ slot = 3#usize ∨
      slot = 4#usize ∨ slot = 5#usize ∨ slot = 6#usize := by scalar_tac
  rcases cases with h | h | h | h | h | h | h
  all_goals subst slot
  all_goals simp only [NGD_SlotBoundaries.boundary0, NGD_SlotBoundaries.boundary1,
    NGD_SlotBoundaries.boundary2, NGD_SlotBoundaries.boundary3,
    NGD_SlotBoundaries.boundary4, NGD_SlotBoundaries.boundary5,
    NGD_SlotBoundaries.boundary6]
  all_goals congr 1
  all_goals apply UScalar.eq_of_val_eq
  all_goals rfl
#print axioms reference
end NGD_SlotModel
