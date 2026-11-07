import NBG_Utilities
set_option autoImplicit false
namespace NNH_SliceEq
open Aeneas Aeneas.Std

theorem self (s : Slice U8) : core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s s=.ok true := by
 unfold core.slice.cmp.PartialEqSlice.eq
 rw [if_pos rfl,NBG_Utilities.lists s.val s.val rfl]
 simp only [decide_true]
#print axioms self
end NNH_SliceEq
