import NNH_SliceEq
set_option autoImplicit false
namespace NNH_SliceEqValue
open Aeneas Aeneas.Std
attribute [local instance] Classical.propDecidable

theorem value (left right : Slice U8) :
 core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 left right=.ok (decide (left.val=right.val)) := by
 unfold core.slice.cmp.PartialEqSlice.eq
 by_cases width : left.val.length=right.val.length
 · rw [if_pos width]
   exact NBG_Utilities.lists _ _ width
 · have different : left.val≠right.val := fun same=>width (congrArg List.length same)
   rw [if_neg width]
   simp only [different,decide_false]
#print axioms value
end NNH_SliceEqValue
