import R1Z.PV_CBL_SoftBlocks
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_SoftBlocksAppend
open PV_CBL_SoftBlocks
set_option autoImplicit false
theorem value_append (state : State) (left right : List Block) :
    value state (left++right) = value (value state left) right := by
  exact List.foldl_append
theorem source_append (state : State) (left right : List Block) :
    source state (left++right) = (do let state ← source state left; source state right) := by
  rw [composed,composed,bind_tc_ok,composed,value_append]
#print axioms value_append
#print axioms source_append
end R1Z.PV_CBL_SoftBlocksAppend
