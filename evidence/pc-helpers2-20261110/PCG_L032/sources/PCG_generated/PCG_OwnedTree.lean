import PCG_HelperRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_OwnedTree
/-- Full owned record: next index, every root limb and every frontier limb.
The native arbitrary-index window covers every array place; empty is unread. -/
theorem row_181 (inner : PCG_HelperRef.Tree) :
 PCG_HelperRef.owned_tree inner = ok inner := rfl
#print axioms row_181
end PCG_OwnedTree
