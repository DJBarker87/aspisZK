import RPv_FIy_EmptyRootBounds
set_option autoImplicit false
namespace AspisR1.FIy_EmptyRoot
open Aeneas Aeneas.Std Result FIq_Native

theorem value (level : Usize) (out : Array U32 8#usize)
    (success : pool_v1.pair_forest_semantic_terminal.empty_root level=ok out) :
    pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1.val[level.val]?=some out ∧
    ∀ x∈out.val,x.val<FIw_ScalarArithmetic.P := by
  unfold pool_v1.pair_forest_semantic_terminal.empty_root at success
  obtain ⟨row,hrow,success⟩ := AspisR1.FIv_Map.bind_success _ _ _ success
  rw [FIy_EmptyRootMap.value] at success
  have same := Result.ok.inj success
  subst row
  have slot := FIy_ArraySlot.value _ level out hrow
  exact ⟨slot,FIy_EmptyRootBounds.value out (List.mem_of_getElem? slot)⟩
#print axioms value
end AspisR1.FIy_EmptyRoot
