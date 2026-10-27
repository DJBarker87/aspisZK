import RPu_FIy_EmptyRootMap
import RPu_FIw_ScalarArithmetic
set_option autoImplicit false
namespace AspisR1.FIy_EmptyRootBounds
open Aeneas Aeneas.Std Result FIq_Native

theorem value : ∀ row∈pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1.val,
    ∀ x∈row.val,x.val<FIw_ScalarArithmetic.P := by
  intro row hr
  simp only [pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1,
    Array.make,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro x hx
    change x.val<2147483647
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals scalar_tac
#print axioms value
end AspisR1.FIy_EmptyRootBounds
