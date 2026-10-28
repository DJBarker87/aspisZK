import RPv_FIy_EmptyRoot
import RPv_JFy_Steps
set_option autoImplicit false
namespace AspisR1.JGa_EmptyRoot
open Aeneas Aeneas.Std Result WP FIq_Native

@[step] theorem source (level : Usize) (hl : level.val<21) :
    pool_v1.pair_forest_semantic_terminal.empty_root level ⦃ out => ∀ x∈out.val,x.val<FIw_ScalarArithmetic.P ⦄ := by
  have spec : Array.index_usize pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1 level ⦃ _ => True ⦄ := by
    step* <;> scalar_tac
  obtain ⟨row,hr,_⟩ := WP.spec_imp_exists spec
  have call : pool_v1.pair_forest_semantic_terminal.empty_root level=ok row := by
    unfold pool_v1.pair_forest_semantic_terminal.empty_root
    rw [hr,bind_tc_ok,FIy_EmptyRootMap.value]
  rw [call]
  exact (FIy_EmptyRoot.value level row call).2
#print axioms source
end AspisR1.JGa_EmptyRoot
