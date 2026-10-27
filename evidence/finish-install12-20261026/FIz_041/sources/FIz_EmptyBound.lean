import FIz_EmptyRoots
set_option autoImplicit false
namespace AspisR1.FIz_EmptyBound
open Aeneas Aeneas.Std

theorem row (level : Fin 21) : FIy_FrontierMeaning.roots level.val ∈
    FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1.val := by
  unfold FIy_FrontierMeaning.roots
  have bound : level.val<FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1.val.length := by
    rw [Aeneas.Std.Array.length_val]
    exact level.isLt
  rw [List.getElem?_eq_getElem bound]
  exact List.getElem_mem _

theorem value (level : Fin 21) (j : Fin 8) : R0P.emptyRootsNat level j<2147483647 := by
  have slot : ((FIy_FrontierMeaning.roots level.val).val[j.val]?).getD (0#u32) ∈
      (FIy_FrontierMeaning.roots level.val).val := by
    rw [List.getElem?_eq_getElem (by simpa only [(FIy_FrontierMeaning.roots level.val).property] using j.isLt)]
    exact List.getElem_mem _
  have hb := FIy_EmptyRootBounds.value _ (row level) _ slot
  rw [FIz_EmptyRoots.table level j] at hb
  exact hb
#print axioms row
#print axioms value
end AspisR1.FIz_EmptyBound
