import RPu_FIw_SelectedValue
set_option autoImplicit false
namespace AspisR1.FJn_H1Index
open Aeneas Aeneas.Std Result FIq_Native
/-- The installed H1 column is 16+10; only tiny word arithmetic is reduced. -/
theorem value : pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN=ok 26#usize := by
  unfold pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  exact FIw_ScalarIndices.add26
#print axioms value
end AspisR1.FJn_H1Index
