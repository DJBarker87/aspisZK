import RPu_FIw_WordValue
import RPu_FIw_ScalarIndices
import RPu_FIv_NativeArray
import RPu_FIq_Native14
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_SelectedValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)

theorem width : pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1=
    ok 28#usize := by
  unfold pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  simp only [FIw_ScalarIndices.add26,FIw_ScalarIndices.add28,bind_tc_ok]

theorem value (claims : Array NQ 84#usize) (point column : Usize) (out : NQ)
    (run : pool_v1.pair_forest_semantic_terminal.selected_claim claims point column=ok out) :
    decode out=FIv_NativeArray.value claims (point.val*28+column.val) := by
  unfold pool_v1.pair_forest_semantic_terminal.selected_claim at run
  rw [width,bind_tc_ok] at run
  obtain ⟨base,hb,r1⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨index,hi,r2⟩ := FIv_Map.bind_success _ _ _ r1
  have baseValue : base.val=point.val*28 := FIw_WordValue.mul point 28#usize base hb
  have indexValue : index.val=point.val*28+column.val := by
    rw [FIw_WordValue.add base column index hi,baseValue]
  rw [← FIv_NativeArray.read claims index out r2,indexValue]
#print axioms width
#print axioms value
end AspisR1.FIw_SelectedValue
end
