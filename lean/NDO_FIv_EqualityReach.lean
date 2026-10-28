import NDO_FIv_EqualityLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_EqualityReach
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)

theorem reached (left right : Array NQ 10#usize) (out : NQ)
    (run : FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value left right=ok out) :
    ∃ a b product, Array.index_usize left 0#usize=ok a ∧
      Array.index_usize right 0#usize=ok b ∧
      FIv_EqualityCell.call () (a,b)=ok product ∧
      FIv_EqualityLoop.loop left right product 1#usize=ok out := by
  unfold FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value at run
  obtain ⟨a,ha,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨product,hp,run⟩ := FIv_Map.bind_success _ _ _ run
  exact ⟨a,b,product,ha,hb,hp,run⟩

#print axioms reached
end AspisR1.FIv_EqualityReach
end
