import NDO_JFu_SelectedClaim
import NDO_JFy_SelectedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SelectedRead
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_semantic_terminal

theorem source (selected : Array field.QM31 84#usize) (hc : FIw_ArrayValue.canonical selected)
    (point column : Usize) (hp : point.val<3) (hj : column.val<28) :
    ∃ q,selected_claim selected point column=ok q ∧ FIv_NativeValue.Canon q := by
  obtain ⟨q,call⟩ := JFu_SelectedClaim.source selected point column hp hj
  refine ⟨q,call,?_⟩
  unfold selected_claim at call
  rw [JFu_SelectedClaim.stride,bind_tc_ok] at call
  obtain ⟨p,hp1,rest⟩ := FIv_Map.bind_success _ _ _ call
  obtain ⟨i,hi,rest⟩ := FIv_Map.bind_success _ _ _ rest
  exact FIv_NativeArray.canonical selected i q hc rest
#print axioms source
end AspisR1.JFy_SelectedRead
end
