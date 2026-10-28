import NDO_JGa_EqualityLoop
import NDO_FIv_EqualityValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_Equality
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem source (left right : Array field.QM31 10#usize) (hl : canonical left) (hr : canonical right) :
    ∃ out,equality_value left right=ok out ∧ Canon out ∧ decode out=FIv_EqualityValue.weight left right := by
  obtain ⟨a,ha,hac⟩ := JFy_ArrayTotal.read left 0#usize (by decide) hl
  obtain ⟨b,hb,hbc⟩ := JFy_ArrayTotal.read right 0#usize (by decide) hr
  obtain ⟨cell,hcell,hcc⟩ := WP.spec_imp_exists (JGa_EqualityCell.source a b hac hbc)
  unfold FIv_EqualityCell.call at hcell
  obtain ⟨out,ho,hoc⟩ := JGa_EqualityLoop.source 9 1#usize left right cell rfl hl hr hcc
  have call : equality_value left right=ok out := by
    unfold equality_value
    rw [ha,bind_tc_ok,hb,bind_tc_ok,hcell,bind_tc_ok,ho]
  exact ⟨out,call,hoc,(FIv_EqualityValue.exact_value left right hl hr out call).2⟩
#print axioms source
end AspisR1.JGa_Equality
end
