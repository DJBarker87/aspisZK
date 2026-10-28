import NDO_JFy_SumHighOuter
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SumHigh
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open pool_v1.pair_forest_semantic_terminal

theorem source (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (ranges : Slice (core.ops.range.Range Usize))
    (hb : ∀ r∈ranges.val,r.start.val≤r.end.val ∧ r.end.val≤64)
    (hs : FIw_ArrayValue.canonical s.high) :
    ∃ out,sum_high s ranges=ok out ∧ Canon out := by
  obtain ⟨out,call,hout⟩ := JFy_SumHighOuter.source ranges.val ⟨ranges,0⟩ s field.QM31.ZERO rfl hb hs FIv_NativeValue.zero.1
  exact ⟨out,call,hout⟩
#print axioms source
end AspisR1.JFy_SumHigh
end
