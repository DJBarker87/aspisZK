import NDO_JFy_SelectorSlices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Selectors
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open pool_v1.pair_forest_copy_terminal
open JFy_SelectorSlices

theorem source (point : Array field.QM31 10#usize) (hc : FIw_ArrayValue.canonical point) :
    ∃ s,Selectors.boxed_at_point point=ok s ∧ FIw_ArrayValue.canonical s.high ∧ FIw_ArrayValue.canonical s.low := by
  have cells : ∀ i : Fin (10#usize).val,Canon (point.val[i.val]'(by simpa only [point.property] using i.isLt)) := by
    intro i
    exact hc _ (List.getElem_mem _)
  obtain ⟨high,hh,hhc⟩ := JFy_SelectorExpand.source 64#usize (prefixSlice point)
    (by simp only [prefixSlice,Slice.length,List.slice_length,point.property];decide)
    (prefix_coordinates_canonical point cells)
  obtain ⟨low,hl,hlc⟩ := JFy_SelectorExpand.source 16#usize (suffixSlice point)
    (by simp only [suffixSlice,Slice.length,List.length_drop,point.property];decide)
    (suffix_coordinates_canonical point cells)
  refine ⟨⟨high,low⟩,?_,hhc,hlc⟩
  unfold Selectors.boxed_at_point Selectors.at_point
  rw [prefix_read,bind_tc_ok,hh,bind_tc_ok,suffix_read,bind_tc_ok,hl,bind_tc_ok]
#print axioms source
end AspisR1.JFy_Selectors
end
