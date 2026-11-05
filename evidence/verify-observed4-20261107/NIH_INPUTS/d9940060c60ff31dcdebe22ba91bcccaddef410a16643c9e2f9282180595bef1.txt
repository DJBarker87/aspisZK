import NIH_ExpandOuter
import NDO_JFy_Selectors
import RPv_FJa_BoxedSelAt
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_AtPoint
open FIq_Native.pool_v1.pair_forest_copy_terminal
open FIv_NativeArithmetic (NQ)
/-- Both original slice domains are derived from this SAME point, not independent arrays. -/
theorem slices (point : Array NQ 10#usize) (canonical : FIw_ArrayValue.canonical point) :
 (JFy_SelectorSlices.prefixSlice point).val.length=6 ∧
 (JFy_SelectorSlices.suffixSlice point).val.length=4 ∧
 (∀ x∈(JFy_SelectorSlices.prefixSlice point).val, FIv_NativeValue.Canon x) ∧
 (∀ x∈(JFy_SelectorSlices.suffixSlice point).val, FIv_NativeValue.Canon x) := by
 have cells : ∀ i : Fin (10#usize).val, FIv_NativeValue.Canon
   (point.val[i.val]'(by simpa only [point.property] using i.isLt)) := by
  intro i
  exact canonical _ (List.getElem_mem _)
 refine ⟨?_,?_,JFy_SelectorSlices.prefix_coordinates_canonical point cells,
   JFy_SelectorSlices.suffix_coordinates_canonical point cells⟩
 · simp only [JFy_SelectorSlices.prefixSlice,List.slice_length,point.property];decide
 · simp only [JFy_SelectorSlices.suffixSlice,List.length_drop,point.property];decide
/-- Full emitted Box-erased carrier and exact adopted selector, with no output premise. -/
theorem boxed (point : Array NQ 10#usize) (canonical : FIw_ArrayValue.canonical point) :
 ∃ s, Selectors.boxed_at_point point=ok s ∧ FIw_ArrayValue.canonical s.high ∧
 FIw_ArrayValue.canonical s.low ∧
 FIw_PublicModel.selector s=R0P.SemSource.selAt (FIw_ArrayValue.decoded point) := by
 obtain ⟨s,run,high,low⟩:=JFy_Selectors.source point canonical
 exact ⟨s,run,high,low,FJa_BoxedSelAt.value point s canonical run⟩
/-- Aeneas's retained Box-erased equation is not a native allocation claim. -/
theorem source (point : Array NQ 10#usize) :
 Selectors.at_point point=Selectors.boxed_at_point point := rfl
#print axioms slices
#print axioms boxed
#print axioms source
end AspisR1.NIH_AtPoint
end
