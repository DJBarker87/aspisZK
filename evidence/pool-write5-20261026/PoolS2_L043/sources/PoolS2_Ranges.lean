import PoolS2_Index
set_option autoImplicit false
namespace AspisR1.PoolS2_Ranges
open Aeneas Aeneas.Std Result

theorem selected_exact {T : Type} (items selected : Slice T) (start finish : Usize)
    (ordered : start.val ≤ finish.val) (within : finish.val ≤ items.val.length)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice T)
      items {start := start, «end» := finish} = ok selected) :
    selected.val = (items.val.drop start.val).take (finish.val-start.val) ∧
      selected.val.length = finish.val-start.val := by
  obtain ⟨out,run,contents,length⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ⟨start,finish⟩ items ordered within)
  have same : out = selected := Result.ok.inj (run.symm.trans range)
  subst out
  refine ⟨?_,length⟩
  change selected.val = items.val.extract start.val finish.val at contents
  simpa only [List.extract_eq_drop_take] using contents

theorem selected_exists {T : Type} (items : Slice T) (start finish : Usize)
    (ordered : start.val ≤ finish.val) (within : finish.val ≤ items.val.length) :
    ∃ selected, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice T)
      items {start := start, «end» := finish} = ok selected := by
  obtain ⟨out,run,_,_⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ⟨start,finish⟩ items ordered within)
  exact ⟨out,run⟩

theorem indexed {T : Type} (items : Slice T) (i : Usize) (value : T)
    (run : Slice.index_usize items i = ok value) :
    ∃ within : i.val < items.val.length, (items.val[i.val]'within) = value := by
  by_cases within : i.val < items.val.length
  · exact ⟨within,Result.ok.inj ((PoolS2_Index.read items i within).symm.trans run)⟩
  · simp [Slice.index_usize,Slice.getElem?_Usize_eq,within] at run

#print axioms selected_exact
#print axioms selected_exists
#print axioms indexed
end AspisR1.PoolS2_Ranges
