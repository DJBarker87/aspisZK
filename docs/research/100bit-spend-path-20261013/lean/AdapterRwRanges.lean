import AdapterRwModel
set_option autoImplicit false
namespace AspisR1.AdapterRw.Ranges
open Aeneas Aeneas.Std Result

/-- The actual checked range operation determines the bytes, not merely a pointer. -/
theorem selected_exact (account selected : Slice U8) (start finish : Usize)
    (ordered : start.val ≤ finish.val) (within : finish.val ≤ account.val.length)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      account {start := start, «end» := finish} = ok selected) :
    selected.val = (account.val.drop start.val).take (finish.val-start.val) ∧
    selected.val.length = finish.val-start.val := by
  obtain ⟨out,run,contents,length⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ⟨start,finish⟩ account ordered within)
  have same : out = selected := Result.ok.inj (run.symm.trans range)
  subst out
  refine ⟨?_,length⟩
  change selected.val = account.val.extract start.val finish.val at contents
  simpa only [List.extract_eq_drop_take] using contents

/-- A selected suffix ending at the account length exhausts the account. -/
theorem suffix_exact (account selected : Slice U8) (start finish : Usize)
    (ordered : start.val ≤ finish.val) (length : account.val.length = finish.val)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      account {start := start, «end» := finish} = ok selected) :
    selected.val.length = finish.val-start.val ∧
    account.val = account.val.take start.val ++ selected.val := by
  have facts := selected_exact account selected start finish ordered (by omega) range
  have full : selected.val = account.val.drop start.val := by
    rw [facts.1,←length,←List.length_drop,List.take_length]
  exact ⟨facts.2, by rw [full]; exact (List.take_append_drop start.val account.val).symm⟩

#print axioms selected_exact
#print axioms suffix_exact
end AspisR1.AdapterRw.Ranges
