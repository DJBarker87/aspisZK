import AdapterRwRanges
set_option autoImplicit false
namespace AspisR1.NCK_ProofSuffix
open Aeneas Aeneas.Std Result
/-- Exact suffix identity and length at the successful top-body range cut.
The checkpoint is a distinct unchanged argument; no hash binding is used. -/
theorem exact_suffix (raw selected : Slice U8)
    (length : raw.val.length = 58295)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      raw {start := 688#usize, «end» := 58295#usize} = ok selected) :
    selected.val = raw.val.drop 688 ∧ selected.val.length = 57607 ∧
    raw.val = raw.val.take 688 ++ selected.val := by
  have h := AdapterRw.Ranges.selected_exact raw selected 688#usize 58295#usize
    (by scalar_tac) (by simpa using length.ge) range
  have count : selected.val.length = 57607 := by simpa using h.2
  have suffix : selected.val = raw.val.drop 688 := by
    rw [h.1]
    change (raw.val.drop 688).take 57607 = raw.val.drop 688
    have remaining : (raw.val.drop 688).length = 57607 := by simp [length]
    simpa only [remaining] using (List.take_length (l := raw.val.drop 688))
  exact ⟨suffix,count,by rw [suffix]; exact (List.take_append_drop 688 raw.val).symm⟩
#print axioms exact_suffix
end AspisR1.NCK_ProofSuffix
