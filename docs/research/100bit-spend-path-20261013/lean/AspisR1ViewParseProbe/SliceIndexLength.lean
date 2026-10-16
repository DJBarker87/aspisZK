import AspisR1ViewParseProbe.CleanParameterizedParse

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ViewParseProbe.SliceIndexLength

theorem range_index_success_length {α : Type} (s out : Slice α)
    (start finish : Usize)
    (h : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice α) s
      { start := start, «end» := finish } = Result.ok out) :
    (Slice.len out).val = finish.val - start.val := by
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    { start := start, «end» := finish } s = Result.ok out at h
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index] at h
  split at h
  · rename_i hbound
    injection h with hout
    subst out
    have hb1 : start.val ≤ finish.val := by
      simpa only [UScalar.le_equiv] using hbound.1
    have hb2 : finish.val ≤ s.val.length := by
      simpa only [UScalar.le_equiv, Slice.length] using hbound.2
    simp [Slice.len, Slice.length, List.slice, hb1, hb2]
    omega
  · cases h

#print axioms range_index_success_length

end AspisR1ViewParseProbe.SliceIndexLength
