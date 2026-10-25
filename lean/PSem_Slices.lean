import PSem_SourceCuts
set_option autoImplicit false
namespace AspisR1.PSem_Slices
open Aeneas Aeneas.Std Result

theorem range_bytes {T : Type} (input output : Slice T) (start stop : Usize)
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice T)
      input {start:=start,«end»:=stop}=ok output) :
    output.val=(input.val.drop start.val).take (stop.val-start.val) := by
  simp only [Slice.index_SliceIndexRangeUsizeSliceInst] at h
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at h
  split at h
  · have same := Result.ok.inj h
    have bytes := congrArg (fun s : Slice T => s.val) same
    simpa only [List.slice] using bytes.symm
  · cases h

theorem range_bounds {T : Type} (input output : Slice T) (start stop : Usize)
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice T)
      input {start:=start,«end»:=stop}=ok output) :
    start.val ≤ stop.val ∧ stop.val ≤ input.val.length := by
  simp only [Slice.index_SliceIndexRangeUsizeSliceInst] at h
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at h
  split at h
  · assumption
  · cases h

theorem range_length {T : Type} (input output : Slice T) (start stop : Usize)
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice T)
      input {start:=start,«end»:=stop}=ok output) :
    output.val.length=stop.val-start.val := by
  have bounds := range_bounds input output start stop h
  rw [range_bytes input output start stop h,List.length_take,List.length_drop]
  omega

#print axioms range_bytes
#print axioms range_bounds
#print axioms range_length
end AspisR1.PSem_Slices
