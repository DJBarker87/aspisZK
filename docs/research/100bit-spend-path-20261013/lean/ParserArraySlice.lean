import AspisV8R19.SamplerWordRead

/-! Generalized successful checked slice for a fixed-length Aeneas array.
This is list/slice plumbing only; it does not prove parser or caller behavior. -/
set_option autoImplicit false

namespace AspisR1.ParserArraySlice

open Aeneas Aeneas.Std Result

/-- The list segment selected by a checked half-open array range. -/
def segment {n : Usize} (arr : Array U8 n) (start width : Usize)
    (bound : start.val + width.val ≤ n.val) : Array U8 width :=
  ⟨(arr.val.drop start.val).take width.val, by
    have harr : arr.val.length = n.val := arr.property
    simp only [List.length_take, List.length_drop, harr]
    change min width.val (n.val - start.val) = width.val
    omega⟩

theorem segment_length {n : Usize} (arr : Array U8 n) (start width : Usize)
    (bound : start.val + width.val ≤ n.val) :
    (segment arr start width bound).val.length = width.val :=
  (segment arr start width bound).property

theorem slice_segment {n : Usize} (arr : Array U8 n) (start width : Usize)
    (bound : start.val + width.val ≤ n.val) (finish : Usize)
    (hfinish : finish.val = start.val + width.val) :
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) (Array.to_slice arr)
      { start := start, «end» := finish } =
      Result.ok (Array.to_slice (segment arr start width bound)) := by
  have harr : arr.val.length = n.val := arr.property
  simp [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    Array.to_slice, Slice.length, segment, List.slice, harr, hfinish]
  omega

#print axioms segment_length
#print axioms slice_segment

end AspisR1.ParserArraySlice
