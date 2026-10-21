import MultiproofConeCanonical

set_option autoImplicit false
namespace AspisR1.MultiproofConeSlices
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical

/-- Immutable owned view used by the extracted parser's checked ranges. -/
def sub (bytes : Slice U8) (start finish : Usize) : Slice U8 :=
  ⟨(bytes.val.drop start.val).take (finish.val-start.val), by
    have hb := bytes.property
    simp only [List.length_take,List.length_drop]
    omega⟩

theorem range_total (bytes : Slice U8) (start finish : Usize)
    (order : start.val ≤ finish.val) (bound : finish.val ≤ bytes.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes { start := start, «end» := finish } = ok (sub bytes start finish) := by
  have valid : start ≤ finish ∧ finish.val ≤ bytes.length := ⟨order,bound⟩
  simp only [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,valid,if_true]
  rfl

theorem prefix_total (bytes : Slice U8) (finish : Usize)
    (bound : finish.val ≤ bytes.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      bytes { «end» := finish } = ok (sub bytes 0#usize finish) := by
  simp only [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,bound,if_true]
  rfl

theorem drop_total (bytes : Slice U8) (start : Usize)
    (bound : start.val ≤ bytes.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      bytes { start := start } = ok (Slice.drop bytes start) := by
  simp only [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,bound,if_true]

theorem bytes_sub (bytes : Slice U8) (start finish : Usize) :
    bytesOf (sub bytes start finish).val =
      OraclePortCompactDraft.slice (bytesOf bytes.val) start.val (finish.val-start.val) := by
  simp only [sub,bytesOf,OraclePortCompactDraft.slice,List.map_take,List.map_drop]

theorem sub_length (bytes : Slice U8) (start finish : Usize)
    (order : start.val ≤ finish.val) (bound : finish.val ≤ bytes.val.length) :
    (sub bytes start finish).val.length = finish.val-start.val := by
  simp only [sub,List.length_take,List.length_drop]
  omega

#print axioms range_total
#print axioms prefix_total
#print axioms drop_total
#print axioms bytes_sub
#print axioms sub_length
end AspisR1.MultiproofConeSlices
