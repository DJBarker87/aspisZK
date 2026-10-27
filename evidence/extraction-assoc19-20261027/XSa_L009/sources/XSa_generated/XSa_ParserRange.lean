import XSa_ParserTotal
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_ParserRange

theorem range (s : Slice U8) (lo hi : Usize) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  s ⟨lo,hi⟩ = XRn_Join_sliceRange s lo.val hi.val := by
 unfold core.slice.index.Slice.index core.slice.index.SliceIndexRangeUsizeSlice
 rfl

#print axioms range
end XSa_ParserRange
