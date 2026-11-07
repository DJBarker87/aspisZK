import NMS_RSLPoolCarriers
import AdapterRwRanges
set_option autoImplicit false
namespace NMS_RSLRanges
open Aeneas Aeneas.Std NMS_RSLScalars
/-- Exact SAME checked range in canonical bytes, not a length-only bridge. -/
theorem selected (source selected : Slice U8) (start finish : Usize)
 (ordered : start.val ≤ finish.val) (within : finish.val ≤ source.val.length)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  source ⟨start,finish⟩ = .ok selected) :
 bytes selected = RSL.slice (bytes source) start.val finish.val := by
 have contents := (AspisR1.AdapterRw.Ranges.selected_exact source selected start finish
   ordered within range).1
 simp only [bytes,RSL.slice,contents,List.map_take,List.map_drop]

theorem public_extent (publicBytes : Aeneas.Std.Array U8 1880#usize) :
 (bytes publicBytes.to_slice).length = RSL.STATEMENT_BYTES := by
 simpa [bytes,RSL.STATEMENT_BYTES] using publicBytes.property

#print axioms selected
#print axioms public_extent
end NMS_RSLRanges
