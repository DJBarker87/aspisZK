import NKO_ViewRanges
set_option autoImplicit false
noncomputable section
namespace NLP_FoldedRange
open Aeneas Aeneas.Std Result AspisR1
/-- Only small layout arithmetic is normalized. -/
theorem diff : (7783#usize).val-(7751#usize).val=32 := by change 7783-7751=32; omega
theorem start : (7751#usize).val=7751 := by scalar_tac
theorem selected (proof selected : Slice U8)
 (call : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=7751#usize,«end»:=7783#usize}=ok selected) :
 selected.val=(proof.val.drop 7751).take 32 := by
 have value:=PSem_Slices.range_bytes proof selected 7751#usize 7783#usize call
 rw [diff,start] at value
 exact value
theorem copied (selected : Slice U8) (root : Array U8 32#usize)
 (call : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 selected=ok (.Ok root)) :
 root.val=selected.val := by
 unfold core.array.TryFromArrayCopySlice.try_from at call
 split at call
 · cases call; rfl
 · cases call
#print copied
#print axioms diff
#print axioms start
#print axioms selected
#print axioms copied
end NLP_FoldedRange
