import NDO_JGp_Recombine
set_option autoImplicit false
namespace AspisR1.JGp_RecombinedReads
open Aeneas Aeneas.Std Result

theorem semantic (semantic y1 : Slice U8) (hs : semantic.length=13831) (hy : y1.length=928) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (JGp_Recombine.vector semantic y1) {«end»:=13831#usize}=ok semantic := by
  change core.slice.index.SliceIndexRangeToUsizeSlice.index
    {«end»:=13831#usize} (JGp_Recombine.vector semantic y1).deref=ok semantic
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.index
  have bound : (13831#usize).val≤(JGp_Recombine.vector semantic y1).val.length := by
    rw [JGp_Recombine.length semantic y1 hs hy]
    decide
  erw [if_pos bound]
  apply congrArg Result.ok
  apply Subtype.ext
  change ((JGp_Recombine.vector semantic y1).val.drop 0).take 13831=semantic.val
  rw [List.drop_zero,JGp_Recombine.take semantic y1 hs hy]
#print axioms semantic

theorem y1 (semantic y1 : Slice U8) (hs : semantic.length=13831) (hy : y1.length=928) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      (JGp_Recombine.vector semantic y1) {start:=13831#usize}=ok y1 := by
  change core.slice.index.SliceIndexRangeFromUsizeSlice.index
    {start:=13831#usize} (JGp_Recombine.vector semantic y1).deref=ok y1
  unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index
  have bound : (13831#usize).val≤(JGp_Recombine.vector semantic y1).val.length := by
    rw [JGp_Recombine.length semantic y1 hs hy]
    decide
  erw [if_pos bound]
  apply congrArg Result.ok
  apply Subtype.ext
  exact JGp_Recombine.drop semantic y1 hs hy
#print axioms y1
end AspisR1.JGp_RecombinedReads
