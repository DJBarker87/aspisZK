import NNG_Split087
import LIBC_Slices
set_option autoImplicit false
namespace AspisR1.NNG_Reassemble087
open Aeneas Aeneas.Std Result

theorem prefix_window (logical : alloc.vec.Vec U8) (semantic y1 : Slice U8)
 (same : logical.val=semantic.val++y1.val) (size : semantic.val.length=13831) :
 alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) logical {«end»:=13831#usize}=.ok semantic := by
 change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   (alloc.vec.Vec.deref logical) {«end»:=13831#usize}=.ok semantic
 rw [MultiproofConeSlices.prefix_total _ _ (by change 13831≤logical.val.length;rw [same,List.length_append,size];omega)]
 apply congrArg Result.ok
 apply Subtype.ext
 change ((logical.val.drop 0).take 13831)=semantic.val
 rw [List.drop_zero,same,←size,List.take_left]

theorem suffix (logical : alloc.vec.Vec U8) (semantic y1 : Slice U8)
 (same : logical.val=semantic.val++y1.val) (size : semantic.val.length=13831) :
 alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) logical {start:=13831#usize}=.ok y1 := by
 change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
   (alloc.vec.Vec.deref logical) {start:=13831#usize}=.ok y1
 rw [MultiproofConeSlices.drop_total _ _ (by change 13831≤logical.val.length;rw [same,List.length_append,size];omega)]
 apply congrArg Result.ok
 apply Subtype.ext
 change logical.val.drop 13831=y1.val
 rw [same,←size,List.drop_left]
#print axioms prefix_window
#print axioms suffix
end AspisR1.NNG_Reassemble087
